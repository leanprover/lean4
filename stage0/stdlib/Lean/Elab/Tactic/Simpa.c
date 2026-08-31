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
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
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
uint8_t v_suppressElabErrors_boxed_116_; uint8_t v___y_4762__boxed_117_; uint8_t v_res_118_; lean_object* v_r_119_; 
v_suppressElabErrors_boxed_116_ = lean_unbox(v_suppressElabErrors_113_);
v___y_4762__boxed_117_ = lean_unbox(v___y_114_);
v_res_118_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0(v_suppressElabErrors_boxed_116_, v___y_4762__boxed_117_, v_x_115_);
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
v_options_131_ = lean_ctor_get(v___y_123_, 1);
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
lean_object* v___y_153_; uint8_t v___y_154_; lean_object* v___y_155_; lean_object* v___y_156_; lean_object* v___y_157_; lean_object* v___y_158_; uint8_t v___y_159_; lean_object* v___y_160_; lean_object* v___y_161_; lean_object* v___y_189_; uint8_t v___y_190_; uint8_t v___y_191_; lean_object* v___y_192_; lean_object* v___y_193_; uint8_t v___y_194_; lean_object* v___y_195_; lean_object* v___y_215_; lean_object* v___y_216_; uint8_t v___y_217_; uint8_t v___y_218_; lean_object* v___y_219_; uint8_t v___y_220_; lean_object* v___y_221_; lean_object* v___y_225_; uint8_t v___y_226_; lean_object* v___y_227_; lean_object* v___y_228_; uint8_t v___y_229_; uint8_t v___y_230_; uint8_t v___x_235_; lean_object* v___y_237_; uint8_t v___y_238_; lean_object* v___y_239_; lean_object* v___y_240_; uint8_t v___y_241_; uint8_t v___y_242_; uint8_t v___y_244_; uint8_t v___x_258_; 
v___x_235_ = 2;
v___x_258_ = l_Lean_instBEqMessageSeverity_beq(v_severity_145_, v___x_235_);
if (v___x_258_ == 0)
{
v___y_244_ = v___x_258_;
goto v___jp_243_;
}
else
{
uint8_t v___x_259_; 
lean_inc_ref(v_msgData_144_);
v___x_259_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_144_);
v___y_244_ = v___x_259_;
goto v___jp_243_;
}
v___jp_152_:
{
lean_object* v___x_162_; lean_object* v_currNamespace_163_; lean_object* v_openDecls_164_; lean_object* v_env_165_; lean_object* v_nextMacroScope_166_; lean_object* v_ngen_167_; lean_object* v_auxDeclNGen_168_; lean_object* v_traceState_169_; lean_object* v_cache_170_; lean_object* v_messages_171_; lean_object* v_infoState_172_; lean_object* v_snapshotTasks_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_187_; 
v___x_162_ = lean_st_ref_take(v___y_161_);
v_currNamespace_163_ = lean_ctor_get(v___y_160_, 5);
v_openDecls_164_ = lean_ctor_get(v___y_160_, 6);
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
lean_ctor_set(v___x_178_, 1, v___y_157_);
lean_inc_ref(v___y_153_);
lean_inc_ref(v___y_155_);
v___x_179_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_179_, 0, v___y_155_);
lean_ctor_set(v___x_179_, 1, v___y_156_);
lean_ctor_set(v___x_179_, 2, v___y_158_);
lean_ctor_set(v___x_179_, 3, v___y_153_);
lean_ctor_set(v___x_179_, 4, v___x_178_);
lean_ctor_set_uint8(v___x_179_, sizeof(void*)*5, v___y_159_);
lean_ctor_set_uint8(v___x_179_, sizeof(void*)*5 + 1, v___y_154_);
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
lean_object* v_fileName_196_; lean_object* v_fileMap_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_213_; 
v_fileName_196_ = lean_ctor_get(v___y_193_, 0);
v_fileMap_197_ = lean_ctor_get(v___y_193_, 1);
v___x_198_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_144_);
v___x_199_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__2(v___x_198_, v___y_147_, v___y_148_, v___y_149_, v___y_150_);
v_a_200_ = lean_ctor_get(v___x_199_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_213_ == 0)
{
v___x_202_ = v___x_199_;
v_isShared_203_ = v_isSharedCheck_213_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v___x_199_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_213_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
lean_inc_ref_n(v_fileMap_197_, 2);
v___x_204_ = l_Lean_FileMap_toPosition(v_fileMap_197_, v___y_192_);
lean_dec(v___y_192_);
v___x_205_ = l_Lean_FileMap_toPosition(v_fileMap_197_, v___y_195_);
lean_dec(v___y_195_);
v___x_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
v___x_207_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___closed__0));
if (v___y_191_ == 0)
{
lean_del_object(v___x_202_);
lean_dec_ref(v___y_189_);
v___y_153_ = v___x_207_;
v___y_154_ = v___y_190_;
v___y_155_ = v_fileName_196_;
v___y_156_ = v___x_204_;
v___y_157_ = v_a_200_;
v___y_158_ = v___x_206_;
v___y_159_ = v___y_194_;
v___y_160_ = v___y_149_;
v___y_161_ = v___y_150_;
goto v___jp_152_;
}
else
{
uint8_t v___x_208_; 
lean_inc(v_a_200_);
v___x_208_ = l_Lean_MessageData_hasTag(v___y_189_, v_a_200_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; lean_object* v___x_211_; 
lean_dec_ref_known(v___x_206_, 1);
lean_dec_ref(v___x_204_);
lean_dec(v_a_200_);
v___x_209_ = lean_box(0);
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 0, v___x_209_);
v___x_211_ = v___x_202_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_209_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
else
{
lean_del_object(v___x_202_);
v___y_153_ = v___x_207_;
v___y_154_ = v___y_190_;
v___y_155_ = v_fileName_196_;
v___y_156_ = v___x_204_;
v___y_157_ = v_a_200_;
v___y_158_ = v___x_206_;
v___y_159_ = v___y_194_;
v___y_160_ = v___y_149_;
v___y_161_ = v___y_150_;
goto v___jp_152_;
}
}
}
}
v___jp_214_:
{
lean_object* v___x_222_; 
v___x_222_ = l_Lean_Syntax_getTailPos_x3f(v___y_216_, v___y_220_);
lean_dec(v___y_216_);
if (lean_obj_tag(v___x_222_) == 0)
{
lean_inc(v___y_221_);
v___y_189_ = v___y_215_;
v___y_190_ = v___y_217_;
v___y_191_ = v___y_218_;
v___y_192_ = v___y_221_;
v___y_193_ = v___y_219_;
v___y_194_ = v___y_220_;
v___y_195_ = v___y_221_;
goto v___jp_188_;
}
else
{
lean_object* v_val_223_; 
v_val_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_val_223_);
lean_dec_ref_known(v___x_222_, 1);
v___y_189_ = v___y_215_;
v___y_190_ = v___y_217_;
v___y_191_ = v___y_218_;
v___y_192_ = v___y_221_;
v___y_193_ = v___y_219_;
v___y_194_ = v___y_220_;
v___y_195_ = v_val_223_;
goto v___jp_188_;
}
}
v___jp_224_:
{
lean_object* v_ref_231_; lean_object* v___x_232_; 
v_ref_231_ = l_Lean_replaceRef(v_ref_143_, v___y_227_);
v___x_232_ = l_Lean_Syntax_getPos_x3f(v_ref_231_, v___y_229_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v___x_233_; 
v___x_233_ = lean_unsigned_to_nat(0u);
v___y_215_ = v___y_225_;
v___y_216_ = v_ref_231_;
v___y_217_ = v___y_230_;
v___y_218_ = v___y_226_;
v___y_219_ = v___y_228_;
v___y_220_ = v___y_229_;
v___y_221_ = v___x_233_;
goto v___jp_214_;
}
else
{
lean_object* v_val_234_; 
v_val_234_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_val_234_);
lean_dec_ref_known(v___x_232_, 1);
v___y_215_ = v___y_225_;
v___y_216_ = v_ref_231_;
v___y_217_ = v___y_230_;
v___y_218_ = v___y_226_;
v___y_219_ = v___y_228_;
v___y_220_ = v___y_229_;
v___y_221_ = v_val_234_;
goto v___jp_214_;
}
}
v___jp_236_:
{
if (v___y_242_ == 0)
{
v___y_225_ = v___y_237_;
v___y_226_ = v___y_238_;
v___y_227_ = v___y_239_;
v___y_228_ = v___y_240_;
v___y_229_ = v___y_241_;
v___y_230_ = v_severity_145_;
goto v___jp_224_;
}
else
{
v___y_225_ = v___y_237_;
v___y_226_ = v___y_238_;
v___y_227_ = v___y_239_;
v___y_228_ = v___y_240_;
v___y_229_ = v___y_241_;
v___y_230_ = v___x_235_;
goto v___jp_224_;
}
}
v___jp_243_:
{
if (v___y_244_ == 0)
{
lean_object* v_toCold_245_; lean_object* v_options_246_; lean_object* v_ref_247_; uint8_t v_suppressElabErrors_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___f_251_; uint8_t v___x_252_; uint8_t v___x_253_; 
v_toCold_245_ = lean_ctor_get(v___y_149_, 0);
v_options_246_ = lean_ctor_get(v___y_149_, 1);
v_ref_247_ = lean_ctor_get(v___y_149_, 4);
v_suppressElabErrors_248_ = lean_ctor_get_uint8(v___y_149_, sizeof(void*)*10 + 1);
v___x_249_ = lean_box(v_suppressElabErrors_248_);
v___x_250_ = lean_box(v___y_244_);
v___f_251_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_251_, 0, v___x_249_);
lean_closure_set(v___f_251_, 1, v___x_250_);
v___x_252_ = 1;
v___x_253_ = l_Lean_instBEqMessageSeverity_beq(v_severity_145_, v___x_252_);
if (v___x_253_ == 0)
{
v___y_237_ = v___f_251_;
v___y_238_ = v_suppressElabErrors_248_;
v___y_239_ = v_ref_247_;
v___y_240_ = v_toCold_245_;
v___y_241_ = v___y_244_;
v___y_242_ = v___x_253_;
goto v___jp_236_;
}
else
{
lean_object* v___x_254_; uint8_t v___x_255_; 
v___x_254_ = l_Lean_warningAsError;
v___x_255_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__3(v_options_246_, v___x_254_);
v___y_237_ = v___f_251_;
v___y_238_ = v_suppressElabErrors_248_;
v___y_239_ = v_ref_247_;
v___y_240_ = v_toCold_245_;
v___y_241_ = v___y_244_;
v___y_242_ = v___x_255_;
goto v___jp_236_;
}
}
else
{
lean_object* v___x_256_; lean_object* v___x_257_; 
lean_dec_ref(v_msgData_144_);
v___x_256_ = lean_box(0);
v___x_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
return v___x_257_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_260_, lean_object* v_msgData_261_, lean_object* v_severity_262_, lean_object* v_isSilent_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
uint8_t v_severity_boxed_269_; uint8_t v_isSilent_boxed_270_; lean_object* v_res_271_; 
v_severity_boxed_269_ = lean_unbox(v_severity_262_);
v_isSilent_boxed_270_ = lean_unbox(v_isSilent_263_);
v_res_271_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg(v_ref_260_, v_msgData_261_, v_severity_boxed_269_, v_isSilent_boxed_270_, v___y_264_, v___y_265_, v___y_266_, v___y_267_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v_ref_260_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0(lean_object* v_ref_272_, lean_object* v_msgData_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
uint8_t v___x_283_; uint8_t v___x_284_; lean_object* v___x_285_; 
v___x_283_ = 1;
v___x_284_ = 0;
v___x_285_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg(v_ref_272_, v_msgData_273_, v___x_283_, v___x_284_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0___boxed(lean_object* v_ref_286_, lean_object* v_msgData_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0(v_ref_286_, v_msgData_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec(v_ref_286_);
return v_res_297_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__1(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__0));
v___x_300_ = l_Lean_stringToMessageData(v___x_299_);
return v___x_300_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__3(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__2));
v___x_303_ = l_Lean_stringToMessageData(v___x_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0(lean_object* v_linterOption_304_, lean_object* v_stx_305_, lean_object* v_msg_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v_name_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_334_; 
v_name_316_ = lean_ctor_get(v_linterOption_304_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v_linterOption_304_);
if (v_isSharedCheck_334_ == 0)
{
lean_object* v_unused_335_; 
v_unused_335_ = lean_ctor_get(v_linterOption_304_, 1);
lean_dec(v_unused_335_);
v___x_318_ = v_linterOption_304_;
v_isShared_319_ = v_isSharedCheck_334_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_name_316_);
lean_dec(v_linterOption_304_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_334_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_323_; 
v___x_320_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__1, &l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__1_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__1);
lean_inc(v_name_316_);
v___x_321_ = l_Lean_MessageData_ofName(v_name_316_);
if (v_isShared_319_ == 0)
{
lean_ctor_set_tag(v___x_318_, 7);
lean_ctor_set(v___x_318_, 1, v___x_321_);
lean_ctor_set(v___x_318_, 0, v___x_320_);
v___x_323_ = v___x_318_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_320_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v___x_321_);
v___x_323_ = v_reuseFailAlloc_333_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v_disable_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_324_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__3, &l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__3_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__3);
v___x_325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_323_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
v_disable_326_ = l_Lean_MessageData_note(v___x_325_);
v___x_327_ = l_Lean_Linter_linterMessageTag;
v___x_328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_328_, 0, v_msg_306_);
lean_ctor_set(v___x_328_, 1, v_disable_326_);
v___x_329_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_327_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
v___x_330_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_330_, 0, v_name_316_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
lean_inc(v_stx_305_);
v___x_331_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_331_, 0, v_stx_305_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
v___x_332_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0(v_stx_305_, v___x_331_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
lean_dec(v_stx_305_);
return v___x_332_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___boxed(lean_object* v_linterOption_336_, lean_object* v_stx_337_, lean_object* v_msg_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0(v_linterOption_336_, v_stx_337_, v_msg_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
return v_res_348_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__1(void){
_start:
{
lean_object* v___x_350_; lean_object* v_msg_351_; 
v___x_350_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__0));
v_msg_351_ = l_Lean_stringToMessageData(v___x_350_);
return v_msg_351_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__6(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__5));
v___x_359_ = l_Lean_MessageData_ofFormat(v___x_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa(lean_object* v_initialState_360_, lean_object* v_ref_361_, lean_object* v_replacement_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v_msg_373_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = lean_box(0);
lean_inc(v_replacement_362_);
v___x_385_ = l_Lean_Meta_Tactic_TryThis_isValidTactic(v_initialState_360_, v_replacement_362_, v___x_384_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_386_; lean_object* v_msg_387_; uint8_t v___x_388_; 
v_a_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_a_386_);
lean_dec_ref_known(v___x_385_, 1);
v_msg_387_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__1, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__1_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__1);
v___x_388_ = lean_unbox(v_a_386_);
lean_dec(v_a_386_);
if (v___x_388_ == 0)
{
lean_dec(v_replacement_362_);
v_msg_373_ = v_msg_387_;
v___y_374_ = v_a_363_;
v___y_375_ = v_a_364_;
v___y_376_ = v_a_365_;
v___y_377_ = v_a_366_;
v___y_378_ = v_a_367_;
v___y_379_ = v_a_368_;
v___y_380_ = v_a_369_;
v___y_381_ = v_a_370_;
goto v___jp_372_;
}
else
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; uint8_t v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; uint8_t v___x_399_; lean_object* v___x_400_; 
v___x_389_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__3));
v___x_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
lean_ctor_set(v___x_390_, 1, v_replacement_362_);
v___x_391_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
lean_ctor_set(v___x_391_, 1, v___x_384_);
lean_ctor_set(v___x_391_, 2, v___x_384_);
lean_ctor_set(v___x_391_, 3, v___x_384_);
lean_ctor_set(v___x_391_, 4, v___x_384_);
lean_ctor_set(v___x_391_, 5, v___x_384_);
lean_inc(v_ref_361_);
v___x_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_392_, 0, v_ref_361_);
v___x_393_ = 4;
lean_inc_ref(v___x_392_);
v___x_394_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_394_, 0, v___x_391_);
lean_ctor_set(v___x_394_, 1, v___x_392_);
lean_ctor_set(v___x_394_, 2, v___x_384_);
lean_ctor_set_uint8(v___x_394_, sizeof(void*)*3, v___x_393_);
v___x_395_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__6);
v___x_396_ = lean_unsigned_to_nat(1u);
v___x_397_ = lean_mk_empty_array_with_capacity(v___x_396_);
v___x_398_ = lean_array_push(v___x_397_, v___x_394_);
v___x_399_ = 0;
v___x_400_ = l_Lean_MessageData_hint(v___x_395_, v___x_398_, v___x_392_, v___x_384_, v___x_399_, v_a_369_, v_a_370_);
lean_dec_ref(v___x_398_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_a_401_; lean_object* v___x_402_; 
v_a_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_a_401_);
lean_dec_ref_known(v___x_400_, 1);
v___x_402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_402_, 0, v_msg_387_);
lean_ctor_set(v___x_402_, 1, v_a_401_);
v_msg_373_ = v___x_402_;
v___y_374_ = v_a_363_;
v___y_375_ = v_a_364_;
v___y_376_ = v_a_365_;
v___y_377_ = v_a_366_;
v___y_378_ = v_a_367_;
v___y_379_ = v_a_368_;
v___y_380_ = v_a_369_;
v___y_381_ = v_a_370_;
goto v___jp_372_;
}
else
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_410_; 
lean_dec(v_ref_361_);
v_a_403_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_410_ == 0)
{
v___x_405_ = v___x_400_;
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_400_);
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
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_418_; 
lean_dec(v_replacement_362_);
lean_dec(v_ref_361_);
v_a_411_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_418_ == 0)
{
v___x_413_ = v___x_385_;
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_385_);
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
v___jp_372_:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = l_Lean_linter_unnecessarySimpa;
v___x_383_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0(v___x_382_, v_ref_361_, v_msg_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
return v___x_383_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___boxed(lean_object* v_initialState_419_, lean_object* v_ref_420_, lean_object* v_replacement_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa(v_initialState_419_, v_ref_420_, v_replacement_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_);
lean_dec(v_a_429_);
lean_dec_ref(v_a_428_);
lean_dec(v_a_427_);
lean_dec_ref(v_a_426_);
lean_dec(v_a_425_);
lean_dec_ref(v_a_424_);
lean_dec(v_a_423_);
lean_dec_ref(v_a_422_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1(lean_object* v_ref_432_, lean_object* v_msgData_433_, uint8_t v_severity_434_, uint8_t v_isSilent_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg(v_ref_432_, v_msgData_433_, v_severity_434_, v_isSilent_435_, v___y_440_, v___y_441_, v___y_442_, v___y_443_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_446_, lean_object* v_msgData_447_, lean_object* v_severity_448_, lean_object* v_isSilent_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
uint8_t v_severity_boxed_459_; uint8_t v_isSilent_boxed_460_; lean_object* v_res_461_; 
v_severity_boxed_459_ = lean_unbox(v_severity_448_);
v_isSilent_boxed_460_ = lean_unbox(v_isSilent_449_);
v_res_461_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1(v_ref_446_, v_msgData_447_, v_severity_boxed_459_, v_isSilent_boxed_460_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
lean_dec(v_ref_446_);
return v_res_461_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_462_ = lean_box(0);
v___x_463_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
lean_ctor_set(v___x_464_, 1, v___x_462_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg(){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0);
v___x_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___boxed(lean_object* v___y_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0(lean_object* v_00_u03b1_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___boxed(lean_object* v_00_u03b1_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0(v_00_u03b1_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___redArg___lam__0(lean_object* v_x_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
lean_object* v___x_502_; 
lean_inc(v___y_496_);
lean_inc_ref(v___y_495_);
lean_inc(v___y_494_);
lean_inc_ref(v___y_493_);
v___x_502_ = lean_apply_9(v_x_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, lean_box(0));
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___redArg___lam__0___boxed(lean_object* v_x_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___redArg___lam__0(v_x_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___redArg(lean_object* v_mvarId_514_, lean_object* v_x_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v___f_525_; lean_object* v___x_526_; 
lean_inc(v___y_519_);
lean_inc_ref(v___y_518_);
lean_inc(v___y_517_);
lean_inc_ref(v___y_516_);
v___f_525_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_525_, 0, v_x_515_);
lean_closure_set(v___f_525_, 1, v___y_516_);
lean_closure_set(v___f_525_, 2, v___y_517_);
lean_closure_set(v___f_525_, 3, v___y_518_);
lean_closure_set(v___f_525_, 4, v___y_519_);
v___x_526_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_514_, v___f_525_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
if (lean_obj_tag(v___x_526_) == 0)
{
return v___x_526_;
}
else
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___x_526_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_526_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___redArg___boxed(lean_object* v_mvarId_535_, lean_object* v_x_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___redArg(v_mvarId_535_, v_x_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(lean_object* v_00_u03b1_547_, lean_object* v_mvarId_548_, lean_object* v_x_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___redArg(v_mvarId_548_, v_x_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___boxed(lean_object* v_00_u03b1_560_, lean_object* v_mvarId_561_, lean_object* v_x_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(v_00_u03b1_560_, v_mvarId_561_, v_x_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
return v_res_572_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_573_ = lean_unsigned_to_nat(32u);
v___x_574_ = lean_mk_empty_array_with_capacity(v___x_573_);
v___x_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
return v___x_575_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__1(void){
_start:
{
size_t v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_576_ = ((size_t)5ULL);
v___x_577_ = lean_unsigned_to_nat(0u);
v___x_578_ = lean_unsigned_to_nat(32u);
v___x_579_ = lean_mk_empty_array_with_capacity(v___x_578_);
v___x_580_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__0);
v___x_581_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_581_, 0, v___x_580_);
lean_ctor_set(v___x_581_, 1, v___x_579_);
lean_ctor_set(v___x_581_, 2, v___x_577_);
lean_ctor_set(v___x_581_, 3, v___x_577_);
lean_ctor_set_usize(v___x_581_, 4, v___x_576_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(lean_object* v___y_582_){
_start:
{
lean_object* v___x_584_; lean_object* v_infoState_585_; lean_object* v_trees_586_; lean_object* v___x_587_; lean_object* v_infoState_588_; lean_object* v_env_589_; lean_object* v_nextMacroScope_590_; lean_object* v_ngen_591_; lean_object* v_auxDeclNGen_592_; lean_object* v_traceState_593_; lean_object* v_cache_594_; lean_object* v_messages_595_; lean_object* v_snapshotTasks_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_617_; 
v___x_584_ = lean_st_ref_get(v___y_582_);
v_infoState_585_ = lean_ctor_get(v___x_584_, 7);
lean_inc_ref(v_infoState_585_);
lean_dec(v___x_584_);
v_trees_586_ = lean_ctor_get(v_infoState_585_, 2);
lean_inc_ref(v_trees_586_);
lean_dec_ref(v_infoState_585_);
v___x_587_ = lean_st_ref_take(v___y_582_);
v_infoState_588_ = lean_ctor_get(v___x_587_, 7);
v_env_589_ = lean_ctor_get(v___x_587_, 0);
v_nextMacroScope_590_ = lean_ctor_get(v___x_587_, 1);
v_ngen_591_ = lean_ctor_get(v___x_587_, 2);
v_auxDeclNGen_592_ = lean_ctor_get(v___x_587_, 3);
v_traceState_593_ = lean_ctor_get(v___x_587_, 4);
v_cache_594_ = lean_ctor_get(v___x_587_, 5);
v_messages_595_ = lean_ctor_get(v___x_587_, 6);
v_snapshotTasks_596_ = lean_ctor_get(v___x_587_, 8);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_617_ == 0)
{
v___x_598_ = v___x_587_;
v_isShared_599_ = v_isSharedCheck_617_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_snapshotTasks_596_);
lean_inc(v_infoState_588_);
lean_inc(v_messages_595_);
lean_inc(v_cache_594_);
lean_inc(v_traceState_593_);
lean_inc(v_auxDeclNGen_592_);
lean_inc(v_ngen_591_);
lean_inc(v_nextMacroScope_590_);
lean_inc(v_env_589_);
lean_dec(v___x_587_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_617_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
uint8_t v_enabled_600_; lean_object* v_assignment_601_; lean_object* v_lazyAssignment_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_615_; 
v_enabled_600_ = lean_ctor_get_uint8(v_infoState_588_, sizeof(void*)*3);
v_assignment_601_ = lean_ctor_get(v_infoState_588_, 0);
v_lazyAssignment_602_ = lean_ctor_get(v_infoState_588_, 1);
v_isSharedCheck_615_ = !lean_is_exclusive(v_infoState_588_);
if (v_isSharedCheck_615_ == 0)
{
lean_object* v_unused_616_; 
v_unused_616_ = lean_ctor_get(v_infoState_588_, 2);
lean_dec(v_unused_616_);
v___x_604_ = v_infoState_588_;
v_isShared_605_ = v_isSharedCheck_615_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_lazyAssignment_602_);
lean_inc(v_assignment_601_);
lean_dec(v_infoState_588_);
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
lean_ctor_set(v___x_598_, 7, v___x_608_);
v___x_610_ = v___x_598_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_env_589_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_nextMacroScope_590_);
lean_ctor_set(v_reuseFailAlloc_613_, 2, v_ngen_591_);
lean_ctor_set(v_reuseFailAlloc_613_, 3, v_auxDeclNGen_592_);
lean_ctor_set(v_reuseFailAlloc_613_, 4, v_traceState_593_);
lean_ctor_set(v_reuseFailAlloc_613_, 5, v_cache_594_);
lean_ctor_set(v_reuseFailAlloc_613_, 6, v_messages_595_);
lean_ctor_set(v_reuseFailAlloc_613_, 7, v___x_608_);
lean_ctor_set(v_reuseFailAlloc_613_, 8, v_snapshotTasks_596_);
v___x_610_ = v_reuseFailAlloc_613_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_st_ref_put(v___y_582_, v___x_610_);
v___x_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_612_, 0, v_trees_586_);
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
lean_object* v___f_652_; lean_object* v___x_83773__overap_653_; lean_object* v___x_654_; 
v___f_652_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___closed__0));
v___x_83773__overap_653_ = lean_panic_fn_borrowed(v___f_652_, v_msg_642_);
lean_inc(v___y_650_);
lean_inc_ref(v___y_649_);
lean_inc(v___y_648_);
lean_inc_ref(v___y_647_);
lean_inc(v___y_646_);
lean_inc_ref(v___y_645_);
lean_inc(v___y_644_);
lean_inc_ref(v___y_643_);
v___x_654_ = lean_apply_9(v___x_83773__overap_653_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, lean_box(0));
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
v_ref_675_ = lean_ctor_get(v___y_672_, 4);
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
v___x_696_ = l_Array_mkArray0(lean_box(0));
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
v_ref_882_ = lean_ctor_get(v___y_724_, 4);
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
v___x_901_ = l_Lean_Syntax_node5(v___x_884_, v___x_893_, v___x_705_, v___y_897_, v___y_896_, v___y_895_, v___x_900_);
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
v___y_895_ = v___x_911_;
v___y_896_ = v___y_907_;
v___y_897_ = v___y_908_;
v___y_898_ = v___x_913_;
goto v___jp_894_;
}
else
{
lean_object* v___x_914_; 
lean_dec(v_loc_717_);
v___x_914_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___y_895_ = v___x_911_;
v___y_896_ = v___y_907_;
v___y_897_ = v___y_908_;
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
v___y_907_ = v___x_919_;
v___y_908_ = v___y_916_;
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
v___y_907_ = v___x_919_;
v___y_908_ = v___y_916_;
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
v_ref_949_ = lean_ctor_get(v___y_724_, 4);
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
lean_inc_ref(v___y_735_);
v___x_737_ = l_Array_append___redArg(v___y_735_, v___y_736_);
lean_dec_ref(v___y_736_);
lean_inc(v___y_729_);
lean_inc(v___y_734_);
v___x_738_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_738_, 0, v___y_734_);
lean_ctor_set(v___x_738_, 1, v___y_729_);
lean_ctor_set(v___x_738_, 2, v___x_737_);
v___x_739_ = l_Lean_Syntax_node6(v___y_734_, v___y_728_, v___y_733_, v___x_705_, v___y_731_, v___y_732_, v___y_730_, v___x_738_);
v___x_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
return v___x_740_;
}
v___jp_741_:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
lean_inc_ref(v___y_748_);
v___x_750_ = l_Array_append___redArg(v___y_748_, v___y_749_);
lean_dec_ref(v___y_749_);
lean_inc(v___y_743_);
lean_inc(v___y_747_);
v___x_751_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_751_, 0, v___y_747_);
lean_ctor_set(v___x_751_, 1, v___y_743_);
lean_ctor_set(v___x_751_, 2, v___x_750_);
if (lean_obj_tag(v_loc_717_) == 1)
{
lean_object* v_val_752_; lean_object* v___x_753_; 
v_val_752_ = lean_ctor_get(v_loc_717_, 0);
lean_inc(v_val_752_);
lean_dec_ref_known(v_loc_717_, 1);
v___x_753_ = l_Array_mkArray1___redArg(v_val_752_);
v___y_728_ = v___y_742_;
v___y_729_ = v___y_743_;
v___y_730_ = v___x_751_;
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
v___y_729_ = v___y_743_;
v___y_730_ = v___x_751_;
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
lean_inc_ref(v___y_761_);
v___x_763_ = l_Array_append___redArg(v___y_761_, v___y_762_);
lean_dec_ref(v___y_762_);
lean_inc(v___y_757_);
lean_inc(v___y_760_);
v___x_764_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_764_, 0, v___y_760_);
lean_ctor_set(v___x_764_, 1, v___y_757_);
lean_ctor_set(v___x_764_, 2, v___x_763_);
if (lean_obj_tag(v_args_707_) == 1)
{
lean_object* v_val_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v_val_765_ = lean_ctor_get(v_args_707_, 0);
v___x_766_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_760_, 3);
v___x_767_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_767_, 0, v___y_760_);
lean_ctor_set(v___x_767_, 1, v___x_766_);
lean_inc_ref(v___y_761_);
v___x_768_ = l_Array_append___redArg(v___y_761_, v_val_765_);
lean_inc(v___y_757_);
v___x_769_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_769_, 0, v___y_760_);
lean_ctor_set(v___x_769_, 1, v___y_757_);
lean_ctor_set(v___x_769_, 2, v___x_768_);
v___x_770_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_771_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_771_, 0, v___y_760_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
v___x_772_ = l_Array_mkArray3___redArg(v___x_767_, v___x_769_, v___x_771_);
v___y_742_ = v___y_756_;
v___y_743_ = v___y_757_;
v___y_744_ = v___y_758_;
v___y_745_ = v___x_764_;
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
v___y_743_ = v___y_757_;
v___y_744_ = v___y_758_;
v___y_745_ = v___x_764_;
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
lean_inc_ref(v___y_779_);
v___x_781_ = l_Array_append___redArg(v___y_779_, v___y_780_);
lean_dec_ref(v___y_780_);
lean_inc(v___y_776_);
lean_inc(v___y_778_);
v___x_782_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_782_, 0, v___y_778_);
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
v___y_757_ = v___y_776_;
v___y_758_ = v___x_782_;
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
v___y_757_ = v___y_776_;
v___y_758_ = v___x_782_;
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
v_ref_791_ = lean_ctor_get(v___y_724_, 4);
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
v___y_775_ = v___x_794_;
v___y_776_ = v___x_796_;
v___y_777_ = v___x_795_;
v___y_778_ = v___x_792_;
v___y_779_ = v___x_797_;
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
v___y_775_ = v___x_794_;
v___y_776_ = v___x_796_;
v___y_777_ = v___x_795_;
v___y_778_ = v___x_792_;
v___y_779_ = v___x_797_;
v___y_780_ = v___x_801_;
goto v___jp_774_;
}
}
v___jp_802_:
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
lean_inc_ref(v___y_808_);
v___x_812_ = l_Array_append___redArg(v___y_808_, v___y_811_);
lean_dec_ref(v___y_811_);
lean_inc(v___y_803_);
lean_inc(v___y_809_);
v___x_813_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_813_, 0, v___y_809_);
lean_ctor_set(v___x_813_, 1, v___y_803_);
lean_ctor_set(v___x_813_, 2, v___x_812_);
v___x_814_ = l_Lean_Syntax_node6(v___y_809_, v___y_810_, v___y_804_, v___x_705_, v___y_807_, v___y_806_, v___y_805_, v___x_813_);
v___x_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
return v___x_815_;
}
v___jp_816_:
{
lean_object* v___x_825_; lean_object* v___x_826_; 
lean_inc_ref(v___y_821_);
v___x_825_ = l_Array_append___redArg(v___y_821_, v___y_824_);
lean_dec_ref(v___y_824_);
lean_inc(v___y_817_);
lean_inc(v___y_822_);
v___x_826_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_826_, 0, v___y_822_);
lean_ctor_set(v___x_826_, 1, v___y_817_);
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
v___y_805_ = v___x_826_;
v___y_806_ = v___y_820_;
v___y_807_ = v___y_819_;
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
v___y_805_ = v___x_826_;
v___y_806_ = v___y_820_;
v___y_807_ = v___y_819_;
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
lean_inc(v___y_831_);
lean_inc(v___y_835_);
v___x_839_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_839_, 0, v___y_835_);
lean_ctor_set(v___x_839_, 1, v___y_831_);
lean_ctor_set(v___x_839_, 2, v___x_838_);
if (lean_obj_tag(v_args_707_) == 1)
{
lean_object* v_val_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v_val_840_ = lean_ctor_get(v_args_707_, 0);
v___x_841_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_835_, 3);
v___x_842_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_842_, 0, v___y_835_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
lean_inc_ref(v___y_834_);
v___x_843_ = l_Array_append___redArg(v___y_834_, v_val_840_);
lean_inc(v___y_831_);
v___x_844_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_844_, 0, v___y_835_);
lean_ctor_set(v___x_844_, 1, v___y_831_);
lean_ctor_set(v___x_844_, 2, v___x_843_);
v___x_845_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_846_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_846_, 0, v___y_835_);
lean_ctor_set(v___x_846_, 1, v___x_845_);
v___x_847_ = l_Array_mkArray3___redArg(v___x_842_, v___x_844_, v___x_846_);
v___y_817_ = v___y_831_;
v___y_818_ = v___y_832_;
v___y_819_ = v___y_833_;
v___y_820_ = v___x_839_;
v___y_821_ = v___y_834_;
v___y_822_ = v___y_835_;
v___y_823_ = v___y_836_;
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
v___y_820_ = v___x_839_;
v___y_821_ = v___y_834_;
v___y_822_ = v___y_835_;
v___y_823_ = v___y_836_;
v___y_824_ = v___x_848_;
goto v___jp_816_;
}
}
v___jp_849_:
{
lean_object* v___x_856_; lean_object* v___x_857_; 
lean_inc_ref(v___y_852_);
v___x_856_ = l_Array_append___redArg(v___y_852_, v___y_855_);
lean_dec_ref(v___y_855_);
lean_inc(v___y_850_);
lean_inc(v___y_853_);
v___x_857_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_857_, 0, v___y_853_);
lean_ctor_set(v___x_857_, 1, v___y_850_);
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
v___y_833_ = v___x_857_;
v___y_834_ = v___y_852_;
v___y_835_ = v___y_853_;
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
v___y_833_ = v___x_857_;
v___y_834_ = v___y_852_;
v___y_835_ = v___y_853_;
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
v_ref_866_ = lean_ctor_get(v___y_724_, 4);
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
v___y_850_ = v___x_872_;
v___y_851_ = v___x_871_;
v___y_852_ = v___x_873_;
v___y_853_ = v___x_867_;
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
v___y_850_ = v___x_872_;
v___y_851_ = v___x_871_;
v___y_852_ = v___x_873_;
v___y_853_ = v___x_867_;
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
uint8_t v___x_92932__boxed_1038_; uint8_t v___x_92937__boxed_1039_; lean_object* v_res_1040_; 
v___x_92932__boxed_1038_ = lean_unbox(v___x_1020_);
v___x_92937__boxed_1039_ = lean_unbox(v___x_1026_);
v_res_1040_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1(v___x_1016_, v___x_1017_, v_args_1018_, v_only_1019_, v___x_92932__boxed_1038_, v___x_1021_, v___x_1022_, v___x_1023_, v___y_1024_, v_unfold_1025_, v___x_92937__boxed_1039_, v_squeeze_1027_, v_loc_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3(lean_object* v_a_1088_, lean_object* v_a_1089_, uint8_t v___x_1090_, uint8_t v___x_1091_, lean_object* v_a_1092_, lean_object* v_mvarCounter_1093_, lean_object* v___x_1094_, lean_object* v___x_1095_, uint8_t v_useReducible_1096_, uint8_t v___x_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
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
v___x_1146_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_1091_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
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
lean_dec_ref(v___x_1094_);
lean_dec_ref(v_a_1092_);
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
lean_inc_ref(v_a_1092_);
v___x_1163_ = l_Lean_indentExpr(v_a_1092_);
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
lean_dec_ref(v___x_1094_);
lean_dec_ref(v_a_1092_);
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
lean_dec_ref(v___x_1094_);
lean_dec_ref(v_a_1092_);
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
lean_dec_ref(v___x_1094_);
lean_dec_ref(v_a_1092_);
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
lean_dec_ref(v___x_1094_);
lean_dec_ref(v_a_1092_);
lean_dec(v_a_1088_);
return v___x_1146_;
}
v___jp_1113_:
{
lean_object* v___x_1122_; 
v___x_1122_ = l_Lean_Meta_getMVars(v_a_1092_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v_a_1123_; lean_object* v___x_1124_; 
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_a_1123_);
lean_dec_ref_known(v___x_1122_, 1);
v___x_1124_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(v_a_1123_, v_mvarCounter_1093_, v___y_1119_);
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
v___x_1128_ = l_Lean_Name_mkStr1(v___x_1094_);
v___x_1129_ = l_Lean_Elab_Tactic_closeMainGoal___redArg(v___x_1128_, v_a_1112_, v___x_1091_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
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
lean_dec_ref(v___x_1094_);
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
lean_dec_ref(v___x_1094_);
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
lean_dec_ref(v___x_1094_);
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
lean_dec_ref(v___x_1094_);
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
lean_dec_ref(v___x_1094_);
lean_dec_ref(v_a_1092_);
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
lean_dec_ref(v___x_1094_);
lean_dec_ref(v_a_1092_);
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
lean_object* v___x_1350_ = _args[3];
lean_object* v_a_1351_ = _args[4];
lean_object* v_mvarCounter_1352_ = _args[5];
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
uint8_t v___x_93647__boxed_1366_; uint8_t v___x_93648__boxed_1367_; uint8_t v_useReducible_boxed_1368_; uint8_t v___x_93652__boxed_1369_; lean_object* v_res_1370_; 
v___x_93647__boxed_1366_ = lean_unbox(v___x_1349_);
v___x_93648__boxed_1367_ = lean_unbox(v___x_1350_);
v_useReducible_boxed_1368_ = lean_unbox(v_useReducible_1355_);
v___x_93652__boxed_1369_ = lean_unbox(v___x_1356_);
v_res_1370_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3(v_a_1347_, v_a_1348_, v___x_93647__boxed_1366_, v___x_93648__boxed_1367_, v_a_1351_, v_mvarCounter_1352_, v___x_1353_, v___x_1354_, v_useReducible_boxed_1368_, v___x_93652__boxed_1369_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v_mvarCounter_1352_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4(lean_object* v_a_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v___x_1381_; lean_object* v_infoState_1382_; lean_object* v_env_1383_; lean_object* v_nextMacroScope_1384_; lean_object* v_ngen_1385_; lean_object* v_auxDeclNGen_1386_; lean_object* v_traceState_1387_; lean_object* v_cache_1388_; lean_object* v_messages_1389_; lean_object* v_snapshotTasks_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1411_; 
v___x_1381_ = lean_st_ref_take(v___y_1379_);
v_infoState_1382_ = lean_ctor_get(v___x_1381_, 7);
v_env_1383_ = lean_ctor_get(v___x_1381_, 0);
v_nextMacroScope_1384_ = lean_ctor_get(v___x_1381_, 1);
v_ngen_1385_ = lean_ctor_get(v___x_1381_, 2);
v_auxDeclNGen_1386_ = lean_ctor_get(v___x_1381_, 3);
v_traceState_1387_ = lean_ctor_get(v___x_1381_, 4);
v_cache_1388_ = lean_ctor_get(v___x_1381_, 5);
v_messages_1389_ = lean_ctor_get(v___x_1381_, 6);
v_snapshotTasks_1390_ = lean_ctor_get(v___x_1381_, 8);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1392_ = v___x_1381_;
v_isShared_1393_ = v_isSharedCheck_1411_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_snapshotTasks_1390_);
lean_inc(v_infoState_1382_);
lean_inc(v_messages_1389_);
lean_inc(v_cache_1388_);
lean_inc(v_traceState_1387_);
lean_inc(v_auxDeclNGen_1386_);
lean_inc(v_ngen_1385_);
lean_inc(v_nextMacroScope_1384_);
lean_inc(v_env_1383_);
lean_dec(v___x_1381_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1411_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
uint8_t v_enabled_1394_; lean_object* v_assignment_1395_; lean_object* v_lazyAssignment_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1409_; 
v_enabled_1394_ = lean_ctor_get_uint8(v_infoState_1382_, sizeof(void*)*3);
v_assignment_1395_ = lean_ctor_get(v_infoState_1382_, 0);
v_lazyAssignment_1396_ = lean_ctor_get(v_infoState_1382_, 1);
v_isSharedCheck_1409_ = !lean_is_exclusive(v_infoState_1382_);
if (v_isSharedCheck_1409_ == 0)
{
lean_object* v_unused_1410_; 
v_unused_1410_ = lean_ctor_get(v_infoState_1382_, 2);
lean_dec(v_unused_1410_);
v___x_1398_ = v_infoState_1382_;
v_isShared_1399_ = v_isSharedCheck_1409_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_lazyAssignment_1396_);
lean_inc(v_assignment_1395_);
lean_dec(v_infoState_1382_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1409_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 2, v_a_1371_);
v___x_1401_ = v___x_1398_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_assignment_1395_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v_lazyAssignment_1396_);
lean_ctor_set(v_reuseFailAlloc_1408_, 2, v_a_1371_);
lean_ctor_set_uint8(v_reuseFailAlloc_1408_, sizeof(void*)*3, v_enabled_1394_);
v___x_1401_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
lean_object* v___x_1403_; 
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 7, v___x_1401_);
v___x_1403_ = v___x_1392_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_env_1383_);
lean_ctor_set(v_reuseFailAlloc_1407_, 1, v_nextMacroScope_1384_);
lean_ctor_set(v_reuseFailAlloc_1407_, 2, v_ngen_1385_);
lean_ctor_set(v_reuseFailAlloc_1407_, 3, v_auxDeclNGen_1386_);
lean_ctor_set(v_reuseFailAlloc_1407_, 4, v_traceState_1387_);
lean_ctor_set(v_reuseFailAlloc_1407_, 5, v_cache_1388_);
lean_ctor_set(v_reuseFailAlloc_1407_, 6, v_messages_1389_);
lean_ctor_set(v_reuseFailAlloc_1407_, 7, v___x_1401_);
lean_ctor_set(v_reuseFailAlloc_1407_, 8, v_snapshotTasks_1390_);
v___x_1403_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1404_ = lean_st_ref_put(v___y_1379_, v___x_1403_);
v___x_1405_ = lean_box(0);
v___x_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1405_);
return v___x_1406_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___boxed(lean_object* v_a_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4(v_a_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
return v_res_1422_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___redArg(lean_object* v_a_1423_, lean_object* v_x_1424_){
_start:
{
if (lean_obj_tag(v_x_1424_) == 0)
{
uint8_t v___x_1425_; 
v___x_1425_ = 0;
return v___x_1425_;
}
else
{
lean_object* v_key_1426_; lean_object* v_tail_1427_; uint8_t v___x_1428_; 
v_key_1426_ = lean_ctor_get(v_x_1424_, 0);
v_tail_1427_ = lean_ctor_get(v_x_1424_, 2);
v___x_1428_ = lean_expr_eqv(v_key_1426_, v_a_1423_);
if (v___x_1428_ == 0)
{
v_x_1424_ = v_tail_1427_;
goto _start;
}
else
{
return v___x_1428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___redArg___boxed(lean_object* v_a_1430_, lean_object* v_x_1431_){
_start:
{
uint8_t v_res_1432_; lean_object* v_r_1433_; 
v_res_1432_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___redArg(v_a_1430_, v_x_1431_);
lean_dec(v_x_1431_);
lean_dec_ref(v_a_1430_);
v_r_1433_ = lean_box(v_res_1432_);
return v_r_1433_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(lean_object* v_m_1434_, lean_object* v_a_1435_){
_start:
{
lean_object* v_buckets_1436_; lean_object* v___x_1437_; uint64_t v___x_1438_; uint64_t v___x_1439_; uint64_t v___x_1440_; uint64_t v_fold_1441_; uint64_t v___x_1442_; uint64_t v___x_1443_; uint64_t v___x_1444_; size_t v___x_1445_; size_t v___x_1446_; size_t v___x_1447_; size_t v___x_1448_; size_t v___x_1449_; lean_object* v___x_1450_; uint8_t v___x_1451_; 
v_buckets_1436_ = lean_ctor_get(v_m_1434_, 1);
v___x_1437_ = lean_array_get_size(v_buckets_1436_);
v___x_1438_ = l_Lean_Expr_hash(v_a_1435_);
v___x_1439_ = 32ULL;
v___x_1440_ = lean_uint64_shift_right(v___x_1438_, v___x_1439_);
v_fold_1441_ = lean_uint64_xor(v___x_1438_, v___x_1440_);
v___x_1442_ = 16ULL;
v___x_1443_ = lean_uint64_shift_right(v_fold_1441_, v___x_1442_);
v___x_1444_ = lean_uint64_xor(v_fold_1441_, v___x_1443_);
v___x_1445_ = lean_uint64_to_usize(v___x_1444_);
v___x_1446_ = lean_usize_of_nat(v___x_1437_);
v___x_1447_ = ((size_t)1ULL);
v___x_1448_ = lean_usize_sub(v___x_1446_, v___x_1447_);
v___x_1449_ = lean_usize_land(v___x_1445_, v___x_1448_);
v___x_1450_ = lean_array_uget_borrowed(v_buckets_1436_, v___x_1449_);
v___x_1451_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___redArg(v_a_1435_, v___x_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg___boxed(lean_object* v_m_1452_, lean_object* v_a_1453_){
_start:
{
uint8_t v_res_1454_; lean_object* v_r_1455_; 
v_res_1454_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(v_m_1452_, v_a_1453_);
lean_dec_ref(v_a_1453_);
lean_dec_ref(v_m_1452_);
v_r_1455_ = lean_box(v_res_1454_);
return v_r_1455_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13_spec__15_spec__20___redArg(lean_object* v_x_1456_, lean_object* v_x_1457_){
_start:
{
if (lean_obj_tag(v_x_1457_) == 0)
{
return v_x_1456_;
}
else
{
lean_object* v_key_1458_; lean_object* v_value_1459_; lean_object* v_tail_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1483_; 
v_key_1458_ = lean_ctor_get(v_x_1457_, 0);
v_value_1459_ = lean_ctor_get(v_x_1457_, 1);
v_tail_1460_ = lean_ctor_get(v_x_1457_, 2);
v_isSharedCheck_1483_ = !lean_is_exclusive(v_x_1457_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1462_ = v_x_1457_;
v_isShared_1463_ = v_isSharedCheck_1483_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_tail_1460_);
lean_inc(v_value_1459_);
lean_inc(v_key_1458_);
lean_dec(v_x_1457_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1483_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1464_; uint64_t v___x_1465_; uint64_t v___x_1466_; uint64_t v___x_1467_; uint64_t v_fold_1468_; uint64_t v___x_1469_; uint64_t v___x_1470_; uint64_t v___x_1471_; size_t v___x_1472_; size_t v___x_1473_; size_t v___x_1474_; size_t v___x_1475_; size_t v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1479_; 
v___x_1464_ = lean_array_get_size(v_x_1456_);
v___x_1465_ = l_Lean_Expr_hash(v_key_1458_);
v___x_1466_ = 32ULL;
v___x_1467_ = lean_uint64_shift_right(v___x_1465_, v___x_1466_);
v_fold_1468_ = lean_uint64_xor(v___x_1465_, v___x_1467_);
v___x_1469_ = 16ULL;
v___x_1470_ = lean_uint64_shift_right(v_fold_1468_, v___x_1469_);
v___x_1471_ = lean_uint64_xor(v_fold_1468_, v___x_1470_);
v___x_1472_ = lean_uint64_to_usize(v___x_1471_);
v___x_1473_ = lean_usize_of_nat(v___x_1464_);
v___x_1474_ = ((size_t)1ULL);
v___x_1475_ = lean_usize_sub(v___x_1473_, v___x_1474_);
v___x_1476_ = lean_usize_land(v___x_1472_, v___x_1475_);
v___x_1477_ = lean_array_uget_borrowed(v_x_1456_, v___x_1476_);
lean_inc(v___x_1477_);
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 2, v___x_1477_);
v___x_1479_ = v___x_1462_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_key_1458_);
lean_ctor_set(v_reuseFailAlloc_1482_, 1, v_value_1459_);
lean_ctor_set(v_reuseFailAlloc_1482_, 2, v___x_1477_);
v___x_1479_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
lean_object* v___x_1480_; 
v___x_1480_ = lean_array_uset(v_x_1456_, v___x_1476_, v___x_1479_);
v_x_1456_ = v___x_1480_;
v_x_1457_ = v_tail_1460_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13_spec__15___redArg(lean_object* v_i_1484_, lean_object* v_source_1485_, lean_object* v_target_1486_){
_start:
{
lean_object* v___x_1487_; uint8_t v___x_1488_; 
v___x_1487_ = lean_array_get_size(v_source_1485_);
v___x_1488_ = lean_nat_dec_lt(v_i_1484_, v___x_1487_);
if (v___x_1488_ == 0)
{
lean_dec_ref(v_source_1485_);
lean_dec(v_i_1484_);
return v_target_1486_;
}
else
{
lean_object* v_es_1489_; lean_object* v___x_1490_; lean_object* v_source_1491_; lean_object* v_target_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v_es_1489_ = lean_array_fget(v_source_1485_, v_i_1484_);
v___x_1490_ = lean_box(0);
v_source_1491_ = lean_array_fset(v_source_1485_, v_i_1484_, v___x_1490_);
v_target_1492_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13_spec__15_spec__20___redArg(v_target_1486_, v_es_1489_);
v___x_1493_ = lean_unsigned_to_nat(1u);
v___x_1494_ = lean_nat_add(v_i_1484_, v___x_1493_);
lean_dec(v_i_1484_);
v_i_1484_ = v___x_1494_;
v_source_1485_ = v_source_1491_;
v_target_1486_ = v_target_1492_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13___redArg(lean_object* v_data_1496_){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v_nbuckets_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1497_ = lean_array_get_size(v_data_1496_);
v___x_1498_ = lean_unsigned_to_nat(2u);
v_nbuckets_1499_ = lean_nat_mul(v___x_1497_, v___x_1498_);
v___x_1500_ = lean_unsigned_to_nat(0u);
v___x_1501_ = lean_box(0);
v___x_1502_ = lean_mk_array(v_nbuckets_1499_, v___x_1501_);
v___x_1503_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13_spec__15___redArg(v___x_1500_, v_data_1496_, v___x_1502_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(lean_object* v_m_1504_, lean_object* v_a_1505_, lean_object* v_b_1506_){
_start:
{
lean_object* v_size_1507_; lean_object* v_buckets_1508_; lean_object* v___x_1509_; uint64_t v___x_1510_; uint64_t v___x_1511_; uint64_t v___x_1512_; uint64_t v_fold_1513_; uint64_t v___x_1514_; uint64_t v___x_1515_; uint64_t v___x_1516_; size_t v___x_1517_; size_t v___x_1518_; size_t v___x_1519_; size_t v___x_1520_; size_t v___x_1521_; lean_object* v_bkt_1522_; uint8_t v___x_1523_; 
v_size_1507_ = lean_ctor_get(v_m_1504_, 0);
v_buckets_1508_ = lean_ctor_get(v_m_1504_, 1);
v___x_1509_ = lean_array_get_size(v_buckets_1508_);
v___x_1510_ = l_Lean_Expr_hash(v_a_1505_);
v___x_1511_ = 32ULL;
v___x_1512_ = lean_uint64_shift_right(v___x_1510_, v___x_1511_);
v_fold_1513_ = lean_uint64_xor(v___x_1510_, v___x_1512_);
v___x_1514_ = 16ULL;
v___x_1515_ = lean_uint64_shift_right(v_fold_1513_, v___x_1514_);
v___x_1516_ = lean_uint64_xor(v_fold_1513_, v___x_1515_);
v___x_1517_ = lean_uint64_to_usize(v___x_1516_);
v___x_1518_ = lean_usize_of_nat(v___x_1509_);
v___x_1519_ = ((size_t)1ULL);
v___x_1520_ = lean_usize_sub(v___x_1518_, v___x_1519_);
v___x_1521_ = lean_usize_land(v___x_1517_, v___x_1520_);
v_bkt_1522_ = lean_array_uget_borrowed(v_buckets_1508_, v___x_1521_);
v___x_1523_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___redArg(v_a_1505_, v_bkt_1522_);
if (v___x_1523_ == 0)
{
lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1544_; 
lean_inc_ref(v_buckets_1508_);
lean_inc(v_size_1507_);
v_isSharedCheck_1544_ = !lean_is_exclusive(v_m_1504_);
if (v_isSharedCheck_1544_ == 0)
{
lean_object* v_unused_1545_; lean_object* v_unused_1546_; 
v_unused_1545_ = lean_ctor_get(v_m_1504_, 1);
lean_dec(v_unused_1545_);
v_unused_1546_ = lean_ctor_get(v_m_1504_, 0);
lean_dec(v_unused_1546_);
v___x_1525_ = v_m_1504_;
v_isShared_1526_ = v_isSharedCheck_1544_;
goto v_resetjp_1524_;
}
else
{
lean_dec(v_m_1504_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1544_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1527_; lean_object* v_size_x27_1528_; lean_object* v___x_1529_; lean_object* v_buckets_x27_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; uint8_t v___x_1536_; 
v___x_1527_ = lean_unsigned_to_nat(1u);
v_size_x27_1528_ = lean_nat_add(v_size_1507_, v___x_1527_);
lean_dec(v_size_1507_);
lean_inc(v_bkt_1522_);
v___x_1529_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1529_, 0, v_a_1505_);
lean_ctor_set(v___x_1529_, 1, v_b_1506_);
lean_ctor_set(v___x_1529_, 2, v_bkt_1522_);
v_buckets_x27_1530_ = lean_array_uset(v_buckets_1508_, v___x_1521_, v___x_1529_);
v___x_1531_ = lean_unsigned_to_nat(4u);
v___x_1532_ = lean_nat_mul(v_size_x27_1528_, v___x_1531_);
v___x_1533_ = lean_unsigned_to_nat(3u);
v___x_1534_ = lean_nat_div(v___x_1532_, v___x_1533_);
lean_dec(v___x_1532_);
v___x_1535_ = lean_array_get_size(v_buckets_x27_1530_);
v___x_1536_ = lean_nat_dec_le(v___x_1534_, v___x_1535_);
lean_dec(v___x_1534_);
if (v___x_1536_ == 0)
{
lean_object* v_val_1537_; lean_object* v___x_1539_; 
v_val_1537_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13___redArg(v_buckets_x27_1530_);
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 1, v_val_1537_);
lean_ctor_set(v___x_1525_, 0, v_size_x27_1528_);
v___x_1539_ = v___x_1525_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_size_x27_1528_);
lean_ctor_set(v_reuseFailAlloc_1540_, 1, v_val_1537_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
else
{
lean_object* v___x_1542_; 
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 1, v_buckets_x27_1530_);
lean_ctor_set(v___x_1525_, 0, v_size_x27_1528_);
v___x_1542_ = v___x_1525_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_size_x27_1528_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v_buckets_x27_1530_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
else
{
lean_dec(v_b_1506_);
lean_dec_ref(v_a_1505_);
return v_m_1504_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg(lean_object* v_mvarId_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
lean_object* v___x_1551_; lean_object* v_mctx_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1551_ = lean_st_ref_get(v___y_1549_);
v_mctx_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc_ref(v_mctx_1552_);
lean_dec(v___x_1551_);
v___x_1553_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_1552_, v_mvarId_1547_);
lean_dec_ref(v_mctx_1552_);
v___x_1554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1553_);
v___x_1555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1554_);
lean_ctor_set(v___x_1555_, 1, v___y_1548_);
v___x_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg___boxed(lean_object* v_mvarId_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg(v_mvarId_1557_, v___y_1558_, v___y_1559_);
lean_dec(v___y_1559_);
lean_dec(v_mvarId_1557_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__15___redArg(lean_object* v_mvarId_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v___x_1566_; lean_object* v_mctx_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1566_ = lean_st_ref_get(v___y_1564_);
v_mctx_1567_ = lean_ctor_get(v___x_1566_, 0);
lean_inc_ref(v_mctx_1567_);
lean_dec(v___x_1566_);
v___x_1568_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_1567_, v_mvarId_1562_);
lean_dec_ref(v_mctx_1567_);
v___x_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1568_);
v___x_1570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1569_);
lean_ctor_set(v___x_1570_, 1, v___y_1563_);
v___x_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__15___redArg___boxed(lean_object* v_mvarId_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
lean_object* v_res_1576_; 
v_res_1576_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__15___redArg(v_mvarId_1572_, v___y_1573_, v___y_1574_);
lean_dec(v___y_1574_);
lean_dec(v_mvarId_1572_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(lean_object* v_mvarId_1581_, lean_object* v_e_1582_, lean_object* v_a_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
lean_object* v_d_1594_; lean_object* v_b_1595_; lean_object* v___y_1596_; uint8_t v___x_1602_; 
v___x_1602_ = l_Lean_Expr_hasExprMVar(v_e_1582_);
if (v___x_1602_ == 0)
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
lean_dec_ref(v_e_1582_);
v___x_1603_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___closed__0));
v___x_1604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
lean_ctor_set(v___x_1604_, 1, v_a_1583_);
v___x_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1604_);
return v___x_1605_;
}
else
{
uint8_t v___x_1606_; 
v___x_1606_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(v_a_1583_, v_e_1582_);
if (v___x_1606_ == 0)
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1607_ = lean_box(0);
lean_inc_ref(v_e_1582_);
v___x_1608_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(v_a_1583_, v_e_1582_, v___x_1607_);
switch(lean_obj_tag(v_e_1582_))
{
case 11:
{
lean_object* v_struct_1609_; 
v_struct_1609_ = lean_ctor_get(v_e_1582_, 2);
lean_inc_ref(v_struct_1609_);
lean_dec_ref_known(v_e_1582_, 3);
v_e_1582_ = v_struct_1609_;
v_a_1583_ = v___x_1608_;
goto _start;
}
case 7:
{
lean_object* v_binderType_1611_; lean_object* v_body_1612_; 
v_binderType_1611_ = lean_ctor_get(v_e_1582_, 1);
lean_inc_ref(v_binderType_1611_);
v_body_1612_ = lean_ctor_get(v_e_1582_, 2);
lean_inc_ref(v_body_1612_);
lean_dec_ref_known(v_e_1582_, 3);
v_d_1594_ = v_binderType_1611_;
v_b_1595_ = v_body_1612_;
v___y_1596_ = v___x_1608_;
goto v___jp_1593_;
}
case 6:
{
lean_object* v_binderType_1613_; lean_object* v_body_1614_; 
v_binderType_1613_ = lean_ctor_get(v_e_1582_, 1);
lean_inc_ref(v_binderType_1613_);
v_body_1614_ = lean_ctor_get(v_e_1582_, 2);
lean_inc_ref(v_body_1614_);
lean_dec_ref_known(v_e_1582_, 3);
v_d_1594_ = v_binderType_1613_;
v_b_1595_ = v_body_1614_;
v___y_1596_ = v___x_1608_;
goto v___jp_1593_;
}
case 8:
{
lean_object* v_type_1615_; lean_object* v_value_1616_; lean_object* v_body_1617_; lean_object* v___x_1618_; 
v_type_1615_ = lean_ctor_get(v_e_1582_, 1);
lean_inc_ref(v_type_1615_);
v_value_1616_ = lean_ctor_get(v_e_1582_, 2);
lean_inc_ref(v_value_1616_);
v_body_1617_ = lean_ctor_get(v_e_1582_, 3);
lean_inc_ref(v_body_1617_);
lean_dec_ref_known(v_e_1582_, 4);
v___x_1618_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_1581_, v_type_1615_, v___x_1608_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; lean_object* v_fst_1620_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_a_1619_);
v_fst_1620_ = lean_ctor_get(v_a_1619_, 0);
if (lean_obj_tag(v_fst_1620_) == 0)
{
lean_dec(v_a_1619_);
lean_dec_ref(v_body_1617_);
lean_dec_ref(v_value_1616_);
return v___x_1618_;
}
else
{
lean_object* v_snd_1621_; lean_object* v___x_1622_; 
lean_dec_ref_known(v___x_1618_, 1);
v_snd_1621_ = lean_ctor_get(v_a_1619_, 1);
lean_inc(v_snd_1621_);
lean_dec(v_a_1619_);
v___x_1622_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_1581_, v_value_1616_, v_snd_1621_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; lean_object* v_fst_1624_; 
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_a_1623_);
v_fst_1624_ = lean_ctor_get(v_a_1623_, 0);
if (lean_obj_tag(v_fst_1624_) == 0)
{
lean_dec(v_a_1623_);
lean_dec_ref(v_body_1617_);
return v___x_1622_;
}
else
{
lean_object* v_snd_1625_; 
lean_dec_ref_known(v___x_1622_, 1);
v_snd_1625_ = lean_ctor_get(v_a_1623_, 1);
lean_inc(v_snd_1625_);
lean_dec(v_a_1623_);
v_e_1582_ = v_body_1617_;
v_a_1583_ = v_snd_1625_;
goto _start;
}
}
else
{
lean_dec_ref(v_body_1617_);
return v___x_1622_;
}
}
}
else
{
lean_dec_ref(v_body_1617_);
lean_dec_ref(v_value_1616_);
return v___x_1618_;
}
}
case 10:
{
lean_object* v_expr_1627_; 
v_expr_1627_ = lean_ctor_get(v_e_1582_, 1);
lean_inc_ref(v_expr_1627_);
lean_dec_ref_known(v_e_1582_, 2);
v_e_1582_ = v_expr_1627_;
v_a_1583_ = v___x_1608_;
goto _start;
}
case 5:
{
lean_object* v_fn_1629_; lean_object* v_arg_1630_; lean_object* v___x_1631_; 
v_fn_1629_ = lean_ctor_get(v_e_1582_, 0);
lean_inc_ref(v_fn_1629_);
v_arg_1630_ = lean_ctor_get(v_e_1582_, 1);
lean_inc_ref(v_arg_1630_);
lean_dec_ref_known(v_e_1582_, 2);
v___x_1631_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_1581_, v_fn_1629_, v___x_1608_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_a_1632_; lean_object* v_fst_1633_; 
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
lean_inc(v_a_1632_);
v_fst_1633_ = lean_ctor_get(v_a_1632_, 0);
if (lean_obj_tag(v_fst_1633_) == 0)
{
lean_dec(v_a_1632_);
lean_dec_ref(v_arg_1630_);
return v___x_1631_;
}
else
{
lean_object* v_snd_1634_; 
lean_dec_ref_known(v___x_1631_, 1);
v_snd_1634_ = lean_ctor_get(v_a_1632_, 1);
lean_inc(v_snd_1634_);
lean_dec(v_a_1632_);
v_e_1582_ = v_arg_1630_;
v_a_1583_ = v_snd_1634_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_1630_);
return v___x_1631_;
}
}
case 2:
{
lean_object* v_mvarId_1636_; lean_object* v___x_1637_; 
v_mvarId_1636_ = lean_ctor_get(v_e_1582_, 0);
lean_inc(v_mvarId_1636_);
lean_dec_ref_known(v_e_1582_, 1);
v___x_1637_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7(v_mvarId_1581_, v_mvarId_1636_, v___x_1608_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
return v___x_1637_;
}
default: 
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
lean_dec_ref(v_e_1582_);
v___x_1638_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___closed__0));
v___x_1639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
lean_ctor_set(v___x_1639_, 1, v___x_1608_);
v___x_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1639_);
return v___x_1640_;
}
}
}
else
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
lean_dec_ref(v_e_1582_);
v___x_1641_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___closed__0));
v___x_1642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1641_);
lean_ctor_set(v___x_1642_, 1, v_a_1583_);
v___x_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
return v___x_1643_;
}
}
v___jp_1593_:
{
lean_object* v___x_1597_; 
v___x_1597_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_1581_, v_d_1594_, v___y_1596_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_a_1598_; lean_object* v_fst_1599_; 
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
lean_inc(v_a_1598_);
v_fst_1599_ = lean_ctor_get(v_a_1598_, 0);
if (lean_obj_tag(v_fst_1599_) == 0)
{
lean_dec(v_a_1598_);
lean_dec_ref(v_b_1595_);
return v___x_1597_;
}
else
{
lean_object* v_snd_1600_; 
lean_dec_ref_known(v___x_1597_, 1);
v_snd_1600_ = lean_ctor_get(v_a_1598_, 1);
lean_inc(v_snd_1600_);
lean_dec(v_a_1598_);
v_e_1582_ = v_b_1595_;
v_a_1583_ = v_snd_1600_;
goto _start;
}
}
else
{
lean_dec_ref(v_b_1595_);
return v___x_1597_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7(lean_object* v_mvarId_1644_, lean_object* v_mvarId_x27_1645_, lean_object* v_a_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
uint8_t v___x_1656_; 
v___x_1656_ = l_Lean_instBEqMVarId_beq(v_mvarId_1644_, v_mvarId_x27_1645_);
if (v___x_1656_ == 0)
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__15___redArg(v_mvarId_x27_1645_, v_a_1646_, v___y_1652_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1741_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1660_ = v___x_1657_;
v_isShared_1661_ = v_isSharedCheck_1741_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1657_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1741_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v_fst_1662_; 
v_fst_1662_ = lean_ctor_get(v_a_1658_, 0);
lean_inc(v_fst_1662_);
if (lean_obj_tag(v_fst_1662_) == 0)
{
lean_object* v_snd_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1681_; 
lean_dec(v_mvarId_x27_1645_);
v_snd_1663_ = lean_ctor_get(v_a_1658_, 1);
v_isSharedCheck_1681_ = !lean_is_exclusive(v_a_1658_);
if (v_isSharedCheck_1681_ == 0)
{
lean_object* v_unused_1682_; 
v_unused_1682_ = lean_ctor_get(v_a_1658_, 0);
lean_dec(v_unused_1682_);
v___x_1665_ = v_a_1658_;
v_isShared_1666_ = v_isSharedCheck_1681_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_snd_1663_);
lean_dec(v_a_1658_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1681_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1680_; 
v_a_1667_ = lean_ctor_get(v_fst_1662_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v_fst_1662_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1669_ = v_fst_1662_;
v_isShared_1670_ = v_isSharedCheck_1680_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v_fst_1662_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1680_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1667_);
v___x_1672_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
lean_object* v___x_1674_; 
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 0, v___x_1672_);
v___x_1674_ = v___x_1665_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1672_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v_snd_1663_);
v___x_1674_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
lean_object* v___x_1676_; 
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 0, v___x_1674_);
v___x_1676_ = v___x_1660_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v___x_1674_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
}
}
else
{
lean_object* v_a_1683_; 
lean_del_object(v___x_1660_);
v_a_1683_ = lean_ctor_get(v_fst_1662_, 0);
lean_inc(v_a_1683_);
lean_dec_ref_known(v_fst_1662_, 1);
if (lean_obj_tag(v_a_1683_) == 0)
{
lean_object* v_snd_1684_; lean_object* v___x_1685_; 
v_snd_1684_ = lean_ctor_get(v_a_1658_, 1);
lean_inc(v_snd_1684_);
lean_dec(v_a_1658_);
v___x_1685_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg(v_mvarId_x27_1645_, v_snd_1684_, v___y_1652_);
lean_dec(v_mvarId_x27_1645_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1729_; 
v_a_1686_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1688_ = v___x_1685_;
v_isShared_1689_ = v_isSharedCheck_1729_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1685_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1729_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v_fst_1690_; 
v_fst_1690_ = lean_ctor_get(v_a_1686_, 0);
lean_inc(v_fst_1690_);
if (lean_obj_tag(v_fst_1690_) == 0)
{
lean_object* v_snd_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1709_; 
v_snd_1691_ = lean_ctor_get(v_a_1686_, 1);
v_isSharedCheck_1709_ = !lean_is_exclusive(v_a_1686_);
if (v_isSharedCheck_1709_ == 0)
{
lean_object* v_unused_1710_; 
v_unused_1710_ = lean_ctor_get(v_a_1686_, 0);
lean_dec(v_unused_1710_);
v___x_1693_ = v_a_1686_;
v_isShared_1694_ = v_isSharedCheck_1709_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_snd_1691_);
lean_dec(v_a_1686_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1709_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1708_; 
v_a_1695_ = lean_ctor_get(v_fst_1690_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v_fst_1690_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1697_ = v_fst_1690_;
v_isShared_1698_ = v_isSharedCheck_1708_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v_fst_1690_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1708_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1698_ == 0)
{
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_a_1695_);
v___x_1700_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
lean_object* v___x_1702_; 
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 0, v___x_1700_);
v___x_1702_ = v___x_1693_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1700_);
lean_ctor_set(v_reuseFailAlloc_1706_, 1, v_snd_1691_);
v___x_1702_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
lean_object* v___x_1704_; 
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 0, v___x_1702_);
v___x_1704_ = v___x_1688_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1702_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
}
}
}
else
{
lean_object* v_a_1711_; 
v_a_1711_ = lean_ctor_get(v_fst_1690_, 0);
lean_inc(v_a_1711_);
lean_dec_ref_known(v_fst_1690_, 1);
if (lean_obj_tag(v_a_1711_) == 0)
{
lean_object* v_snd_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1723_; 
v_snd_1712_ = lean_ctor_get(v_a_1686_, 1);
v_isSharedCheck_1723_ = !lean_is_exclusive(v_a_1686_);
if (v_isSharedCheck_1723_ == 0)
{
lean_object* v_unused_1724_; 
v_unused_1724_ = lean_ctor_get(v_a_1686_, 0);
lean_dec(v_unused_1724_);
v___x_1714_ = v_a_1686_;
v_isShared_1715_ = v_isSharedCheck_1723_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_snd_1712_);
lean_dec(v_a_1686_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1723_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1716_; lean_object* v___x_1718_; 
v___x_1716_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___closed__0));
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 0, v___x_1716_);
v___x_1718_ = v___x_1714_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1716_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_snd_1712_);
v___x_1718_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
lean_object* v___x_1720_; 
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 0, v___x_1718_);
v___x_1720_ = v___x_1688_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v___x_1718_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
else
{
lean_object* v_val_1725_; lean_object* v_snd_1726_; lean_object* v_mvarIdPending_1727_; 
lean_del_object(v___x_1688_);
v_val_1725_ = lean_ctor_get(v_a_1711_, 0);
lean_inc(v_val_1725_);
lean_dec_ref_known(v_a_1711_, 1);
v_snd_1726_ = lean_ctor_get(v_a_1686_, 1);
lean_inc(v_snd_1726_);
lean_dec(v_a_1686_);
v_mvarIdPending_1727_ = lean_ctor_get(v_val_1725_, 1);
lean_inc(v_mvarIdPending_1727_);
lean_dec(v_val_1725_);
v_mvarId_x27_1645_ = v_mvarIdPending_1727_;
v_a_1646_ = v_snd_1726_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1737_; 
v_a_1730_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1732_ = v___x_1685_;
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v___x_1685_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1735_; 
if (v_isShared_1733_ == 0)
{
v___x_1735_ = v___x_1732_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_a_1730_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
}
else
{
lean_object* v_snd_1738_; lean_object* v_val_1739_; lean_object* v___x_1740_; 
lean_dec(v_mvarId_x27_1645_);
v_snd_1738_ = lean_ctor_get(v_a_1658_, 1);
lean_inc(v_snd_1738_);
lean_dec(v_a_1658_);
v_val_1739_ = lean_ctor_get(v_a_1683_, 0);
lean_inc(v_val_1739_);
lean_dec_ref_known(v_a_1683_, 1);
v___x_1740_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_1644_, v_val_1739_, v_snd_1738_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
return v___x_1740_;
}
}
}
}
else
{
lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1749_; 
lean_dec(v_mvarId_x27_1645_);
v_a_1742_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1744_ = v___x_1657_;
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___x_1657_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1747_; 
if (v_isShared_1745_ == 0)
{
v___x_1747_ = v___x_1744_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_a_1742_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
else
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
lean_dec(v_mvarId_x27_1645_);
v___x_1750_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___closed__1));
v___x_1751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1750_);
lean_ctor_set(v___x_1751_, 1, v_a_1646_);
v___x_1752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1751_);
return v___x_1752_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___boxed(lean_object* v_mvarId_1753_, lean_object* v_mvarId_x27_1754_, lean_object* v_a_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7(v_mvarId_1753_, v_mvarId_x27_1754_, v_a_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v_mvarId_1753_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1___boxed(lean_object* v_mvarId_1766_, lean_object* v_e_1767_, lean_object* v_a_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_1766_, v_e_1767_, v_a_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec(v_mvarId_1766_);
return v_res_1778_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1779_ = lean_box(0);
v___x_1780_ = lean_unsigned_to_nat(16u);
v___x_1781_ = lean_mk_array(v___x_1780_, v___x_1779_);
return v___x_1781_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1782_ = lean_obj_once(&l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0, &l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0_once, _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0);
v___x_1783_ = lean_unsigned_to_nat(0u);
v___x_1784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1783_);
lean_ctor_set(v___x_1784_, 1, v___x_1782_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(lean_object* v_mvarId_1785_, lean_object* v_e_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
uint8_t v___x_1796_; 
v___x_1796_ = l_Lean_Expr_hasExprMVar(v_e_1786_);
if (v___x_1796_ == 0)
{
uint8_t v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
lean_dec_ref(v_e_1786_);
v___x_1797_ = 1;
v___x_1798_ = lean_box(v___x_1797_);
v___x_1799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1798_);
return v___x_1799_;
}
else
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1800_ = lean_obj_once(&l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1, &l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1_once, _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1);
v___x_1801_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_1785_, v_e_1786_, v___x_1800_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1816_; 
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1804_ = v___x_1801_;
v_isShared_1805_ = v_isSharedCheck_1816_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1801_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1816_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v_fst_1806_; 
v_fst_1806_ = lean_ctor_get(v_a_1802_, 0);
lean_inc(v_fst_1806_);
lean_dec(v_a_1802_);
if (lean_obj_tag(v_fst_1806_) == 0)
{
uint8_t v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1810_; 
lean_dec_ref_known(v_fst_1806_, 1);
v___x_1807_ = 0;
v___x_1808_ = lean_box(v___x_1807_);
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v___x_1808_);
v___x_1810_ = v___x_1804_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v___x_1808_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
else
{
lean_object* v___x_1812_; lean_object* v___x_1814_; 
lean_dec_ref_known(v_fst_1806_, 1);
v___x_1812_ = lean_box(v___x_1796_);
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v___x_1812_);
v___x_1814_ = v___x_1804_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1812_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
else
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1824_; 
v_a_1817_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1819_ = v___x_1801_;
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1801_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1822_; 
if (v_isShared_1820_ == 0)
{
v___x_1822_ = v___x_1819_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_a_1817_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___boxed(lean_object* v_mvarId_1825_, lean_object* v_e_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(v_mvarId_1825_, v_e_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v_mvarId_1825_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0(lean_object* v___y_1837_, lean_object* v_mkInfoTree_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v_a_1846_, lean_object* v_a_x3f_1847_){
_start:
{
lean_object* v___x_1849_; lean_object* v_infoState_1850_; lean_object* v_trees_1851_; lean_object* v___x_1852_; 
v___x_1849_ = lean_st_ref_get(v___y_1837_);
v_infoState_1850_ = lean_ctor_get(v___x_1849_, 7);
lean_inc_ref(v_infoState_1850_);
lean_dec(v___x_1849_);
v_trees_1851_ = lean_ctor_get(v_infoState_1850_, 2);
lean_inc_ref(v_trees_1851_);
lean_dec_ref(v_infoState_1850_);
lean_inc(v___y_1837_);
lean_inc_ref(v___y_1845_);
lean_inc(v___y_1844_);
lean_inc_ref(v___y_1843_);
lean_inc(v___y_1842_);
lean_inc_ref(v___y_1841_);
lean_inc(v___y_1840_);
lean_inc_ref(v___y_1839_);
v___x_1852_ = lean_apply_10(v_mkInfoTree_1838_, v_trees_1851_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1837_, lean_box(0));
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1891_; 
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1855_ = v___x_1852_;
v_isShared_1856_ = v_isSharedCheck_1891_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1852_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1891_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1857_; lean_object* v_infoState_1858_; lean_object* v_env_1859_; lean_object* v_nextMacroScope_1860_; lean_object* v_ngen_1861_; lean_object* v_auxDeclNGen_1862_; lean_object* v_traceState_1863_; lean_object* v_cache_1864_; lean_object* v_messages_1865_; lean_object* v_snapshotTasks_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1890_; 
v___x_1857_ = lean_st_ref_take(v___y_1837_);
v_infoState_1858_ = lean_ctor_get(v___x_1857_, 7);
v_env_1859_ = lean_ctor_get(v___x_1857_, 0);
v_nextMacroScope_1860_ = lean_ctor_get(v___x_1857_, 1);
v_ngen_1861_ = lean_ctor_get(v___x_1857_, 2);
v_auxDeclNGen_1862_ = lean_ctor_get(v___x_1857_, 3);
v_traceState_1863_ = lean_ctor_get(v___x_1857_, 4);
v_cache_1864_ = lean_ctor_get(v___x_1857_, 5);
v_messages_1865_ = lean_ctor_get(v___x_1857_, 6);
v_snapshotTasks_1866_ = lean_ctor_get(v___x_1857_, 8);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1868_ = v___x_1857_;
v_isShared_1869_ = v_isSharedCheck_1890_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_snapshotTasks_1866_);
lean_inc(v_infoState_1858_);
lean_inc(v_messages_1865_);
lean_inc(v_cache_1864_);
lean_inc(v_traceState_1863_);
lean_inc(v_auxDeclNGen_1862_);
lean_inc(v_ngen_1861_);
lean_inc(v_nextMacroScope_1860_);
lean_inc(v_env_1859_);
lean_dec(v___x_1857_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1890_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
uint8_t v_enabled_1870_; lean_object* v_assignment_1871_; lean_object* v_lazyAssignment_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1888_; 
v_enabled_1870_ = lean_ctor_get_uint8(v_infoState_1858_, sizeof(void*)*3);
v_assignment_1871_ = lean_ctor_get(v_infoState_1858_, 0);
v_lazyAssignment_1872_ = lean_ctor_get(v_infoState_1858_, 1);
v_isSharedCheck_1888_ = !lean_is_exclusive(v_infoState_1858_);
if (v_isSharedCheck_1888_ == 0)
{
lean_object* v_unused_1889_; 
v_unused_1889_ = lean_ctor_get(v_infoState_1858_, 2);
lean_dec(v_unused_1889_);
v___x_1874_ = v_infoState_1858_;
v_isShared_1875_ = v_isSharedCheck_1888_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_lazyAssignment_1872_);
lean_inc(v_assignment_1871_);
lean_dec(v_infoState_1858_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1888_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1876_; lean_object* v___x_1878_; 
v___x_1876_ = l_Lean_PersistentArray_push___redArg(v_a_1846_, v_a_1853_);
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 2, v___x_1876_);
v___x_1878_ = v___x_1874_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_assignment_1871_);
lean_ctor_set(v_reuseFailAlloc_1887_, 1, v_lazyAssignment_1872_);
lean_ctor_set(v_reuseFailAlloc_1887_, 2, v___x_1876_);
lean_ctor_set_uint8(v_reuseFailAlloc_1887_, sizeof(void*)*3, v_enabled_1870_);
v___x_1878_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
lean_object* v___x_1880_; 
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 7, v___x_1878_);
v___x_1880_ = v___x_1868_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_env_1859_);
lean_ctor_set(v_reuseFailAlloc_1886_, 1, v_nextMacroScope_1860_);
lean_ctor_set(v_reuseFailAlloc_1886_, 2, v_ngen_1861_);
lean_ctor_set(v_reuseFailAlloc_1886_, 3, v_auxDeclNGen_1862_);
lean_ctor_set(v_reuseFailAlloc_1886_, 4, v_traceState_1863_);
lean_ctor_set(v_reuseFailAlloc_1886_, 5, v_cache_1864_);
lean_ctor_set(v_reuseFailAlloc_1886_, 6, v_messages_1865_);
lean_ctor_set(v_reuseFailAlloc_1886_, 7, v___x_1878_);
lean_ctor_set(v_reuseFailAlloc_1886_, 8, v_snapshotTasks_1866_);
v___x_1880_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1884_; 
v___x_1881_ = lean_st_ref_put(v___y_1837_, v___x_1880_);
v___x_1882_ = lean_box(0);
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 0, v___x_1882_);
v___x_1884_ = v___x_1855_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1882_);
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
}
}
}
else
{
lean_object* v_a_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1899_; 
lean_dec_ref(v_a_1846_);
v_a_1892_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1894_ = v___x_1852_;
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_a_1892_);
lean_dec(v___x_1852_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1897_; 
if (v_isShared_1895_ == 0)
{
v___x_1897_ = v___x_1894_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_a_1892_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0___boxed(lean_object* v___y_1900_, lean_object* v_mkInfoTree_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v_a_1909_, lean_object* v_a_x3f_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0(v___y_1900_, v_mkInfoTree_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v_a_1909_, v_a_x3f_1910_);
lean_dec(v_a_x3f_1910_);
lean_dec_ref(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1900_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(lean_object* v_x_1913_, lean_object* v_mkInfoTree_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v___x_1924_; lean_object* v_infoState_1925_; uint8_t v_enabled_1926_; 
v___x_1924_ = lean_st_ref_get(v___y_1922_);
v_infoState_1925_ = lean_ctor_get(v___x_1924_, 7);
lean_inc_ref(v_infoState_1925_);
lean_dec(v___x_1924_);
v_enabled_1926_ = lean_ctor_get_uint8(v_infoState_1925_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1925_);
if (v_enabled_1926_ == 0)
{
lean_object* v___x_1927_; 
lean_dec_ref(v_mkInfoTree_1914_);
lean_inc(v___y_1922_);
lean_inc_ref(v___y_1921_);
lean_inc(v___y_1920_);
lean_inc_ref(v___y_1919_);
lean_inc(v___y_1918_);
lean_inc_ref(v___y_1917_);
lean_inc(v___y_1916_);
lean_inc_ref(v___y_1915_);
v___x_1927_ = lean_apply_9(v_x_1913_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, lean_box(0));
return v___x_1927_;
}
else
{
lean_object* v___x_1928_; lean_object* v_a_1929_; lean_object* v_r_1930_; 
v___x_1928_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___y_1922_);
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_a_1929_);
lean_dec_ref(v___x_1928_);
lean_inc(v___y_1922_);
lean_inc_ref(v___y_1921_);
lean_inc(v___y_1920_);
lean_inc_ref(v___y_1919_);
lean_inc(v___y_1918_);
lean_inc_ref(v___y_1917_);
lean_inc(v___y_1916_);
lean_inc_ref(v___y_1915_);
v_r_1930_ = lean_apply_9(v_x_1913_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, lean_box(0));
if (lean_obj_tag(v_r_1930_) == 0)
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1955_; 
v_a_1931_ = lean_ctor_get(v_r_1930_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v_r_1930_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1933_ = v_r_1930_;
v_isShared_1934_ = v_isSharedCheck_1955_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v_r_1930_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1955_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
lean_inc(v_a_1931_);
if (v_isShared_1934_ == 0)
{
lean_ctor_set_tag(v___x_1933_, 1);
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1931_);
v___x_1936_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
lean_object* v___x_1937_; 
v___x_1937_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0(v___y_1922_, v_mkInfoTree_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v_a_1929_, v___x_1936_);
lean_dec_ref(v___x_1936_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1944_ == 0)
{
lean_object* v_unused_1945_; 
v_unused_1945_ = lean_ctor_get(v___x_1937_, 0);
lean_dec(v_unused_1945_);
v___x_1939_ = v___x_1937_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_dec(v___x_1937_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 0, v_a_1931_);
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1931_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
else
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
lean_dec(v_a_1931_);
v_a_1946_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1948_ = v___x_1937_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1937_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1946_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
}
}
}
else
{
lean_object* v_a_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v_a_1956_ = lean_ctor_get(v_r_1930_, 0);
lean_inc(v_a_1956_);
lean_dec_ref_known(v_r_1930_, 1);
v___x_1957_ = lean_box(0);
v___x_1958_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0(v___y_1922_, v_mkInfoTree_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v_a_1929_, v___x_1957_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1965_ == 0)
{
lean_object* v_unused_1966_; 
v_unused_1966_ = lean_ctor_get(v___x_1958_, 0);
lean_dec(v_unused_1966_);
v___x_1960_ = v___x_1958_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_dec(v___x_1958_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
lean_ctor_set_tag(v___x_1960_, 1);
lean_ctor_set(v___x_1960_, 0, v_a_1956_);
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_a_1956_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
else
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1974_; 
lean_dec(v_a_1956_);
v_a_1967_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1969_ = v___x_1958_;
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1958_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_a_1967_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___boxed(lean_object* v_x_1975_, lean_object* v_mkInfoTree_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v_x_1975_, v_mkInfoTree_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(lean_object* v_msg_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
lean_object* v_ref_1993_; lean_object* v___x_1994_; lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2003_; 
v_ref_1993_ = lean_ctor_get(v___y_1990_, 4);
v___x_1994_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__2(v_msg_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1997_ = v___x_1994_;
v_isShared_1998_ = v_isSharedCheck_2003_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1994_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2003_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_1999_; lean_object* v___x_2001_; 
lean_inc(v_ref_1993_);
v___x_1999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1999_, 0, v_ref_1993_);
lean_ctor_set(v___x_1999_, 1, v_a_1995_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set_tag(v___x_1997_, 1);
lean_ctor_set(v___x_1997_, 0, v___x_1999_);
v___x_2001_ = v___x_1997_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1999_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg___boxed(lean_object* v_msg_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_msg_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__19_spec__21___redArg(lean_object* v_x_2011_, lean_object* v_x_2012_, lean_object* v_x_2013_, lean_object* v_x_2014_){
_start:
{
lean_object* v_ks_2015_; lean_object* v_vs_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2040_; 
v_ks_2015_ = lean_ctor_get(v_x_2011_, 0);
v_vs_2016_ = lean_ctor_get(v_x_2011_, 1);
v_isSharedCheck_2040_ = !lean_is_exclusive(v_x_2011_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2018_ = v_x_2011_;
v_isShared_2019_ = v_isSharedCheck_2040_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_vs_2016_);
lean_inc(v_ks_2015_);
lean_dec(v_x_2011_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2040_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2020_; uint8_t v___x_2021_; 
v___x_2020_ = lean_array_get_size(v_ks_2015_);
v___x_2021_ = lean_nat_dec_lt(v_x_2012_, v___x_2020_);
if (v___x_2021_ == 0)
{
lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2025_; 
lean_dec(v_x_2012_);
v___x_2022_ = lean_array_push(v_ks_2015_, v_x_2013_);
v___x_2023_ = lean_array_push(v_vs_2016_, v_x_2014_);
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 1, v___x_2023_);
lean_ctor_set(v___x_2018_, 0, v___x_2022_);
v___x_2025_ = v___x_2018_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2022_);
lean_ctor_set(v_reuseFailAlloc_2026_, 1, v___x_2023_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
else
{
lean_object* v_k_x27_2027_; uint8_t v___x_2028_; 
v_k_x27_2027_ = lean_array_fget_borrowed(v_ks_2015_, v_x_2012_);
v___x_2028_ = l_Lean_instBEqMVarId_beq(v_x_2013_, v_k_x27_2027_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2030_; 
if (v_isShared_2019_ == 0)
{
v___x_2030_ = v___x_2018_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_ks_2015_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v_vs_2016_);
v___x_2030_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2031_ = lean_unsigned_to_nat(1u);
v___x_2032_ = lean_nat_add(v_x_2012_, v___x_2031_);
lean_dec(v_x_2012_);
v_x_2011_ = v___x_2030_;
v_x_2012_ = v___x_2032_;
goto _start;
}
}
else
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2038_; 
v___x_2035_ = lean_array_fset(v_ks_2015_, v_x_2012_, v_x_2013_);
v___x_2036_ = lean_array_fset(v_vs_2016_, v_x_2012_, v_x_2014_);
lean_dec(v_x_2012_);
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 1, v___x_2036_);
lean_ctor_set(v___x_2018_, 0, v___x_2035_);
v___x_2038_ = v___x_2018_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v___x_2035_);
lean_ctor_set(v_reuseFailAlloc_2039_, 1, v___x_2036_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__19___redArg(lean_object* v_n_2041_, lean_object* v_k_2042_, lean_object* v_v_2043_){
_start:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2044_ = lean_unsigned_to_nat(0u);
v___x_2045_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__19_spec__21___redArg(v_n_2041_, v___x_2044_, v_k_2042_, v_v_2043_);
return v___x_2045_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_2046_; 
v___x_2046_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___redArg(lean_object* v_x_2047_, size_t v_x_2048_, size_t v_x_2049_, lean_object* v_x_2050_, lean_object* v_x_2051_){
_start:
{
if (lean_obj_tag(v_x_2047_) == 0)
{
lean_object* v_es_2052_; size_t v___x_2053_; size_t v___x_2054_; lean_object* v_j_2055_; lean_object* v___x_2056_; uint8_t v___x_2057_; 
v_es_2052_ = lean_ctor_get(v_x_2047_, 0);
v___x_2053_ = ((size_t)31ULL);
v___x_2054_ = lean_usize_land(v_x_2048_, v___x_2053_);
v_j_2055_ = lean_usize_to_nat(v___x_2054_);
v___x_2056_ = lean_array_get_size(v_es_2052_);
v___x_2057_ = lean_nat_dec_lt(v_j_2055_, v___x_2056_);
if (v___x_2057_ == 0)
{
lean_dec(v_j_2055_);
lean_dec(v_x_2051_);
lean_dec(v_x_2050_);
return v_x_2047_;
}
else
{
lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2096_; 
lean_inc_ref(v_es_2052_);
v_isSharedCheck_2096_ = !lean_is_exclusive(v_x_2047_);
if (v_isSharedCheck_2096_ == 0)
{
lean_object* v_unused_2097_; 
v_unused_2097_ = lean_ctor_get(v_x_2047_, 0);
lean_dec(v_unused_2097_);
v___x_2059_ = v_x_2047_;
v_isShared_2060_ = v_isSharedCheck_2096_;
goto v_resetjp_2058_;
}
else
{
lean_dec(v_x_2047_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2096_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v_v_2061_; lean_object* v___x_2062_; lean_object* v_xs_x27_2063_; lean_object* v___y_2065_; 
v_v_2061_ = lean_array_fget(v_es_2052_, v_j_2055_);
v___x_2062_ = lean_box(0);
v_xs_x27_2063_ = lean_array_fset(v_es_2052_, v_j_2055_, v___x_2062_);
switch(lean_obj_tag(v_v_2061_))
{
case 0:
{
lean_object* v_key_2070_; lean_object* v_val_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2081_; 
v_key_2070_ = lean_ctor_get(v_v_2061_, 0);
v_val_2071_ = lean_ctor_get(v_v_2061_, 1);
v_isSharedCheck_2081_ = !lean_is_exclusive(v_v_2061_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2073_ = v_v_2061_;
v_isShared_2074_ = v_isSharedCheck_2081_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_val_2071_);
lean_inc(v_key_2070_);
lean_dec(v_v_2061_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2081_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
uint8_t v___x_2075_; 
v___x_2075_ = l_Lean_instBEqMVarId_beq(v_x_2050_, v_key_2070_);
if (v___x_2075_ == 0)
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
lean_del_object(v___x_2073_);
v___x_2076_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2070_, v_val_2071_, v_x_2050_, v_x_2051_);
v___x_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2076_);
v___y_2065_ = v___x_2077_;
goto v___jp_2064_;
}
else
{
lean_object* v___x_2079_; 
lean_dec(v_val_2071_);
lean_dec(v_key_2070_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 1, v_x_2051_);
lean_ctor_set(v___x_2073_, 0, v_x_2050_);
v___x_2079_ = v___x_2073_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_x_2050_);
lean_ctor_set(v_reuseFailAlloc_2080_, 1, v_x_2051_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
v___y_2065_ = v___x_2079_;
goto v___jp_2064_;
}
}
}
}
case 1:
{
lean_object* v_node_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2094_; 
v_node_2082_ = lean_ctor_get(v_v_2061_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v_v_2061_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2084_ = v_v_2061_;
v_isShared_2085_ = v_isSharedCheck_2094_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_node_2082_);
lean_dec(v_v_2061_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2094_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
size_t v___x_2086_; size_t v___x_2087_; size_t v___x_2088_; size_t v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2092_; 
v___x_2086_ = ((size_t)5ULL);
v___x_2087_ = lean_usize_shift_right(v_x_2048_, v___x_2086_);
v___x_2088_ = ((size_t)1ULL);
v___x_2089_ = lean_usize_add(v_x_2049_, v___x_2088_);
v___x_2090_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___redArg(v_node_2082_, v___x_2087_, v___x_2089_, v_x_2050_, v_x_2051_);
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 0, v___x_2090_);
v___x_2092_ = v___x_2084_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v___x_2090_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
v___y_2065_ = v___x_2092_;
goto v___jp_2064_;
}
}
}
default: 
{
lean_object* v___x_2095_; 
v___x_2095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2095_, 0, v_x_2050_);
lean_ctor_set(v___x_2095_, 1, v_x_2051_);
v___y_2065_ = v___x_2095_;
goto v___jp_2064_;
}
}
v___jp_2064_:
{
lean_object* v___x_2066_; lean_object* v___x_2068_; 
v___x_2066_ = lean_array_fset(v_xs_x27_2063_, v_j_2055_, v___y_2065_);
lean_dec(v_j_2055_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 0, v___x_2066_);
v___x_2068_ = v___x_2059_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2066_);
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
}
else
{
lean_object* v_ks_2098_; lean_object* v_vs_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2117_; 
v_ks_2098_ = lean_ctor_get(v_x_2047_, 0);
v_vs_2099_ = lean_ctor_get(v_x_2047_, 1);
v_isSharedCheck_2117_ = !lean_is_exclusive(v_x_2047_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2101_ = v_x_2047_;
v_isShared_2102_ = v_isSharedCheck_2117_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_vs_2099_);
lean_inc(v_ks_2098_);
lean_dec(v_x_2047_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2117_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_ks_2098_);
lean_ctor_set(v_reuseFailAlloc_2116_, 1, v_vs_2099_);
v___x_2104_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
lean_object* v_newNode_2105_; size_t v___x_2106_; uint8_t v___x_2107_; 
v_newNode_2105_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__19___redArg(v___x_2104_, v_x_2050_, v_x_2051_);
v___x_2106_ = ((size_t)7ULL);
v___x_2107_ = lean_usize_dec_le(v___x_2106_, v_x_2049_);
if (v___x_2107_ == 0)
{
lean_object* v___x_2108_; lean_object* v___x_2109_; uint8_t v___x_2110_; 
v___x_2108_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2105_);
v___x_2109_ = lean_unsigned_to_nat(4u);
v___x_2110_ = lean_nat_dec_lt(v___x_2108_, v___x_2109_);
lean_dec(v___x_2108_);
if (v___x_2110_ == 0)
{
lean_object* v_ks_2111_; lean_object* v_vs_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v_ks_2111_ = lean_ctor_get(v_newNode_2105_, 0);
lean_inc_ref(v_ks_2111_);
v_vs_2112_ = lean_ctor_get(v_newNode_2105_, 1);
lean_inc_ref(v_vs_2112_);
lean_dec_ref(v_newNode_2105_);
v___x_2113_ = lean_unsigned_to_nat(0u);
v___x_2114_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___redArg___closed__0);
v___x_2115_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__20___redArg(v_x_2049_, v_ks_2111_, v_vs_2112_, v___x_2113_, v___x_2114_);
lean_dec_ref(v_vs_2112_);
lean_dec_ref(v_ks_2111_);
return v___x_2115_;
}
else
{
return v_newNode_2105_;
}
}
else
{
return v_newNode_2105_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__20___redArg(size_t v_depth_2118_, lean_object* v_keys_2119_, lean_object* v_vals_2120_, lean_object* v_i_2121_, lean_object* v_entries_2122_){
_start:
{
lean_object* v___x_2123_; uint8_t v___x_2124_; 
v___x_2123_ = lean_array_get_size(v_keys_2119_);
v___x_2124_ = lean_nat_dec_lt(v_i_2121_, v___x_2123_);
if (v___x_2124_ == 0)
{
lean_dec(v_i_2121_);
return v_entries_2122_;
}
else
{
lean_object* v_k_2125_; lean_object* v_v_2126_; uint64_t v___x_2127_; size_t v_h_2128_; size_t v___x_2129_; lean_object* v___x_2130_; size_t v___x_2131_; size_t v___x_2132_; size_t v___x_2133_; size_t v_h_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v_k_2125_ = lean_array_fget_borrowed(v_keys_2119_, v_i_2121_);
v_v_2126_ = lean_array_fget_borrowed(v_vals_2120_, v_i_2121_);
v___x_2127_ = l_Lean_instHashableMVarId_hash(v_k_2125_);
v_h_2128_ = lean_uint64_to_usize(v___x_2127_);
v___x_2129_ = ((size_t)5ULL);
v___x_2130_ = lean_unsigned_to_nat(1u);
v___x_2131_ = ((size_t)1ULL);
v___x_2132_ = lean_usize_sub(v_depth_2118_, v___x_2131_);
v___x_2133_ = lean_usize_mul(v___x_2129_, v___x_2132_);
v_h_2134_ = lean_usize_shift_right(v_h_2128_, v___x_2133_);
v___x_2135_ = lean_nat_add(v_i_2121_, v___x_2130_);
lean_dec(v_i_2121_);
lean_inc(v_v_2126_);
lean_inc(v_k_2125_);
v___x_2136_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___redArg(v_entries_2122_, v_h_2134_, v_depth_2118_, v_k_2125_, v_v_2126_);
v_i_2121_ = v___x_2135_;
v_entries_2122_ = v___x_2136_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__20___redArg___boxed(lean_object* v_depth_2138_, lean_object* v_keys_2139_, lean_object* v_vals_2140_, lean_object* v_i_2141_, lean_object* v_entries_2142_){
_start:
{
size_t v_depth_boxed_2143_; lean_object* v_res_2144_; 
v_depth_boxed_2143_ = lean_unbox_usize(v_depth_2138_);
lean_dec(v_depth_2138_);
v_res_2144_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__20___redArg(v_depth_boxed_2143_, v_keys_2139_, v_vals_2140_, v_i_2141_, v_entries_2142_);
lean_dec_ref(v_vals_2140_);
lean_dec_ref(v_keys_2139_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___redArg___boxed(lean_object* v_x_2145_, lean_object* v_x_2146_, lean_object* v_x_2147_, lean_object* v_x_2148_, lean_object* v_x_2149_){
_start:
{
size_t v_x_95154__boxed_2150_; size_t v_x_95155__boxed_2151_; lean_object* v_res_2152_; 
v_x_95154__boxed_2150_ = lean_unbox_usize(v_x_2146_);
lean_dec(v_x_2146_);
v_x_95155__boxed_2151_ = lean_unbox_usize(v_x_2147_);
lean_dec(v_x_2147_);
v_res_2152_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___redArg(v_x_2145_, v_x_95154__boxed_2150_, v_x_95155__boxed_2151_, v_x_2148_, v_x_2149_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(lean_object* v_x_2153_, lean_object* v_x_2154_, lean_object* v_x_2155_){
_start:
{
uint64_t v___x_2156_; size_t v___x_2157_; size_t v___x_2158_; lean_object* v___x_2159_; 
v___x_2156_ = l_Lean_instHashableMVarId_hash(v_x_2154_);
v___x_2157_ = lean_uint64_to_usize(v___x_2156_);
v___x_2158_ = ((size_t)1ULL);
v___x_2159_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___redArg(v_x_2153_, v___x_2157_, v___x_2158_, v_x_2154_, v_x_2155_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(lean_object* v_mvarId_2160_, lean_object* v_val_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v___x_2164_; lean_object* v_mctx_2165_; lean_object* v_cache_2166_; lean_object* v_zetaDeltaFVarIds_2167_; lean_object* v_postponed_2168_; lean_object* v_diag_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2198_; 
v___x_2164_ = lean_st_ref_take(v___y_2162_);
v_mctx_2165_ = lean_ctor_get(v___x_2164_, 0);
v_cache_2166_ = lean_ctor_get(v___x_2164_, 1);
v_zetaDeltaFVarIds_2167_ = lean_ctor_get(v___x_2164_, 2);
v_postponed_2168_ = lean_ctor_get(v___x_2164_, 3);
v_diag_2169_ = lean_ctor_get(v___x_2164_, 4);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2171_ = v___x_2164_;
v_isShared_2172_ = v_isSharedCheck_2198_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_diag_2169_);
lean_inc(v_postponed_2168_);
lean_inc(v_zetaDeltaFVarIds_2167_);
lean_inc(v_cache_2166_);
lean_inc(v_mctx_2165_);
lean_dec(v___x_2164_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2198_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v_depth_2173_; lean_object* v_levelAssignDepth_2174_; lean_object* v_lmvarCounter_2175_; lean_object* v_mvarCounter_2176_; lean_object* v_lDecls_2177_; lean_object* v_decls_2178_; lean_object* v_userNames_2179_; lean_object* v_lAssignment_2180_; lean_object* v_eAssignment_2181_; lean_object* v_dAssignment_2182_; lean_object* v_instanceTypedMVars_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2197_; 
v_depth_2173_ = lean_ctor_get(v_mctx_2165_, 0);
v_levelAssignDepth_2174_ = lean_ctor_get(v_mctx_2165_, 1);
v_lmvarCounter_2175_ = lean_ctor_get(v_mctx_2165_, 2);
v_mvarCounter_2176_ = lean_ctor_get(v_mctx_2165_, 3);
v_lDecls_2177_ = lean_ctor_get(v_mctx_2165_, 4);
v_decls_2178_ = lean_ctor_get(v_mctx_2165_, 5);
v_userNames_2179_ = lean_ctor_get(v_mctx_2165_, 6);
v_lAssignment_2180_ = lean_ctor_get(v_mctx_2165_, 7);
v_eAssignment_2181_ = lean_ctor_get(v_mctx_2165_, 8);
v_dAssignment_2182_ = lean_ctor_get(v_mctx_2165_, 9);
v_instanceTypedMVars_2183_ = lean_ctor_get(v_mctx_2165_, 10);
v_isSharedCheck_2197_ = !lean_is_exclusive(v_mctx_2165_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2185_ = v_mctx_2165_;
v_isShared_2186_ = v_isSharedCheck_2197_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_instanceTypedMVars_2183_);
lean_inc(v_dAssignment_2182_);
lean_inc(v_eAssignment_2181_);
lean_inc(v_lAssignment_2180_);
lean_inc(v_userNames_2179_);
lean_inc(v_decls_2178_);
lean_inc(v_lDecls_2177_);
lean_inc(v_mvarCounter_2176_);
lean_inc(v_lmvarCounter_2175_);
lean_inc(v_levelAssignDepth_2174_);
lean_inc(v_depth_2173_);
lean_dec(v_mctx_2165_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2197_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2187_; lean_object* v___x_2189_; 
v___x_2187_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(v_eAssignment_2181_, v_mvarId_2160_, v_val_2161_);
if (v_isShared_2186_ == 0)
{
lean_ctor_set(v___x_2185_, 8, v___x_2187_);
v___x_2189_ = v___x_2185_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_depth_2173_);
lean_ctor_set(v_reuseFailAlloc_2196_, 1, v_levelAssignDepth_2174_);
lean_ctor_set(v_reuseFailAlloc_2196_, 2, v_lmvarCounter_2175_);
lean_ctor_set(v_reuseFailAlloc_2196_, 3, v_mvarCounter_2176_);
lean_ctor_set(v_reuseFailAlloc_2196_, 4, v_lDecls_2177_);
lean_ctor_set(v_reuseFailAlloc_2196_, 5, v_decls_2178_);
lean_ctor_set(v_reuseFailAlloc_2196_, 6, v_userNames_2179_);
lean_ctor_set(v_reuseFailAlloc_2196_, 7, v_lAssignment_2180_);
lean_ctor_set(v_reuseFailAlloc_2196_, 8, v___x_2187_);
lean_ctor_set(v_reuseFailAlloc_2196_, 9, v_dAssignment_2182_);
lean_ctor_set(v_reuseFailAlloc_2196_, 10, v_instanceTypedMVars_2183_);
v___x_2189_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
lean_object* v___x_2191_; 
if (v_isShared_2172_ == 0)
{
lean_ctor_set(v___x_2171_, 0, v___x_2189_);
v___x_2191_ = v___x_2171_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2189_);
lean_ctor_set(v_reuseFailAlloc_2195_, 1, v_cache_2166_);
lean_ctor_set(v_reuseFailAlloc_2195_, 2, v_zetaDeltaFVarIds_2167_);
lean_ctor_set(v_reuseFailAlloc_2195_, 3, v_postponed_2168_);
lean_ctor_set(v_reuseFailAlloc_2195_, 4, v_diag_2169_);
v___x_2191_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2192_ = lean_st_ref_put(v___y_2162_, v___x_2191_);
v___x_2193_ = lean_box(0);
v___x_2194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2193_);
return v___x_2194_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg___boxed(lean_object* v_mvarId_2199_, lean_object* v_val_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(v_mvarId_2199_, v_val_2200_, v___y_2201_);
lean_dec(v___y_2201_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(lean_object* v_o_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v___x_2207_; lean_object* v_env_2208_; lean_object* v___x_2209_; lean_object* v_toEnvExtension_2210_; lean_object* v_asyncMode_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v_merged_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2223_; 
v___x_2207_ = lean_st_ref_get(v___y_2205_);
v_env_2208_ = lean_ctor_get(v___x_2207_, 0);
lean_inc_ref(v_env_2208_);
lean_dec(v___x_2207_);
v___x_2209_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_2210_ = lean_ctor_get(v___x_2209_, 0);
v_asyncMode_2211_ = lean_ctor_get(v_toEnvExtension_2210_, 2);
v___x_2212_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_2213_ = lean_box(0);
v___x_2214_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2212_, v___x_2209_, v_env_2208_, v_asyncMode_2211_, v___x_2213_);
v_merged_2215_ = lean_ctor_get(v___x_2214_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2214_);
if (v_isSharedCheck_2223_ == 0)
{
lean_object* v_unused_2224_; 
v_unused_2224_ = lean_ctor_get(v___x_2214_, 1);
lean_dec(v_unused_2224_);
v___x_2217_ = v___x_2214_;
v_isShared_2218_ = v_isSharedCheck_2223_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_merged_2215_);
lean_dec(v___x_2214_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2223_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2220_; 
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 1, v_merged_2215_);
lean_ctor_set(v___x_2217_, 0, v_o_2204_);
v___x_2220_ = v___x_2217_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_o_2204_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v_merged_2215_);
v___x_2220_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
lean_object* v___x_2221_; 
v___x_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
return v___x_2221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg___boxed(lean_object* v_o_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(v_o_2225_, v___y_2226_);
lean_dec(v___y_2226_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
lean_object* v_options_2238_; lean_object* v___x_2239_; 
v_options_2238_ = lean_ctor_get(v___y_2235_, 1);
lean_inc_ref(v_options_2238_);
v___x_2239_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(v_options_2238_, v___y_2236_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___boxed(lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v_res_2249_; 
v_res_2249_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
return v_res_2249_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__6(void){
_start:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2257_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5));
v___x_2258_ = l_Lean_stringToMessageData(v___x_2257_);
return v___x_2258_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__8(void){
_start:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2260_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__7));
v___x_2261_ = l_Lean_stringToMessageData(v___x_2260_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5(lean_object* v_usingArg_2265_, lean_object* v_snd_2266_, uint8_t v___x_2267_, uint8_t v___x_2268_, lean_object* v___x_2269_, uint8_t v_useReducible_2270_, uint8_t v___x_2271_, lean_object* v___x_2272_, lean_object* v___x_2273_, lean_object* v_simprocs_2274_, lean_object* v_discharge_x3f_2275_, lean_object* v_snd_2276_, lean_object* v___f_2277_, lean_object* v___x_2278_, lean_object* v___x_2279_, lean_object* v___x_2280_, lean_object* v___x_2281_, lean_object* v___f_2282_, lean_object* v_a_2283_, lean_object* v___x_2284_, lean_object* v___f_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
lean_object* v___y_2296_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2309_; lean_object* v___y_2310_; lean_object* v___y_2311_; lean_object* v___y_2312_; lean_object* v___y_2313_; lean_object* v___y_2314_; lean_object* v___y_2315_; lean_object* v___y_2316_; lean_object* v___y_2317_; lean_object* v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___y_2322_; lean_object* v___y_2323_; lean_object* v___y_2324_; lean_object* v___y_2360_; lean_object* v___y_2361_; lean_object* v___y_2362_; lean_object* v___y_2363_; lean_object* v___y_2364_; lean_object* v___y_2365_; lean_object* v___y_2366_; lean_object* v___y_2367_; lean_object* v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; 
if (lean_obj_tag(v_usingArg_2265_) == 1)
{
lean_object* v_val_2509_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v___y_2514_; lean_object* v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___x_2561_; lean_object* v_infoState_2562_; uint8_t v_enabled_2563_; 
v_val_2509_ = lean_ctor_get(v_usingArg_2265_, 0);
lean_inc(v_val_2509_);
lean_dec_ref_known(v_usingArg_2265_, 1);
v___x_2561_ = lean_st_ref_get(v___y_2293_);
v_infoState_2562_ = lean_ctor_get(v___x_2561_, 7);
lean_inc_ref(v_infoState_2562_);
lean_dec(v___x_2561_);
v_enabled_2563_ = lean_ctor_get_uint8(v_infoState_2562_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2562_);
if (v_enabled_2563_ == 0)
{
lean_dec_ref(v___f_2285_);
v___y_2511_ = v___y_2286_;
v___y_2512_ = v___y_2287_;
v___y_2513_ = v___y_2288_;
v___y_2514_ = v___y_2289_;
v___y_2515_ = v___y_2290_;
v___y_2516_ = v___y_2291_;
v___y_2517_ = v___y_2292_;
v___y_2518_ = v___y_2293_;
goto v___jp_2510_;
}
else
{
lean_object* v___x_2564_; lean_object* v_a_2565_; lean_object* v___f_2566_; lean_object* v___x_2567_; 
v___x_2564_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___y_2293_);
v_a_2565_ = lean_ctor_get(v___x_2564_, 0);
lean_inc(v_a_2565_);
lean_dec_ref(v___x_2564_);
v___f_2566_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___boxed), 10, 1);
lean_closure_set(v___f_2566_, 0, v_a_2565_);
v___x_2567_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v___f_2566_, v___f_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_dec_ref_known(v___x_2567_, 1);
v___y_2511_ = v___y_2286_;
v___y_2512_ = v___y_2287_;
v___y_2513_ = v___y_2288_;
v___y_2514_ = v___y_2289_;
v___y_2515_ = v___y_2290_;
v___y_2516_ = v___y_2291_;
v___y_2517_ = v___y_2292_;
v___y_2518_ = v___y_2293_;
goto v___jp_2510_;
}
else
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2575_; 
lean_dec(v_val_2509_);
lean_dec_ref(v_a_2283_);
lean_dec_ref(v___f_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2280_);
lean_dec_ref(v___x_2279_);
lean_dec(v___x_2278_);
lean_dec_ref(v___f_2277_);
lean_dec_ref(v_snd_2276_);
lean_dec(v_discharge_x3f_2275_);
lean_dec_ref(v_simprocs_2274_);
lean_dec_ref(v___x_2273_);
lean_dec_ref(v___x_2269_);
lean_dec(v_snd_2266_);
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
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2519_ = lean_st_ref_get(v___y_2516_);
v___x_2520_ = lean_box(0);
v___x_2521_ = l_Lean_Elab_Tactic_elabTerm(v_val_2509_, v___x_2520_, v___x_2267_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_object* v_a_2522_; lean_object* v___x_2523_; 
v_a_2522_ = lean_ctor_get(v___x_2521_, 0);
lean_inc_n(v_a_2522_, 2);
lean_dec_ref_known(v___x_2521_, 1);
v___x_2523_ = l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(v_snd_2266_, v_a_2522_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_mctx_2524_; lean_object* v_a_2525_; uint8_t v___x_2526_; 
v_mctx_2524_ = lean_ctor_get(v___x_2519_, 0);
lean_inc_ref(v_mctx_2524_);
lean_dec(v___x_2519_);
v_a_2525_ = lean_ctor_get(v___x_2523_, 0);
lean_inc(v_a_2525_);
lean_dec_ref_known(v___x_2523_, 1);
v___x_2526_ = lean_unbox(v_a_2525_);
lean_dec(v_a_2525_);
if (v___x_2526_ == 0)
{
lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
lean_dec_ref(v_mctx_2524_);
lean_dec_ref(v_a_2283_);
lean_dec_ref(v___f_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2280_);
lean_dec_ref(v___x_2279_);
lean_dec(v___x_2278_);
lean_dec_ref(v___f_2277_);
lean_dec_ref(v_snd_2276_);
lean_dec(v_discharge_x3f_2275_);
lean_dec_ref(v_simprocs_2274_);
lean_dec_ref(v___x_2273_);
lean_dec_ref(v___x_2269_);
v___x_2527_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__6);
v___x_2528_ = l_Lean_indentExpr(v_a_2522_);
v___x_2529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2527_);
lean_ctor_set(v___x_2529_, 1, v___x_2528_);
v___x_2530_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__8, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__8_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__8);
v___x_2531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2531_, 0, v___x_2529_);
lean_ctor_set(v___x_2531_, 1, v___x_2530_);
v___x_2532_ = l_Lean_Expr_mvar___override(v_snd_2266_);
v___x_2533_ = l_Lean_MessageData_ofExpr(v___x_2532_);
v___x_2534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2534_, 0, v___x_2531_);
lean_ctor_set(v___x_2534_, 1, v___x_2533_);
v___x_2535_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v___x_2534_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
v_a_2536_ = lean_ctor_get(v___x_2535_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2538_ = v___x_2535_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2535_);
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
else
{
lean_object* v_mvarCounter_2544_; 
v_mvarCounter_2544_ = lean_ctor_get(v_mctx_2524_, 3);
lean_inc(v_mvarCounter_2544_);
lean_dec_ref(v_mctx_2524_);
lean_inc(v_a_2522_);
v___y_2360_ = v_a_2522_;
v___y_2361_ = v___x_2520_;
v___y_2362_ = v_mvarCounter_2544_;
v___y_2363_ = v_a_2522_;
v___y_2364_ = v___x_2520_;
v___y_2365_ = v___y_2511_;
v___y_2366_ = v___y_2512_;
v___y_2367_ = v___y_2513_;
v___y_2368_ = v___y_2514_;
v___y_2369_ = v___y_2515_;
v___y_2370_ = v___y_2516_;
v___y_2371_ = v___y_2517_;
v___y_2372_ = v___y_2518_;
goto v___jp_2359_;
}
}
else
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2552_; 
lean_dec(v_a_2522_);
lean_dec(v___x_2519_);
lean_dec_ref(v_a_2283_);
lean_dec_ref(v___f_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2280_);
lean_dec_ref(v___x_2279_);
lean_dec(v___x_2278_);
lean_dec_ref(v___f_2277_);
lean_dec_ref(v_snd_2276_);
lean_dec(v_discharge_x3f_2275_);
lean_dec_ref(v_simprocs_2274_);
lean_dec_ref(v___x_2273_);
lean_dec_ref(v___x_2269_);
lean_dec(v_snd_2266_);
v_a_2545_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2547_ = v___x_2523_;
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2523_);
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
lean_dec(v___x_2519_);
lean_dec_ref(v_a_2283_);
lean_dec_ref(v___f_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2280_);
lean_dec_ref(v___x_2279_);
lean_dec(v___x_2278_);
lean_dec_ref(v___f_2277_);
lean_dec_ref(v_snd_2276_);
lean_dec(v_discharge_x3f_2275_);
lean_dec_ref(v_simprocs_2274_);
lean_dec_ref(v___x_2273_);
lean_dec_ref(v___x_2269_);
lean_dec(v_snd_2266_);
v_a_2553_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2555_ = v___x_2521_;
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2521_);
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
lean_dec_ref(v___f_2285_);
lean_dec_ref(v_a_2283_);
lean_dec_ref(v___f_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2280_);
lean_dec_ref(v___x_2279_);
lean_dec(v___x_2278_);
lean_dec_ref(v___f_2277_);
lean_dec_ref(v___x_2269_);
lean_dec(v_usingArg_2265_);
v_lctx_2576_ = lean_ctor_get(v___y_2290_, 2);
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
v___x_2581_ = lean_mk_empty_array_with_capacity(v___x_2272_);
v___x_2582_ = lean_array_push(v___x_2581_, v___x_2580_);
lean_inc_ref(v_snd_2276_);
v___x_2583_ = l_Lean_Meta_simpGoal(v_snd_2266_, v___x_2273_, v_simprocs_2274_, v_discharge_x3f_2275_, v___x_2268_, v___x_2582_, v_snd_2276_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
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
lean_dec_ref(v_snd_2276_);
v_val_2589_ = lean_ctor_get(v_fst_2588_, 0);
lean_inc(v_val_2589_);
v_snd_2590_ = lean_ctor_get(v_a_2584_, 1);
lean_inc(v_snd_2590_);
lean_dec(v_a_2584_);
v_snd_2591_ = lean_ctor_get(v_val_2589_, 1);
lean_inc(v_snd_2591_);
lean_dec(v_val_2589_);
v___x_2592_ = l_Lean_MVarId_assumption(v_snd_2591_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
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
lean_ctor_set(v___x_2586_, 0, v_snd_2276_);
v___x_2610_ = v___x_2586_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_snd_2276_);
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
lean_dec_ref(v_snd_2276_);
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
lean_dec(v_discharge_x3f_2275_);
lean_dec_ref(v_simprocs_2274_);
lean_dec_ref(v___x_2273_);
v___x_2621_ = l_Lean_MVarId_assumption(v_snd_2266_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
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
lean_ctor_set(v___x_2623_, 0, v_snd_2276_);
v___x_2626_ = v___x_2623_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_snd_2276_);
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
lean_dec_ref(v_snd_2276_);
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
v___jp_2295_:
{
lean_object* v___x_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2306_; 
v___x_2299_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(v_snd_2266_, v___y_2296_, v___y_2298_);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2306_ == 0)
{
lean_object* v_unused_2307_; 
v_unused_2307_ = lean_ctor_get(v___x_2299_, 0);
lean_dec(v_unused_2307_);
v___x_2301_ = v___x_2299_;
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
else
{
lean_dec(v___x_2299_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 0, v___y_2297_);
v___x_2304_ = v___x_2301_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v___y_2297_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
v___jp_2308_:
{
lean_object* v___x_2325_; 
v___x_2325_ = l_Lean_Core_mkFreshUserName(v___y_2313_, v___y_2314_, v___y_2322_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; lean_object* v___x_2327_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
lean_inc_n(v_a_2326_, 2);
lean_dec_ref_known(v___x_2325_, 1);
v___x_2327_ = l_Lean_MVarId_rename(v___y_2323_, v___y_2324_, v_a_2326_, v___y_2316_, v___y_2312_, v___y_2314_, v___y_2322_);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v_a_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___f_2333_; lean_object* v___x_2334_; 
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
lean_inc_n(v_a_2328_, 2);
lean_dec_ref_known(v___x_2327_, 1);
v___x_2329_ = lean_box(v___x_2267_);
v___x_2330_ = lean_box(v___x_2268_);
v___x_2331_ = lean_box(v_useReducible_2270_);
v___x_2332_ = lean_box(v___x_2271_);
v___f_2333_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___boxed), 19, 10);
lean_closure_set(v___f_2333_, 0, v_a_2328_);
lean_closure_set(v___f_2333_, 1, v_a_2326_);
lean_closure_set(v___f_2333_, 2, v___x_2329_);
lean_closure_set(v___f_2333_, 3, v___x_2330_);
lean_closure_set(v___f_2333_, 4, v___y_2309_);
lean_closure_set(v___f_2333_, 5, v___y_2311_);
lean_closure_set(v___f_2333_, 6, v___x_2269_);
lean_closure_set(v___f_2333_, 7, v___y_2310_);
lean_closure_set(v___f_2333_, 8, v___x_2331_);
lean_closure_set(v___f_2333_, 9, v___x_2332_);
v___x_2334_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___redArg(v_a_2328_, v___f_2333_, v___y_2319_, v___y_2321_, v___y_2318_, v___y_2317_, v___y_2316_, v___y_2312_, v___y_2314_, v___y_2322_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_dec_ref_known(v___x_2334_, 1);
v___y_2296_ = v___y_2315_;
v___y_2297_ = v___y_2320_;
v___y_2298_ = v___y_2312_;
goto v___jp_2295_;
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
lean_dec_ref(v___y_2320_);
lean_dec_ref(v___y_2315_);
lean_dec(v_snd_2266_);
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2334_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2334_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2335_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
else
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2350_; 
lean_dec(v_a_2326_);
lean_dec_ref(v___y_2320_);
lean_dec_ref(v___y_2315_);
lean_dec(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec_ref(v___x_2269_);
lean_dec(v_snd_2266_);
v_a_2343_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2345_ = v___x_2327_;
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2327_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2348_; 
if (v_isShared_2346_ == 0)
{
v___x_2348_ = v___x_2345_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_a_2343_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
}
else
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
lean_dec(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2320_);
lean_dec_ref(v___y_2315_);
lean_dec(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec_ref(v___x_2269_);
lean_dec(v_snd_2266_);
v_a_2351_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2353_ = v___x_2325_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2325_);
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
v___jp_2359_:
{
lean_object* v___x_2373_; 
lean_inc(v_snd_2266_);
v___x_2373_ = l_Lean_MVarId_getType(v_snd_2266_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_object* v_a_2374_; lean_object* v___x_2375_; 
v_a_2374_ = lean_ctor_get(v___x_2373_, 0);
lean_inc(v_a_2374_);
lean_dec_ref_known(v___x_2373_, 1);
lean_inc(v_snd_2266_);
v___x_2375_ = l_Lean_MVarId_getTag(v_snd_2266_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
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
lean_inc_ref(v___y_2363_);
v___x_2381_ = l_Lean_MVarId_note(v___x_2379_, v___x_2380_, v___y_2363_, v___y_2364_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
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
v___x_2385_ = lean_mk_empty_array_with_capacity(v___x_2272_);
v___x_2386_ = lean_array_push(v___x_2385_, v_fst_2383_);
v___x_2387_ = l_Lean_Meta_simpGoal(v_snd_2384_, v___x_2273_, v_simprocs_2274_, v_discharge_x3f_2275_, v___x_2268_, v___x_2386_, v_snd_2276_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
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
lean_dec(v___y_2362_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
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
v___x_2394_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
lean_inc(v_a_2395_);
lean_dec_ref(v___x_2394_);
v___x_2396_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_a_2395_);
lean_dec(v_a_2395_);
if (v___x_2396_ == 0)
{
lean_del_object(v___x_2392_);
lean_dec_ref(v___y_2363_);
lean_dec_ref(v_a_2283_);
lean_dec_ref(v___f_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2280_);
lean_dec_ref(v___x_2279_);
lean_dec(v___x_2278_);
lean_dec_ref(v___f_2277_);
v___y_2296_ = v_a_2378_;
v___y_2297_ = v_snd_2390_;
v___y_2298_ = v___y_2370_;
goto v___jp_2295_;
}
else
{
if (lean_obj_tag(v___y_2363_) == 1)
{
lean_object* v_fvarId_2397_; lean_object* v_lctx_2398_; lean_object* v___x_2399_; 
v_fvarId_2397_ = lean_ctor_get(v___y_2363_, 0);
lean_inc(v_fvarId_2397_);
lean_dec_ref_known(v___y_2363_, 1);
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
lean_object* v___x_2404_; 
lean_inc_ref(v___f_2277_);
lean_inc(v___y_2372_);
lean_inc_ref(v___y_2371_);
lean_inc(v___y_2370_);
lean_inc_ref(v___y_2369_);
lean_inc(v___y_2368_);
lean_inc_ref(v___y_2367_);
lean_inc(v___y_2366_);
lean_inc_ref(v___y_2365_);
v___x_2404_ = lean_apply_9(v___f_2277_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, lean_box(0));
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_object* v_a_2405_; lean_object* v___x_2406_; 
v_a_2405_ = lean_ctor_get(v___x_2404_, 0);
lean_inc(v_a_2405_);
lean_dec_ref_known(v___x_2404_, 1);
lean_inc(v___y_2372_);
lean_inc_ref(v___y_2371_);
lean_inc(v___y_2370_);
lean_inc_ref(v___y_2369_);
lean_inc(v___y_2368_);
lean_inc_ref(v___y_2367_);
lean_inc(v___y_2366_);
lean_inc_ref(v___y_2365_);
v___x_2406_ = lean_apply_9(v___f_2277_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, lean_box(0));
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v_a_2407_; lean_object* v_ref_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2415_; 
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
lean_inc_n(v_a_2407_, 2);
lean_dec_ref_known(v___x_2406_, 1);
v_ref_2408_ = lean_ctor_get(v___y_2371_, 4);
v___x_2409_ = l_Lean_mkIdent(v_val_2400_);
lean_inc(v_a_2405_);
v___x_2410_ = l_Lean_Syntax_node1(v_a_2405_, v___x_2278_, v___x_2409_);
v___x_2411_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2));
lean_inc_ref(v___x_2281_);
lean_inc_ref(v___x_2280_);
lean_inc_ref(v___x_2279_);
v___x_2412_ = l_Lean_Name_mkStr4(v___x_2279_, v___x_2280_, v___x_2281_, v___x_2411_);
v___x_2413_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__3));
if (v_isShared_2393_ == 0)
{
lean_ctor_set_tag(v___x_2392_, 2);
lean_ctor_set(v___x_2392_, 1, v___x_2413_);
lean_ctor_set(v___x_2392_, 0, v_a_2407_);
v___x_2415_ = v___x_2392_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2407_);
lean_ctor_set(v_reuseFailAlloc_2442_, 1, v___x_2413_);
v___x_2415_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2421_; 
v___x_2416_ = l_Lean_Syntax_node1(v_a_2405_, v___x_2412_, v___x_2410_);
v___x_2417_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__4));
v___x_2418_ = l_Lean_Name_mkStr4(v___x_2279_, v___x_2280_, v___x_2281_, v___x_2417_);
v___x_2419_ = l_Lean_Syntax_node2(v_a_2407_, v___x_2418_, v___x_2415_, v___x_2416_);
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
v___x_2422_ = lean_apply_10(v___f_2282_, v___x_2421_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, lean_box(0));
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v_a_2423_; lean_object* v___x_2424_; 
v_a_2423_ = lean_ctor_get(v___x_2422_, 0);
lean_inc(v_a_2423_);
lean_dec_ref_known(v___x_2422_, 1);
lean_inc(v_ref_2408_);
v___x_2424_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa(v_a_2283_, v_ref_2408_, v_a_2423_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_dec_ref_known(v___x_2424_, 1);
v___y_2296_ = v_a_2378_;
v___y_2297_ = v_snd_2390_;
v___y_2298_ = v___y_2370_;
goto v___jp_2295_;
}
else
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2432_; 
lean_dec(v_snd_2390_);
lean_dec(v_a_2378_);
lean_dec(v_snd_2266_);
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
lean_dec_ref(v_a_2283_);
lean_dec(v_snd_2266_);
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
lean_dec(v_a_2405_);
lean_del_object(v___x_2402_);
lean_dec(v_val_2400_);
lean_del_object(v___x_2392_);
lean_dec(v_snd_2390_);
lean_dec(v_a_2378_);
lean_dec_ref(v_a_2283_);
lean_dec_ref(v___f_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2280_);
lean_dec_ref(v___x_2279_);
lean_dec(v___x_2278_);
lean_dec(v_snd_2266_);
v_a_2443_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2445_ = v___x_2406_;
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2406_);
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
lean_del_object(v___x_2402_);
lean_dec(v_val_2400_);
lean_del_object(v___x_2392_);
lean_dec(v_snd_2390_);
lean_dec(v_a_2378_);
lean_dec_ref(v_a_2283_);
lean_dec_ref(v___f_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2280_);
lean_dec_ref(v___x_2279_);
lean_dec(v___x_2278_);
lean_dec_ref(v___f_2277_);
lean_dec(v_snd_2266_);
v_a_2451_ = lean_ctor_get(v___x_2404_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2453_ = v___x_2404_;
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2404_);
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
lean_dec_ref(v_a_2283_);
lean_dec_ref(v___f_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2280_);
lean_dec_ref(v___x_2279_);
lean_dec(v___x_2278_);
lean_dec_ref(v___f_2277_);
v___y_2296_ = v_a_2378_;
v___y_2297_ = v_snd_2390_;
v___y_2298_ = v___y_2370_;
goto v___jp_2295_;
}
}
else
{
lean_del_object(v___x_2392_);
lean_dec_ref(v___y_2363_);
lean_dec_ref(v_a_2283_);
lean_dec_ref(v___f_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2280_);
lean_dec_ref(v___x_2279_);
lean_dec(v___x_2278_);
lean_dec_ref(v___f_2277_);
v___y_2296_ = v_a_2378_;
v___y_2297_ = v_snd_2390_;
v___y_2298_ = v___y_2370_;
goto v___jp_2295_;
}
}
}
}
else
{
lean_object* v_val_2462_; lean_object* v_snd_2463_; lean_object* v_fst_2464_; lean_object* v_snd_2465_; lean_object* v___x_2466_; uint8_t v___x_2467_; 
lean_dec_ref(v___y_2363_);
lean_dec_ref(v_a_2283_);
lean_dec_ref(v___f_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2280_);
lean_dec_ref(v___x_2279_);
lean_dec(v___x_2278_);
lean_dec_ref(v___f_2277_);
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
v___x_2467_ = lean_nat_dec_lt(v___x_2284_, v___x_2466_);
if (v___x_2467_ == 0)
{
lean_dec(v_fst_2464_);
v___y_2309_ = v___y_2360_;
v___y_2310_ = v___y_2361_;
v___y_2311_ = v___y_2362_;
v___y_2312_ = v___y_2370_;
v___y_2313_ = v___x_2380_;
v___y_2314_ = v___y_2371_;
v___y_2315_ = v_a_2378_;
v___y_2316_ = v___y_2369_;
v___y_2317_ = v___y_2368_;
v___y_2318_ = v___y_2367_;
v___y_2319_ = v___y_2365_;
v___y_2320_ = v_snd_2463_;
v___y_2321_ = v___y_2366_;
v___y_2322_ = v___y_2372_;
v___y_2323_ = v_snd_2465_;
v___y_2324_ = v_fst_2383_;
goto v___jp_2308_;
}
else
{
lean_object* v___x_2468_; 
lean_dec(v_fst_2383_);
v___x_2468_ = lean_array_fget(v_fst_2464_, v___x_2284_);
lean_dec(v_fst_2464_);
v___y_2309_ = v___y_2360_;
v___y_2310_ = v___y_2361_;
v___y_2311_ = v___y_2362_;
v___y_2312_ = v___y_2370_;
v___y_2313_ = v___x_2380_;
v___y_2314_ = v___y_2371_;
v___y_2315_ = v_a_2378_;
v___y_2316_ = v___y_2369_;
v___y_2317_ = v___y_2368_;
v___y_2318_ = v___y_2367_;
v___y_2319_ = v___y_2365_;
v___y_2320_ = v_snd_2463_;
v___y_2321_ = v___y_2366_;
v___y_2322_ = v___y_2372_;
v___y_2323_ = v_snd_2465_;
v___y_2324_ = v___x_2468_;
goto v___jp_2308_;
}
}
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2476_; 
lean_dec(v_fst_2383_);
lean_dec(v_a_2378_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
lean_dec_ref(v_a_2283_);
lean_dec_ref(v___f_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2280_);
lean_dec_ref(v___x_2279_);
lean_dec(v___x_2278_);
lean_dec_ref(v___f_2277_);
lean_dec_ref(v___x_2269_);
lean_dec(v_snd_2266_);
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
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
lean_dec_ref(v_a_2283_);
lean_dec_ref(v___f_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2280_);
lean_dec_ref(v___x_2279_);
lean_dec(v___x_2278_);
lean_dec_ref(v___f_2277_);
lean_dec_ref(v_snd_2276_);
lean_dec(v_discharge_x3f_2275_);
lean_dec_ref(v_simprocs_2274_);
lean_dec_ref(v___x_2273_);
lean_dec_ref(v___x_2269_);
lean_dec(v_snd_2266_);
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
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
lean_dec_ref(v_a_2283_);
lean_dec_ref(v___f_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2280_);
lean_dec_ref(v___x_2279_);
lean_dec(v___x_2278_);
lean_dec_ref(v___f_2277_);
lean_dec_ref(v_snd_2276_);
lean_dec(v_discharge_x3f_2275_);
lean_dec_ref(v_simprocs_2274_);
lean_dec_ref(v___x_2273_);
lean_dec_ref(v___x_2269_);
lean_dec(v_snd_2266_);
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
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
lean_dec_ref(v_a_2283_);
lean_dec_ref(v___f_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2280_);
lean_dec_ref(v___x_2279_);
lean_dec(v___x_2278_);
lean_dec_ref(v___f_2277_);
lean_dec_ref(v_snd_2276_);
lean_dec(v_discharge_x3f_2275_);
lean_dec_ref(v_simprocs_2274_);
lean_dec_ref(v___x_2273_);
lean_dec_ref(v___x_2269_);
lean_dec(v_snd_2266_);
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
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
lean_dec_ref(v_a_2283_);
lean_dec_ref(v___f_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2280_);
lean_dec_ref(v___x_2279_);
lean_dec(v___x_2278_);
lean_dec_ref(v___f_2277_);
lean_dec_ref(v_snd_2276_);
lean_dec(v_discharge_x3f_2275_);
lean_dec_ref(v_simprocs_2274_);
lean_dec_ref(v___x_2273_);
lean_dec_ref(v___x_2269_);
lean_dec(v_snd_2266_);
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
uint8_t v___x_95463__boxed_2668_; uint8_t v___x_95464__boxed_2669_; uint8_t v_useReducible_boxed_2670_; uint8_t v___x_95466__boxed_2671_; lean_object* v_res_2672_; 
v___x_95463__boxed_2668_ = lean_unbox(v___x_2640_);
v___x_95464__boxed_2669_ = lean_unbox(v___x_2641_);
v_useReducible_boxed_2670_ = lean_unbox(v_useReducible_2643_);
v___x_95466__boxed_2671_ = lean_unbox(v___x_2644_);
v_res_2672_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5(v_usingArg_2638_, v_snd_2639_, v___x_95463__boxed_2668_, v___x_95464__boxed_2669_, v___x_2642_, v_useReducible_boxed_2670_, v___x_95466__boxed_2671_, v___x_2645_, v___x_2646_, v_simprocs_2647_, v_discharge_x3f_2648_, v_snd_2649_, v___f_2650_, v___x_2651_, v___x_2652_, v___x_2653_, v___x_2654_, v___f_2655_, v_a_2656_, v___x_2657_, v___f_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
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
v___x_2673_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6(lean_object* v___x_2679_, lean_object* v_tk_2680_, lean_object* v___x_2681_, lean_object* v___x_2682_, lean_object* v___x_2683_, lean_object* v_simprocs_2684_, uint8_t v___x_2685_, lean_object* v_usingArg_2686_, uint8_t v___x_2687_, lean_object* v___x_2688_, uint8_t v_useReducible_2689_, uint8_t v___x_2690_, lean_object* v___x_2691_, lean_object* v___f_2692_, lean_object* v___x_2693_, lean_object* v___x_2694_, lean_object* v___x_2695_, lean_object* v___f_2696_, lean_object* v_a_2697_, lean_object* v_usingTk_x3f_2698_, lean_object* v_discharge_x3f_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
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
lean_object* v_a_2717_; lean_object* v___x_2718_; 
v_a_2717_ = lean_ctor_get(v___x_2716_, 0);
lean_inc(v_a_2717_);
lean_dec_ref_known(v___x_2716_, 1);
v___x_2718_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2701_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
if (lean_obj_tag(v___x_2718_) == 0)
{
lean_object* v_a_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; size_t v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v_a_2719_ = lean_ctor_get(v___x_2718_, 0);
lean_inc(v_a_2719_);
lean_dec_ref_known(v___x_2718_, 1);
v___x_2720_ = lean_mk_empty_array_with_capacity(v___x_2682_);
v___x_2721_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1);
lean_inc_n(v___x_2682_, 3);
v___x_2722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2721_);
lean_ctor_set(v___x_2722_, 1, v___x_2682_);
v___x_2723_ = lean_unsigned_to_nat(32u);
v___x_2724_ = lean_mk_empty_array_with_capacity(v___x_2723_);
v___x_2725_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2);
v___x_2726_ = ((size_t)5ULL);
v___x_2727_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2727_, 0, v___x_2725_);
lean_ctor_set(v___x_2727_, 1, v___x_2724_);
lean_ctor_set(v___x_2727_, 2, v___x_2682_);
lean_ctor_set(v___x_2727_, 3, v___x_2682_);
lean_ctor_set_usize(v___x_2727_, 4, v___x_2726_);
v___x_2728_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2728_, 0, v___x_2721_);
lean_ctor_set(v___x_2728_, 1, v___x_2721_);
lean_ctor_set(v___x_2728_, 2, v___x_2721_);
lean_ctor_set(v___x_2728_, 3, v___x_2727_);
v___x_2729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2722_);
lean_ctor_set(v___x_2729_, 1, v___x_2728_);
lean_inc_ref(v___x_2729_);
lean_inc(v_discharge_x3f_2699_);
lean_inc_ref(v_simprocs_2684_);
lean_inc_ref(v___x_2683_);
v___x_2730_ = l_Lean_Meta_simpGoal(v_a_2719_, v___x_2683_, v_simprocs_2684_, v_discharge_x3f_2699_, v___x_2685_, v___x_2720_, v___x_2729_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v_a_2731_; lean_object* v_fst_2732_; 
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
lean_inc(v_a_2731_);
lean_dec_ref_known(v___x_2730_, 1);
v_fst_2732_ = lean_ctor_get(v_a_2731_, 0);
if (lean_obj_tag(v_fst_2732_) == 1)
{
lean_object* v_val_2733_; lean_object* v_snd_2734_; lean_object* v_snd_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2759_; 
lean_dec_ref_known(v___x_2729_, 2);
v_val_2733_ = lean_ctor_get(v_fst_2732_, 0);
lean_inc(v_val_2733_);
v_snd_2734_ = lean_ctor_get(v_a_2731_, 1);
lean_inc(v_snd_2734_);
lean_dec(v_a_2731_);
v_snd_2735_ = lean_ctor_get(v_val_2733_, 1);
v_isSharedCheck_2759_ = !lean_is_exclusive(v_val_2733_);
if (v_isSharedCheck_2759_ == 0)
{
lean_object* v_unused_2760_; 
v_unused_2760_ = lean_ctor_get(v_val_2733_, 0);
lean_dec(v_unused_2760_);
v___x_2737_ = v_val_2733_;
v_isShared_2738_ = v_isSharedCheck_2759_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_snd_2735_);
lean_dec(v_val_2733_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2759_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2739_; lean_object* v___x_2741_; 
v___x_2739_ = lean_box(0);
lean_inc(v_snd_2735_);
if (v_isShared_2738_ == 0)
{
lean_ctor_set_tag(v___x_2737_, 1);
lean_ctor_set(v___x_2737_, 1, v___x_2739_);
lean_ctor_set(v___x_2737_, 0, v_snd_2735_);
v___x_2741_ = v___x_2737_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_snd_2735_);
lean_ctor_set(v_reuseFailAlloc_2758_, 1, v___x_2739_);
v___x_2741_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
lean_object* v___x_2742_; 
v___x_2742_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2741_, v___y_2701_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v___f_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___y_2748_; lean_object* v___x_2749_; 
lean_dec_ref_known(v___x_2742_, 1);
v___f_2743_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___boxed), 11, 1);
lean_closure_set(v___f_2743_, 0, v_a_2717_);
v___x_2744_ = lean_box(v___x_2685_);
v___x_2745_ = lean_box(v___x_2687_);
v___x_2746_ = lean_box(v_useReducible_2689_);
v___x_2747_ = lean_box(v___x_2690_);
lean_inc(v_snd_2735_);
v___y_2748_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___boxed), 30, 21);
lean_closure_set(v___y_2748_, 0, v_usingArg_2686_);
lean_closure_set(v___y_2748_, 1, v_snd_2735_);
lean_closure_set(v___y_2748_, 2, v___x_2744_);
lean_closure_set(v___y_2748_, 3, v___x_2745_);
lean_closure_set(v___y_2748_, 4, v___x_2688_);
lean_closure_set(v___y_2748_, 5, v___x_2746_);
lean_closure_set(v___y_2748_, 6, v___x_2747_);
lean_closure_set(v___y_2748_, 7, v___x_2691_);
lean_closure_set(v___y_2748_, 8, v___x_2683_);
lean_closure_set(v___y_2748_, 9, v_simprocs_2684_);
lean_closure_set(v___y_2748_, 10, v_discharge_x3f_2699_);
lean_closure_set(v___y_2748_, 11, v_snd_2734_);
lean_closure_set(v___y_2748_, 12, v___f_2692_);
lean_closure_set(v___y_2748_, 13, v___x_2681_);
lean_closure_set(v___y_2748_, 14, v___x_2693_);
lean_closure_set(v___y_2748_, 15, v___x_2694_);
lean_closure_set(v___y_2748_, 16, v___x_2695_);
lean_closure_set(v___y_2748_, 17, v___f_2696_);
lean_closure_set(v___y_2748_, 18, v_a_2697_);
lean_closure_set(v___y_2748_, 19, v___x_2682_);
lean_closure_set(v___y_2748_, 20, v___f_2743_);
v___x_2749_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___redArg(v_snd_2735_, v___y_2748_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
return v___x_2749_;
}
else
{
lean_object* v_a_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2757_; 
lean_dec(v_snd_2735_);
lean_dec(v_snd_2734_);
lean_dec(v_a_2717_);
lean_dec(v_discharge_x3f_2699_);
lean_dec_ref(v_a_2697_);
lean_dec_ref(v___f_2696_);
lean_dec_ref(v___x_2695_);
lean_dec_ref(v___x_2694_);
lean_dec_ref(v___x_2693_);
lean_dec_ref(v___f_2692_);
lean_dec(v___x_2691_);
lean_dec_ref(v___x_2688_);
lean_dec(v_usingArg_2686_);
lean_dec_ref(v_simprocs_2684_);
lean_dec_ref(v___x_2683_);
lean_dec(v___x_2682_);
lean_dec(v___x_2681_);
v_a_2750_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2752_ = v___x_2742_;
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_a_2750_);
lean_dec(v___x_2742_);
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
lean_dec(v_a_2731_);
lean_dec(v_a_2717_);
lean_dec(v_discharge_x3f_2699_);
lean_dec_ref(v___x_2695_);
lean_dec_ref(v___x_2694_);
lean_dec_ref(v___x_2693_);
lean_dec_ref(v___f_2692_);
lean_dec(v___x_2691_);
lean_dec_ref(v___x_2688_);
lean_dec(v_usingArg_2686_);
lean_dec_ref(v_simprocs_2684_);
lean_dec_ref(v___x_2683_);
lean_dec(v___x_2682_);
lean_dec(v___x_2681_);
v___x_2761_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
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
lean_ctor_set(v___x_2764_, 0, v___x_2729_);
v___x_2768_ = v___x_2764_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v___x_2729_);
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
v_ref_2770_ = lean_ctor_get(v___y_2706_, 4);
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
lean_ctor_set(v___x_2776_, 0, v___x_2729_);
v___x_2779_ = v___x_2776_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v___x_2729_);
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
lean_dec_ref_known(v___x_2729_, 2);
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
lean_dec_ref_known(v___x_2729_, 2);
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
lean_dec_ref_known(v___x_2729_, 2);
lean_dec(v_a_2717_);
lean_dec(v_discharge_x3f_2699_);
lean_dec_ref(v_a_2697_);
lean_dec_ref(v___f_2696_);
lean_dec_ref(v___x_2695_);
lean_dec_ref(v___x_2694_);
lean_dec_ref(v___x_2693_);
lean_dec_ref(v___f_2692_);
lean_dec(v___x_2691_);
lean_dec_ref(v___x_2688_);
lean_dec(v_usingArg_2686_);
lean_dec_ref(v_simprocs_2684_);
lean_dec_ref(v___x_2683_);
lean_dec(v___x_2682_);
lean_dec(v___x_2681_);
v_a_2800_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2802_ = v___x_2730_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2730_);
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
lean_dec(v_a_2717_);
lean_dec(v_discharge_x3f_2699_);
lean_dec_ref(v_a_2697_);
lean_dec_ref(v___f_2696_);
lean_dec_ref(v___x_2695_);
lean_dec_ref(v___x_2694_);
lean_dec_ref(v___x_2693_);
lean_dec_ref(v___f_2692_);
lean_dec(v___x_2691_);
lean_dec_ref(v___x_2688_);
lean_dec(v_usingArg_2686_);
lean_dec_ref(v_simprocs_2684_);
lean_dec_ref(v___x_2683_);
lean_dec(v___x_2682_);
lean_dec(v___x_2681_);
v_a_2808_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2810_ = v___x_2718_;
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2718_);
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
lean_dec_ref(v___x_2688_);
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
uint8_t v___x_96258__boxed_2856_; uint8_t v___x_96259__boxed_2857_; uint8_t v_useReducible_boxed_2858_; uint8_t v___x_96261__boxed_2859_; lean_object* v_res_2860_; 
v___x_96258__boxed_2856_ = lean_unbox(v___x_2832_);
v___x_96259__boxed_2857_ = lean_unbox(v___x_2834_);
v_useReducible_boxed_2858_ = lean_unbox(v_useReducible_2836_);
v___x_96261__boxed_2859_ = lean_unbox(v___x_2837_);
v_res_2860_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6(v___x_2826_, v_tk_2827_, v___x_2828_, v___x_2829_, v___x_2830_, v_simprocs_2831_, v___x_96258__boxed_2856_, v_usingArg_2833_, v___x_96259__boxed_2857_, v___x_2835_, v_useReducible_boxed_2858_, v___x_96261__boxed_2859_, v___x_2838_, v___f_2839_, v___x_2840_, v___x_2841_, v___x_2842_, v___f_2843_, v_a_2844_, v_usingTk_x3f_2845_, v_discharge_x3f_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
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
lean_object* v_a_2975_; lean_object* v_options_2976_; lean_object* v_ref_2977_; uint8_t v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; uint8_t v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3386_; uint8_t v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v_args_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3427_; uint8_t v___y_3428_; lean_object* v___y_3429_; lean_object* v___y_3430_; lean_object* v___y_3431_; lean_object* v___y_3432_; lean_object* v_only_3433_; lean_object* v___y_3434_; lean_object* v___y_3435_; lean_object* v___y_3436_; lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3441_; uint8_t v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3464_; uint8_t v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3523_; uint8_t v___y_3534_; lean_object* v___y_3535_; lean_object* v___y_3536_; uint8_t v___y_3537_; lean_object* v___y_3539_; uint8_t v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3563_; lean_object* v___y_3564_; lean_object* v___y_3565_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3611_; 
v_a_2975_ = lean_ctor_get(v___x_2974_, 0);
lean_inc(v_a_2975_);
lean_dec_ref_known(v___x_2974_, 1);
v_options_2976_ = lean_ctor_get(v___y_2917_, 1);
v_ref_2977_ = lean_ctor_get(v___y_2917_, 4);
v___x_2978_ = 0;
v___x_2979_ = l_Lean_SourceInfo_fromRef(v_ref_2977_, v___x_2978_);
v___x_2980_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__3));
lean_inc_ref(v___x_2888_);
lean_inc_ref(v___x_2887_);
lean_inc_ref(v___x_2886_);
v___x_2981_ = l_Lean_Name_mkStr4(v___x_2886_, v___x_2887_, v___x_2888_, v___x_2980_);
lean_inc(v___x_2979_);
v___x_2982_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2982_, 0, v___x_2979_);
lean_ctor_set(v___x_2982_, 1, v___x_2980_);
v___x_2983_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_2984_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6);
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
v___jp_2985_:
{
lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
v___x_2997_ = l_Array_append___redArg(v___x_2984_, v___y_2996_);
lean_dec_ref(v___y_2996_);
lean_inc_n(v___y_2988_, 2);
v___x_2998_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2998_, 0, v___y_2988_);
lean_ctor_set(v___x_2998_, 1, v___x_2983_);
lean_ctor_set(v___x_2998_, 2, v___x_2997_);
v___x_2999_ = l_Lean_Syntax_node5(v___y_2988_, v___x_2891_, v___y_2986_, v___y_2993_, v___y_2989_, v___y_2995_, v___x_2998_);
v___x_3000_ = l_Lean_Syntax_node2(v___y_2988_, v___y_2992_, v___y_2987_, v___x_2999_);
v___y_2948_ = v___y_2990_;
v_stx_2949_ = v___x_3000_;
v___y_2950_ = v___y_2991_;
v___y_2951_ = v___y_2994_;
goto v___jp_2947_;
}
v___jp_3001_:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3013_ = l_Array_append___redArg(v___x_2984_, v___y_3012_);
lean_dec_ref(v___y_3012_);
lean_inc(v___y_3004_);
v___x_3014_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3014_, 0, v___y_3004_);
lean_ctor_set(v___x_3014_, 1, v___x_2983_);
lean_ctor_set(v___x_3014_, 2, v___x_3013_);
if (lean_obj_tag(v___y_3007_) == 1)
{
lean_object* v_val_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; 
lean_dec(v___x_2889_);
v_val_3015_ = lean_ctor_get(v___y_3007_, 0);
lean_inc(v_val_3015_);
lean_dec_ref_known(v___y_3007_, 1);
v___x_3016_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__5));
lean_inc(v___y_3004_);
v___x_3017_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3017_, 0, v___y_3004_);
lean_ctor_set(v___x_3017_, 1, v___x_3016_);
v___x_3018_ = l_Array_mkArray2___redArg(v___x_3017_, v_val_3015_);
v___y_2986_ = v___y_3002_;
v___y_2987_ = v___y_3003_;
v___y_2988_ = v___y_3004_;
v___y_2989_ = v___y_3005_;
v___y_2990_ = v___y_3006_;
v___y_2991_ = v___y_3010_;
v___y_2992_ = v___y_3009_;
v___y_2993_ = v___y_3008_;
v___y_2994_ = v___y_3011_;
v___y_2995_ = v___x_3014_;
v___y_2996_ = v___x_3018_;
goto v___jp_2985_;
}
else
{
lean_object* v___x_3019_; 
lean_dec(v___y_3007_);
v___x_3019_ = lean_mk_empty_array_with_capacity(v___x_2889_);
lean_dec(v___x_2889_);
v___y_2986_ = v___y_3002_;
v___y_2987_ = v___y_3003_;
v___y_2988_ = v___y_3004_;
v___y_2989_ = v___y_3005_;
v___y_2990_ = v___y_3006_;
v___y_2991_ = v___y_3010_;
v___y_2992_ = v___y_3009_;
v___y_2993_ = v___y_3008_;
v___y_2994_ = v___y_3011_;
v___y_2995_ = v___x_3014_;
v___y_2996_ = v___x_3019_;
goto v___jp_2985_;
}
}
v___jp_3020_:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3032_ = l_Array_append___redArg(v___x_2984_, v___y_3031_);
lean_dec_ref(v___y_3031_);
lean_inc(v___y_3023_);
v___x_3033_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3033_, 0, v___y_3023_);
lean_ctor_set(v___x_3033_, 1, v___x_2983_);
lean_ctor_set(v___x_3033_, 2, v___x_3032_);
if (lean_obj_tag(v___y_3024_) == 1)
{
lean_object* v_val_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; 
v_val_3034_ = lean_ctor_get(v___y_3024_, 0);
lean_inc(v_val_3034_);
lean_dec_ref_known(v___y_3024_, 1);
v___x_3035_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_3036_ = l_Lean_Name_mkStr4(v___x_2886_, v___x_2887_, v___x_2888_, v___x_3035_);
v___x_3037_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_3023_, 4);
v___x_3038_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3038_, 0, v___y_3023_);
lean_ctor_set(v___x_3038_, 1, v___x_3037_);
v___x_3039_ = l_Array_append___redArg(v___x_2984_, v_val_3034_);
lean_dec(v_val_3034_);
v___x_3040_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3040_, 0, v___y_3023_);
lean_ctor_set(v___x_3040_, 1, v___x_2983_);
lean_ctor_set(v___x_3040_, 2, v___x_3039_);
v___x_3041_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_3042_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3042_, 0, v___y_3023_);
lean_ctor_set(v___x_3042_, 1, v___x_3041_);
v___x_3043_ = l_Lean_Syntax_node3(v___y_3023_, v___x_3036_, v___x_3038_, v___x_3040_, v___x_3042_);
v___x_3044_ = l_Array_mkArray1___redArg(v___x_3043_);
v___y_3002_ = v___y_3021_;
v___y_3003_ = v___y_3022_;
v___y_3004_ = v___y_3023_;
v___y_3005_ = v___x_3033_;
v___y_3006_ = v___y_3025_;
v___y_3007_ = v___y_3029_;
v___y_3008_ = v___y_3028_;
v___y_3009_ = v___y_3027_;
v___y_3010_ = v___y_3026_;
v___y_3011_ = v___y_3030_;
v___y_3012_ = v___x_3044_;
goto v___jp_3001_;
}
else
{
lean_object* v___x_3045_; 
lean_dec(v___y_3024_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v___x_2886_);
v___x_3045_ = lean_mk_empty_array_with_capacity(v___x_2889_);
v___y_3002_ = v___y_3021_;
v___y_3003_ = v___y_3022_;
v___y_3004_ = v___y_3023_;
v___y_3005_ = v___x_3033_;
v___y_3006_ = v___y_3025_;
v___y_3007_ = v___y_3029_;
v___y_3008_ = v___y_3028_;
v___y_3009_ = v___y_3027_;
v___y_3010_ = v___y_3026_;
v___y_3011_ = v___y_3030_;
v___y_3012_ = v___x_3045_;
goto v___jp_3001_;
}
}
v___jp_3046_:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3058_ = l_Array_append___redArg(v___x_2984_, v___y_3057_);
lean_dec_ref(v___y_3057_);
lean_inc(v___y_3049_);
v___x_3059_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3059_, 0, v___y_3049_);
lean_ctor_set(v___x_3059_, 1, v___x_2983_);
lean_ctor_set(v___x_3059_, 2, v___x_3058_);
if (lean_obj_tag(v___y_3051_) == 1)
{
lean_object* v_val_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; 
v_val_3060_ = lean_ctor_get(v___y_3051_, 0);
lean_inc(v_val_3060_);
lean_dec_ref_known(v___y_3051_, 1);
v___x_3061_ = l_Lean_SourceInfo_fromRef(v_val_3060_, v___x_2890_);
lean_dec(v_val_3060_);
v___x_3062_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_3063_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3063_, 0, v___x_3061_);
lean_ctor_set(v___x_3063_, 1, v___x_3062_);
v___x_3064_ = l_Array_mkArray1___redArg(v___x_3063_);
v___y_3021_ = v___y_3047_;
v___y_3022_ = v___y_3048_;
v___y_3023_ = v___y_3049_;
v___y_3024_ = v___y_3050_;
v___y_3025_ = v___y_3052_;
v___y_3026_ = v___y_3055_;
v___y_3027_ = v___y_3054_;
v___y_3028_ = v___x_3059_;
v___y_3029_ = v___y_3053_;
v___y_3030_ = v___y_3056_;
v___y_3031_ = v___x_3064_;
goto v___jp_3020_;
}
else
{
lean_object* v___x_3065_; 
lean_dec(v___y_3051_);
v___x_3065_ = lean_mk_empty_array_with_capacity(v___x_2889_);
v___y_3021_ = v___y_3047_;
v___y_3022_ = v___y_3048_;
v___y_3023_ = v___y_3049_;
v___y_3024_ = v___y_3050_;
v___y_3025_ = v___y_3052_;
v___y_3026_ = v___y_3055_;
v___y_3027_ = v___y_3054_;
v___y_3028_ = v___x_3059_;
v___y_3029_ = v___y_3053_;
v___y_3030_ = v___y_3056_;
v___y_3031_ = v___x_3065_;
goto v___jp_3020_;
}
}
v___jp_3066_:
{
lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3081_ = l_Array_append___redArg(v___x_2984_, v___y_3080_);
lean_dec_ref(v___y_3080_);
lean_inc_n(v___y_3077_, 3);
v___x_3082_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3082_, 0, v___y_3077_);
lean_ctor_set(v___x_3082_, 1, v___x_2983_);
lean_ctor_set(v___x_3082_, 2, v___x_3081_);
v___x_3083_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__6));
v___x_3084_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3084_, 0, v___y_3077_);
lean_ctor_set(v___x_3084_, 1, v___x_3083_);
v___x_3085_ = l_Lean_Syntax_node6(v___y_3077_, v___y_3073_, v___y_3067_, v___y_3071_, v___y_3068_, v___x_3082_, v___x_3084_, v___y_3069_);
v___x_3086_ = l_Lean_Syntax_node4(v___y_3077_, v___y_3074_, v___y_3075_, v___y_3079_, v___y_3072_, v___x_3085_);
v___y_2948_ = v___y_3076_;
v_stx_2949_ = v___x_3086_;
v___y_2950_ = v___y_3078_;
v___y_2951_ = v___y_3070_;
goto v___jp_2947_;
}
v___jp_3087_:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3102_ = l_Array_append___redArg(v___x_2984_, v___y_3101_);
lean_dec_ref(v___y_3101_);
lean_inc(v___y_3098_);
v___x_3103_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3103_, 0, v___y_3098_);
lean_ctor_set(v___x_3103_, 1, v___x_2983_);
lean_ctor_set(v___x_3103_, 2, v___x_3102_);
if (lean_obj_tag(v___y_3089_) == 1)
{
lean_object* v_val_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
lean_dec(v___x_2889_);
v_val_3104_ = lean_ctor_get(v___y_3089_, 0);
lean_inc(v_val_3104_);
lean_dec_ref_known(v___y_3089_, 1);
v___x_3105_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_3106_ = l_Lean_Name_mkStr4(v___x_2886_, v___x_2887_, v___x_2888_, v___x_3105_);
v___x_3107_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_3098_, 4);
v___x_3108_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3108_, 0, v___y_3098_);
lean_ctor_set(v___x_3108_, 1, v___x_3107_);
v___x_3109_ = l_Array_append___redArg(v___x_2984_, v_val_3104_);
lean_dec(v_val_3104_);
v___x_3110_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3110_, 0, v___y_3098_);
lean_ctor_set(v___x_3110_, 1, v___x_2983_);
lean_ctor_set(v___x_3110_, 2, v___x_3109_);
v___x_3111_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_3112_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3112_, 0, v___y_3098_);
lean_ctor_set(v___x_3112_, 1, v___x_3111_);
v___x_3113_ = l_Lean_Syntax_node3(v___y_3098_, v___x_3106_, v___x_3108_, v___x_3110_, v___x_3112_);
v___x_3114_ = l_Array_mkArray1___redArg(v___x_3113_);
v___y_3067_ = v___y_3088_;
v___y_3068_ = v___x_3103_;
v___y_3069_ = v___y_3090_;
v___y_3070_ = v___y_3091_;
v___y_3071_ = v___y_3092_;
v___y_3072_ = v___y_3093_;
v___y_3073_ = v___y_3094_;
v___y_3074_ = v___y_3095_;
v___y_3075_ = v___y_3096_;
v___y_3076_ = v___y_3097_;
v___y_3077_ = v___y_3098_;
v___y_3078_ = v___y_3099_;
v___y_3079_ = v___y_3100_;
v___y_3080_ = v___x_3114_;
goto v___jp_3066_;
}
else
{
lean_object* v___x_3115_; 
lean_dec(v___y_3089_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v___x_2886_);
v___x_3115_ = lean_mk_empty_array_with_capacity(v___x_2889_);
lean_dec(v___x_2889_);
v___y_3067_ = v___y_3088_;
v___y_3068_ = v___x_3103_;
v___y_3069_ = v___y_3090_;
v___y_3070_ = v___y_3091_;
v___y_3071_ = v___y_3092_;
v___y_3072_ = v___y_3093_;
v___y_3073_ = v___y_3094_;
v___y_3074_ = v___y_3095_;
v___y_3075_ = v___y_3096_;
v___y_3076_ = v___y_3097_;
v___y_3077_ = v___y_3098_;
v___y_3078_ = v___y_3099_;
v___y_3079_ = v___y_3100_;
v___y_3080_ = v___x_3115_;
goto v___jp_3066_;
}
}
v___jp_3116_:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3131_ = l_Array_append___redArg(v___x_2984_, v___y_3130_);
lean_dec_ref(v___y_3130_);
lean_inc(v___y_3127_);
v___x_3132_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3132_, 0, v___y_3127_);
lean_ctor_set(v___x_3132_, 1, v___x_2983_);
lean_ctor_set(v___x_3132_, 2, v___x_3131_);
if (lean_obj_tag(v___y_3120_) == 1)
{
lean_object* v_val_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v_val_3133_ = lean_ctor_get(v___y_3120_, 0);
lean_inc(v_val_3133_);
lean_dec_ref_known(v___y_3120_, 1);
v___x_3134_ = l_Lean_SourceInfo_fromRef(v_val_3133_, v___x_2890_);
lean_dec(v_val_3133_);
v___x_3135_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_3136_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3134_);
lean_ctor_set(v___x_3136_, 1, v___x_3135_);
v___x_3137_ = l_Array_mkArray1___redArg(v___x_3136_);
v___y_3088_ = v___y_3117_;
v___y_3089_ = v___y_3118_;
v___y_3090_ = v___y_3119_;
v___y_3091_ = v___y_3121_;
v___y_3092_ = v___x_3132_;
v___y_3093_ = v___y_3122_;
v___y_3094_ = v___y_3123_;
v___y_3095_ = v___y_3124_;
v___y_3096_ = v___y_3125_;
v___y_3097_ = v___y_3126_;
v___y_3098_ = v___y_3127_;
v___y_3099_ = v___y_3128_;
v___y_3100_ = v___y_3129_;
v___y_3101_ = v___x_3137_;
goto v___jp_3087_;
}
else
{
lean_object* v___x_3138_; 
lean_dec(v___y_3120_);
v___x_3138_ = lean_mk_empty_array_with_capacity(v___x_2889_);
v___y_3088_ = v___y_3117_;
v___y_3089_ = v___y_3118_;
v___y_3090_ = v___y_3119_;
v___y_3091_ = v___y_3121_;
v___y_3092_ = v___x_3132_;
v___y_3093_ = v___y_3122_;
v___y_3094_ = v___y_3123_;
v___y_3095_ = v___y_3124_;
v___y_3096_ = v___y_3125_;
v___y_3097_ = v___y_3126_;
v___y_3098_ = v___y_3127_;
v___y_3099_ = v___y_3128_;
v___y_3100_ = v___y_3129_;
v___y_3101_ = v___x_3138_;
goto v___jp_3087_;
}
}
v___jp_3139_:
{
lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___x_3151_ = l_Array_append___redArg(v___x_2984_, v___y_3150_);
lean_dec_ref(v___y_3150_);
lean_inc_n(v___y_3149_, 2);
v___x_3152_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3152_, 0, v___y_3149_);
lean_ctor_set(v___x_3152_, 1, v___x_2983_);
lean_ctor_set(v___x_3152_, 2, v___x_3151_);
v___x_3153_ = l_Lean_Syntax_node5(v___y_3149_, v___x_2891_, v___y_3142_, v___y_3141_, v___y_3144_, v___y_3140_, v___x_3152_);
lean_inc(v___y_3143_);
v___x_3154_ = l_Lean_Syntax_node4(v___y_3149_, v___x_2892_, v___y_3147_, v___y_3143_, v___y_3143_, v___x_3153_);
v___y_2948_ = v___y_3145_;
v_stx_2949_ = v___x_3154_;
v___y_2950_ = v___y_3146_;
v___y_2951_ = v___y_3148_;
goto v___jp_2947_;
}
v___jp_3155_:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; 
v___x_3167_ = l_Array_append___redArg(v___x_2984_, v___y_3166_);
lean_dec_ref(v___y_3166_);
lean_inc(v___y_3165_);
v___x_3168_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3168_, 0, v___y_3165_);
lean_ctor_set(v___x_3168_, 1, v___x_2983_);
lean_ctor_set(v___x_3168_, 2, v___x_3167_);
if (lean_obj_tag(v___y_3161_) == 1)
{
lean_object* v_val_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; 
lean_dec(v___x_2889_);
v_val_3169_ = lean_ctor_get(v___y_3161_, 0);
lean_inc(v_val_3169_);
lean_dec_ref_known(v___y_3161_, 1);
v___x_3170_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__5));
lean_inc(v___y_3165_);
v___x_3171_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3171_, 0, v___y_3165_);
lean_ctor_set(v___x_3171_, 1, v___x_3170_);
v___x_3172_ = l_Array_mkArray2___redArg(v___x_3171_, v_val_3169_);
v___y_3140_ = v___x_3168_;
v___y_3141_ = v___y_3157_;
v___y_3142_ = v___y_3156_;
v___y_3143_ = v___y_3159_;
v___y_3144_ = v___y_3158_;
v___y_3145_ = v___y_3160_;
v___y_3146_ = v___y_3163_;
v___y_3147_ = v___y_3162_;
v___y_3148_ = v___y_3164_;
v___y_3149_ = v___y_3165_;
v___y_3150_ = v___x_3172_;
goto v___jp_3139_;
}
else
{
lean_object* v___x_3173_; 
lean_dec(v___y_3161_);
v___x_3173_ = lean_mk_empty_array_with_capacity(v___x_2889_);
lean_dec(v___x_2889_);
v___y_3140_ = v___x_3168_;
v___y_3141_ = v___y_3157_;
v___y_3142_ = v___y_3156_;
v___y_3143_ = v___y_3159_;
v___y_3144_ = v___y_3158_;
v___y_3145_ = v___y_3160_;
v___y_3146_ = v___y_3163_;
v___y_3147_ = v___y_3162_;
v___y_3148_ = v___y_3164_;
v___y_3149_ = v___y_3165_;
v___y_3150_ = v___x_3173_;
goto v___jp_3139_;
}
}
v___jp_3174_:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3186_ = l_Array_append___redArg(v___x_2984_, v___y_3185_);
lean_dec_ref(v___y_3185_);
lean_inc(v___y_3184_);
v___x_3187_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3187_, 0, v___y_3184_);
lean_ctor_set(v___x_3187_, 1, v___x_2983_);
lean_ctor_set(v___x_3187_, 2, v___x_3186_);
if (lean_obj_tag(v___y_3177_) == 1)
{
lean_object* v_val_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; 
v_val_3188_ = lean_ctor_get(v___y_3177_, 0);
lean_inc(v_val_3188_);
lean_dec_ref_known(v___y_3177_, 1);
v___x_3189_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_3190_ = l_Lean_Name_mkStr4(v___x_2886_, v___x_2887_, v___x_2888_, v___x_3189_);
v___x_3191_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_3184_, 4);
v___x_3192_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3192_, 0, v___y_3184_);
lean_ctor_set(v___x_3192_, 1, v___x_3191_);
v___x_3193_ = l_Array_append___redArg(v___x_2984_, v_val_3188_);
lean_dec(v_val_3188_);
v___x_3194_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3194_, 0, v___y_3184_);
lean_ctor_set(v___x_3194_, 1, v___x_2983_);
lean_ctor_set(v___x_3194_, 2, v___x_3193_);
v___x_3195_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_3196_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3196_, 0, v___y_3184_);
lean_ctor_set(v___x_3196_, 1, v___x_3195_);
v___x_3197_ = l_Lean_Syntax_node3(v___y_3184_, v___x_3190_, v___x_3192_, v___x_3194_, v___x_3196_);
v___x_3198_ = l_Array_mkArray1___redArg(v___x_3197_);
v___y_3156_ = v___y_3176_;
v___y_3157_ = v___y_3175_;
v___y_3158_ = v___x_3187_;
v___y_3159_ = v___y_3178_;
v___y_3160_ = v___y_3179_;
v___y_3161_ = v___y_3182_;
v___y_3162_ = v___y_3181_;
v___y_3163_ = v___y_3180_;
v___y_3164_ = v___y_3183_;
v___y_3165_ = v___y_3184_;
v___y_3166_ = v___x_3198_;
goto v___jp_3155_;
}
else
{
lean_object* v___x_3199_; 
lean_dec(v___y_3177_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v___x_2886_);
v___x_3199_ = lean_mk_empty_array_with_capacity(v___x_2889_);
v___y_3156_ = v___y_3176_;
v___y_3157_ = v___y_3175_;
v___y_3158_ = v___x_3187_;
v___y_3159_ = v___y_3178_;
v___y_3160_ = v___y_3179_;
v___y_3161_ = v___y_3182_;
v___y_3162_ = v___y_3181_;
v___y_3163_ = v___y_3180_;
v___y_3164_ = v___y_3183_;
v___y_3165_ = v___y_3184_;
v___y_3166_ = v___x_3199_;
goto v___jp_3155_;
}
}
v___jp_3200_:
{
lean_object* v___x_3212_; lean_object* v___x_3213_; 
v___x_3212_ = l_Array_append___redArg(v___x_2984_, v___y_3211_);
lean_dec_ref(v___y_3211_);
lean_inc(v___y_3210_);
v___x_3213_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3213_, 0, v___y_3210_);
lean_ctor_set(v___x_3213_, 1, v___x_2983_);
lean_ctor_set(v___x_3213_, 2, v___x_3212_);
if (lean_obj_tag(v___y_3204_) == 1)
{
lean_object* v_val_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; 
v_val_3214_ = lean_ctor_get(v___y_3204_, 0);
lean_inc(v_val_3214_);
lean_dec_ref_known(v___y_3204_, 1);
v___x_3215_ = l_Lean_SourceInfo_fromRef(v_val_3214_, v___x_2890_);
lean_dec(v_val_3214_);
v___x_3216_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_3217_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3217_, 0, v___x_3215_);
lean_ctor_set(v___x_3217_, 1, v___x_3216_);
v___x_3218_ = l_Array_mkArray1___redArg(v___x_3217_);
v___y_3175_ = v___x_3213_;
v___y_3176_ = v___y_3201_;
v___y_3177_ = v___y_3203_;
v___y_3178_ = v___y_3202_;
v___y_3179_ = v___y_3205_;
v___y_3180_ = v___y_3208_;
v___y_3181_ = v___y_3207_;
v___y_3182_ = v___y_3206_;
v___y_3183_ = v___y_3209_;
v___y_3184_ = v___y_3210_;
v___y_3185_ = v___x_3218_;
goto v___jp_3174_;
}
else
{
lean_object* v___x_3219_; 
lean_dec(v___y_3204_);
v___x_3219_ = lean_mk_empty_array_with_capacity(v___x_2889_);
v___y_3175_ = v___x_3213_;
v___y_3176_ = v___y_3201_;
v___y_3177_ = v___y_3203_;
v___y_3178_ = v___y_3202_;
v___y_3179_ = v___y_3205_;
v___y_3180_ = v___y_3208_;
v___y_3181_ = v___y_3207_;
v___y_3182_ = v___y_3206_;
v___y_3183_ = v___y_3209_;
v___y_3184_ = v___y_3210_;
v___y_3185_ = v___x_3219_;
goto v___jp_3174_;
}
}
v___jp_3220_:
{
lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3234_ = l_Array_append___redArg(v___x_2984_, v___y_3233_);
lean_dec_ref(v___y_3233_);
lean_inc_n(v___y_3228_, 3);
v___x_3235_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3235_, 0, v___y_3228_);
lean_ctor_set(v___x_3235_, 1, v___x_2983_);
lean_ctor_set(v___x_3235_, 2, v___x_3234_);
v___x_3236_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__6));
v___x_3237_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3237_, 0, v___y_3228_);
lean_ctor_set(v___x_3237_, 1, v___x_3236_);
v___x_3238_ = l_Lean_Syntax_node6(v___y_3228_, v___y_3222_, v___y_3221_, v___y_3225_, v___y_3227_, v___x_3235_, v___x_3237_, v___y_3224_);
lean_inc(v___y_3232_);
v___x_3239_ = l_Lean_Syntax_node4(v___y_3228_, v___y_3223_, v___y_3231_, v___y_3232_, v___y_3232_, v___x_3238_);
v___y_2948_ = v___y_3229_;
v_stx_2949_ = v___x_3239_;
v___y_2950_ = v___y_3230_;
v___y_2951_ = v___y_3226_;
goto v___jp_2947_;
}
v___jp_3240_:
{
lean_object* v___x_3254_; lean_object* v___x_3255_; 
v___x_3254_ = l_Array_append___redArg(v___x_2984_, v___y_3253_);
lean_dec_ref(v___y_3253_);
lean_inc(v___y_3248_);
v___x_3255_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3255_, 0, v___y_3248_);
lean_ctor_set(v___x_3255_, 1, v___x_2983_);
lean_ctor_set(v___x_3255_, 2, v___x_3254_);
if (lean_obj_tag(v___y_3244_) == 1)
{
lean_object* v_val_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; 
lean_dec(v___x_2889_);
v_val_3256_ = lean_ctor_get(v___y_3244_, 0);
lean_inc(v_val_3256_);
lean_dec_ref_known(v___y_3244_, 1);
v___x_3257_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_3258_ = l_Lean_Name_mkStr4(v___x_2886_, v___x_2887_, v___x_2888_, v___x_3257_);
v___x_3259_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_3248_, 4);
v___x_3260_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3260_, 0, v___y_3248_);
lean_ctor_set(v___x_3260_, 1, v___x_3259_);
v___x_3261_ = l_Array_append___redArg(v___x_2984_, v_val_3256_);
lean_dec(v_val_3256_);
v___x_3262_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3262_, 0, v___y_3248_);
lean_ctor_set(v___x_3262_, 1, v___x_2983_);
lean_ctor_set(v___x_3262_, 2, v___x_3261_);
v___x_3263_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_3264_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3264_, 0, v___y_3248_);
lean_ctor_set(v___x_3264_, 1, v___x_3263_);
v___x_3265_ = l_Lean_Syntax_node3(v___y_3248_, v___x_3258_, v___x_3260_, v___x_3262_, v___x_3264_);
v___x_3266_ = l_Array_mkArray1___redArg(v___x_3265_);
v___y_3221_ = v___y_3241_;
v___y_3222_ = v___y_3242_;
v___y_3223_ = v___y_3243_;
v___y_3224_ = v___y_3245_;
v___y_3225_ = v___y_3246_;
v___y_3226_ = v___y_3247_;
v___y_3227_ = v___x_3255_;
v___y_3228_ = v___y_3248_;
v___y_3229_ = v___y_3249_;
v___y_3230_ = v___y_3250_;
v___y_3231_ = v___y_3251_;
v___y_3232_ = v___y_3252_;
v___y_3233_ = v___x_3266_;
goto v___jp_3220_;
}
else
{
lean_object* v___x_3267_; 
lean_dec(v___y_3244_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v___x_2886_);
v___x_3267_ = lean_mk_empty_array_with_capacity(v___x_2889_);
lean_dec(v___x_2889_);
v___y_3221_ = v___y_3241_;
v___y_3222_ = v___y_3242_;
v___y_3223_ = v___y_3243_;
v___y_3224_ = v___y_3245_;
v___y_3225_ = v___y_3246_;
v___y_3226_ = v___y_3247_;
v___y_3227_ = v___x_3255_;
v___y_3228_ = v___y_3248_;
v___y_3229_ = v___y_3249_;
v___y_3230_ = v___y_3250_;
v___y_3231_ = v___y_3251_;
v___y_3232_ = v___y_3252_;
v___y_3233_ = v___x_3267_;
goto v___jp_3220_;
}
}
v___jp_3268_:
{
lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___x_3282_ = l_Array_append___redArg(v___x_2984_, v___y_3281_);
lean_dec_ref(v___y_3281_);
lean_inc(v___y_3276_);
v___x_3283_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3283_, 0, v___y_3276_);
lean_ctor_set(v___x_3283_, 1, v___x_2983_);
lean_ctor_set(v___x_3283_, 2, v___x_3282_);
if (lean_obj_tag(v___y_3274_) == 1)
{
lean_object* v_val_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; 
v_val_3284_ = lean_ctor_get(v___y_3274_, 0);
lean_inc(v_val_3284_);
lean_dec_ref_known(v___y_3274_, 1);
v___x_3285_ = l_Lean_SourceInfo_fromRef(v_val_3284_, v___x_2890_);
lean_dec(v_val_3284_);
v___x_3286_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_3287_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3287_, 0, v___x_3285_);
lean_ctor_set(v___x_3287_, 1, v___x_3286_);
v___x_3288_ = l_Array_mkArray1___redArg(v___x_3287_);
v___y_3241_ = v___y_3269_;
v___y_3242_ = v___y_3270_;
v___y_3243_ = v___y_3271_;
v___y_3244_ = v___y_3272_;
v___y_3245_ = v___y_3273_;
v___y_3246_ = v___x_3283_;
v___y_3247_ = v___y_3275_;
v___y_3248_ = v___y_3276_;
v___y_3249_ = v___y_3277_;
v___y_3250_ = v___y_3278_;
v___y_3251_ = v___y_3279_;
v___y_3252_ = v___y_3280_;
v___y_3253_ = v___x_3288_;
goto v___jp_3240_;
}
else
{
lean_object* v___x_3289_; 
lean_dec(v___y_3274_);
v___x_3289_ = lean_mk_empty_array_with_capacity(v___x_2889_);
v___y_3241_ = v___y_3269_;
v___y_3242_ = v___y_3270_;
v___y_3243_ = v___y_3271_;
v___y_3244_ = v___y_3272_;
v___y_3245_ = v___y_3273_;
v___y_3246_ = v___x_3283_;
v___y_3247_ = v___y_3275_;
v___y_3248_ = v___y_3276_;
v___y_3249_ = v___y_3277_;
v___y_3250_ = v___y_3278_;
v___y_3251_ = v___y_3279_;
v___y_3252_ = v___y_3280_;
v___y_3253_ = v___x_3289_;
goto v___jp_3240_;
}
}
v___jp_3290_:
{
if (v___y_3297_ == 0)
{
if (v_useReducible_2893_ == 0)
{
lean_dec(v___x_2892_);
lean_dec(v___x_2891_);
if (lean_obj_tag(v___y_3302_) == 0)
{
lean_dec(v___y_3305_);
lean_dec(v___y_3295_);
lean_dec(v___y_3293_);
lean_dec(v___y_3291_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___f_2894_);
lean_dec(v___x_2889_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v___x_2886_);
v___y_2954_ = v___y_3301_;
v___y_2955_ = v___y_3298_;
v___y_2956_ = v___y_3292_;
v___y_2957_ = v___y_3299_;
v___y_2958_ = v___y_3300_;
v___y_2959_ = v___y_3294_;
v___y_2960_ = v___y_3303_;
v___y_2961_ = v___y_3304_;
v___y_2962_ = v___y_3296_;
goto v___jp_2953_;
}
else
{
lean_object* v_val_3306_; lean_object* v___x_3307_; 
v_val_3306_ = lean_ctor_get(v___y_3302_, 0);
lean_inc(v_val_3306_);
lean_dec_ref_known(v___y_3302_, 1);
lean_inc(v___y_3296_);
lean_inc_ref(v___y_3304_);
v___x_3307_ = lean_apply_9(v___f_2894_, v___y_3298_, v___y_3292_, v___y_3299_, v___y_3300_, v___y_3294_, v___y_3303_, v___y_3304_, v___y_3296_, lean_box(0));
if (lean_obj_tag(v___x_3307_) == 0)
{
lean_object* v_a_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; 
v_a_3308_ = lean_ctor_get(v___x_3307_, 0);
lean_inc_n(v_a_3308_, 3);
lean_dec_ref_known(v___x_3307_, 1);
v___x_3309_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__7));
lean_inc_ref_n(v___x_2888_, 2);
lean_inc_ref_n(v___x_2887_, 2);
lean_inc_ref_n(v___x_2886_, 2);
v___x_3310_ = l_Lean_Name_mkStr4(v___x_2886_, v___x_2887_, v___x_2888_, v___x_3309_);
v___x_3311_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3311_, 0, v_a_3308_);
lean_ctor_set(v___x_3311_, 1, v___x_2895_);
v___x_3312_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3312_, 0, v_a_3308_);
lean_ctor_set(v___x_3312_, 1, v___x_2983_);
lean_ctor_set(v___x_3312_, 2, v___x_2984_);
v___x_3313_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__8));
v___x_3314_ = l_Lean_Name_mkStr4(v___x_2886_, v___x_2887_, v___x_2888_, v___x_3313_);
if (lean_obj_tag(v___y_3305_) == 0)
{
lean_object* v___x_3315_; 
v___x_3315_ = lean_mk_empty_array_with_capacity(v___x_2889_);
v___y_3269_ = v___y_3291_;
v___y_3270_ = v___x_3314_;
v___y_3271_ = v___x_3310_;
v___y_3272_ = v___y_3293_;
v___y_3273_ = v_val_3306_;
v___y_3274_ = v___y_3295_;
v___y_3275_ = v___y_3296_;
v___y_3276_ = v_a_3308_;
v___y_3277_ = v___y_3301_;
v___y_3278_ = v___y_3304_;
v___y_3279_ = v___x_3311_;
v___y_3280_ = v___x_3312_;
v___y_3281_ = v___x_3315_;
goto v___jp_3268_;
}
else
{
lean_object* v_val_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
v_val_3316_ = lean_ctor_get(v___y_3305_, 0);
lean_inc(v_val_3316_);
lean_dec_ref_known(v___y_3305_, 1);
v___x_3317_ = lean_mk_empty_array_with_capacity(v___x_2889_);
v___x_3318_ = lean_array_push(v___x_3317_, v_val_3316_);
v___y_3269_ = v___y_3291_;
v___y_3270_ = v___x_3314_;
v___y_3271_ = v___x_3310_;
v___y_3272_ = v___y_3293_;
v___y_3273_ = v_val_3306_;
v___y_3274_ = v___y_3295_;
v___y_3275_ = v___y_3296_;
v___y_3276_ = v_a_3308_;
v___y_3277_ = v___y_3301_;
v___y_3278_ = v___y_3304_;
v___y_3279_ = v___x_3311_;
v___y_3280_ = v___x_3312_;
v___y_3281_ = v___x_3318_;
goto v___jp_3268_;
}
}
else
{
lean_object* v_a_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3326_; 
lean_dec(v_val_3306_);
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
lean_dec_ref(v___y_3301_);
lean_dec(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec(v___y_3293_);
lean_dec(v___y_3291_);
lean_dec_ref(v___x_2895_);
lean_dec(v___x_2889_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v___x_2886_);
lean_dec(v_tk_2885_);
v_a_3319_ = lean_ctor_get(v___x_3307_, 0);
v_isSharedCheck_3326_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3321_ = v___x_3307_;
v_isShared_3322_ = v_isSharedCheck_3326_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_a_3319_);
lean_dec(v___x_3307_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3326_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v___x_3324_; 
if (v_isShared_3322_ == 0)
{
v___x_3324_ = v___x_3321_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v_a_3319_);
v___x_3324_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
return v___x_3324_;
}
}
}
}
}
else
{
lean_object* v___x_3327_; 
lean_inc(v___y_3296_);
lean_inc_ref(v___y_3304_);
v___x_3327_ = lean_apply_9(v___f_2894_, v___y_3298_, v___y_3292_, v___y_3299_, v___y_3300_, v___y_3294_, v___y_3303_, v___y_3304_, v___y_3296_, lean_box(0));
if (lean_obj_tag(v___x_3327_) == 0)
{
lean_object* v_a_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
v_a_3328_ = lean_ctor_get(v___x_3327_, 0);
lean_inc_n(v_a_3328_, 3);
lean_dec_ref_known(v___x_3327_, 1);
v___x_3329_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3329_, 0, v_a_3328_);
lean_ctor_set(v___x_3329_, 1, v___x_2895_);
v___x_3330_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3330_, 0, v_a_3328_);
lean_ctor_set(v___x_3330_, 1, v___x_2983_);
lean_ctor_set(v___x_3330_, 2, v___x_2984_);
if (lean_obj_tag(v___y_3305_) == 0)
{
lean_object* v___x_3331_; 
v___x_3331_ = lean_mk_empty_array_with_capacity(v___x_2889_);
v___y_3201_ = v___y_3291_;
v___y_3202_ = v___x_3330_;
v___y_3203_ = v___y_3293_;
v___y_3204_ = v___y_3295_;
v___y_3205_ = v___y_3301_;
v___y_3206_ = v___y_3302_;
v___y_3207_ = v___x_3329_;
v___y_3208_ = v___y_3304_;
v___y_3209_ = v___y_3296_;
v___y_3210_ = v_a_3328_;
v___y_3211_ = v___x_3331_;
goto v___jp_3200_;
}
else
{
lean_object* v_val_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; 
v_val_3332_ = lean_ctor_get(v___y_3305_, 0);
lean_inc(v_val_3332_);
lean_dec_ref_known(v___y_3305_, 1);
v___x_3333_ = lean_mk_empty_array_with_capacity(v___x_2889_);
v___x_3334_ = lean_array_push(v___x_3333_, v_val_3332_);
v___y_3201_ = v___y_3291_;
v___y_3202_ = v___x_3330_;
v___y_3203_ = v___y_3293_;
v___y_3204_ = v___y_3295_;
v___y_3205_ = v___y_3301_;
v___y_3206_ = v___y_3302_;
v___y_3207_ = v___x_3329_;
v___y_3208_ = v___y_3304_;
v___y_3209_ = v___y_3296_;
v___y_3210_ = v_a_3328_;
v___y_3211_ = v___x_3334_;
goto v___jp_3200_;
}
}
else
{
lean_object* v_a_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3342_; 
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
lean_dec(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec(v___y_3293_);
lean_dec(v___y_3291_);
lean_dec_ref(v___x_2895_);
lean_dec(v___x_2892_);
lean_dec(v___x_2891_);
lean_dec(v___x_2889_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v___x_2886_);
lean_dec(v_tk_2885_);
v_a_3335_ = lean_ctor_get(v___x_3327_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3327_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3337_ = v___x_3327_;
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_a_3335_);
lean_dec(v___x_3327_);
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
else
{
lean_dec(v___x_2892_);
if (v_useReducible_2893_ == 0)
{
lean_dec(v___x_2891_);
if (lean_obj_tag(v___y_3302_) == 0)
{
lean_dec(v___y_3305_);
lean_dec(v___y_3295_);
lean_dec(v___y_3293_);
lean_dec(v___y_3291_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___f_2894_);
lean_dec(v___x_2889_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v___x_2886_);
v___y_2954_ = v___y_3301_;
v___y_2955_ = v___y_3298_;
v___y_2956_ = v___y_3292_;
v___y_2957_ = v___y_3299_;
v___y_2958_ = v___y_3300_;
v___y_2959_ = v___y_3294_;
v___y_2960_ = v___y_3303_;
v___y_2961_ = v___y_3304_;
v___y_2962_ = v___y_3296_;
goto v___jp_2953_;
}
else
{
lean_object* v_val_3343_; lean_object* v___x_3344_; 
v_val_3343_ = lean_ctor_get(v___y_3302_, 0);
lean_inc(v_val_3343_);
lean_dec_ref_known(v___y_3302_, 1);
lean_inc(v___y_3296_);
lean_inc_ref(v___y_3304_);
v___x_3344_ = lean_apply_9(v___f_2894_, v___y_3298_, v___y_3292_, v___y_3299_, v___y_3300_, v___y_3294_, v___y_3303_, v___y_3304_, v___y_3296_, lean_box(0));
if (lean_obj_tag(v___x_3344_) == 0)
{
lean_object* v_a_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; 
v_a_3345_ = lean_ctor_get(v___x_3344_, 0);
lean_inc_n(v_a_3345_, 5);
lean_dec_ref_known(v___x_3344_, 1);
v___x_3346_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__7));
lean_inc_ref_n(v___x_2888_, 2);
lean_inc_ref_n(v___x_2887_, 2);
lean_inc_ref_n(v___x_2886_, 2);
v___x_3347_ = l_Lean_Name_mkStr4(v___x_2886_, v___x_2887_, v___x_2888_, v___x_3346_);
v___x_3348_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3348_, 0, v_a_3345_);
lean_ctor_set(v___x_3348_, 1, v___x_2895_);
v___x_3349_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3349_, 0, v_a_3345_);
lean_ctor_set(v___x_3349_, 1, v___x_2983_);
lean_ctor_set(v___x_3349_, 2, v___x_2984_);
v___x_3350_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__9));
v___x_3351_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3351_, 0, v_a_3345_);
lean_ctor_set(v___x_3351_, 1, v___x_3350_);
v___x_3352_ = l_Lean_Syntax_node1(v_a_3345_, v___x_2983_, v___x_3351_);
v___x_3353_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__8));
v___x_3354_ = l_Lean_Name_mkStr4(v___x_2886_, v___x_2887_, v___x_2888_, v___x_3353_);
if (lean_obj_tag(v___y_3305_) == 0)
{
lean_object* v___x_3355_; 
v___x_3355_ = lean_mk_empty_array_with_capacity(v___x_2889_);
v___y_3117_ = v___y_3291_;
v___y_3118_ = v___y_3293_;
v___y_3119_ = v_val_3343_;
v___y_3120_ = v___y_3295_;
v___y_3121_ = v___y_3296_;
v___y_3122_ = v___x_3352_;
v___y_3123_ = v___x_3354_;
v___y_3124_ = v___x_3347_;
v___y_3125_ = v___x_3348_;
v___y_3126_ = v___y_3301_;
v___y_3127_ = v_a_3345_;
v___y_3128_ = v___y_3304_;
v___y_3129_ = v___x_3349_;
v___y_3130_ = v___x_3355_;
goto v___jp_3116_;
}
else
{
lean_object* v_val_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; 
v_val_3356_ = lean_ctor_get(v___y_3305_, 0);
lean_inc(v_val_3356_);
lean_dec_ref_known(v___y_3305_, 1);
v___x_3357_ = lean_mk_empty_array_with_capacity(v___x_2889_);
v___x_3358_ = lean_array_push(v___x_3357_, v_val_3356_);
v___y_3117_ = v___y_3291_;
v___y_3118_ = v___y_3293_;
v___y_3119_ = v_val_3343_;
v___y_3120_ = v___y_3295_;
v___y_3121_ = v___y_3296_;
v___y_3122_ = v___x_3352_;
v___y_3123_ = v___x_3354_;
v___y_3124_ = v___x_3347_;
v___y_3125_ = v___x_3348_;
v___y_3126_ = v___y_3301_;
v___y_3127_ = v_a_3345_;
v___y_3128_ = v___y_3304_;
v___y_3129_ = v___x_3349_;
v___y_3130_ = v___x_3358_;
goto v___jp_3116_;
}
}
else
{
lean_object* v_a_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3366_; 
lean_dec(v_val_3343_);
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
lean_dec_ref(v___y_3301_);
lean_dec(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec(v___y_3293_);
lean_dec(v___y_3291_);
lean_dec_ref(v___x_2895_);
lean_dec(v___x_2889_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v___x_2886_);
lean_dec(v_tk_2885_);
v_a_3359_ = lean_ctor_get(v___x_3344_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3344_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3361_ = v___x_3344_;
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_a_3359_);
lean_dec(v___x_3344_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3364_; 
if (v_isShared_3362_ == 0)
{
v___x_3364_ = v___x_3361_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_a_3359_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
}
}
}
}
}
else
{
lean_object* v___x_3367_; 
lean_dec_ref(v___x_2895_);
lean_inc(v___y_3296_);
lean_inc_ref(v___y_3304_);
v___x_3367_ = lean_apply_9(v___f_2894_, v___y_3298_, v___y_3292_, v___y_3299_, v___y_3300_, v___y_3294_, v___y_3303_, v___y_3304_, v___y_3296_, lean_box(0));
if (lean_obj_tag(v___x_3367_) == 0)
{
lean_object* v_a_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; 
v_a_3368_ = lean_ctor_get(v___x_3367_, 0);
lean_inc_n(v_a_3368_, 2);
lean_dec_ref_known(v___x_3367_, 1);
v___x_3369_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__10));
lean_inc_ref(v___x_2888_);
lean_inc_ref(v___x_2887_);
lean_inc_ref(v___x_2886_);
v___x_3370_ = l_Lean_Name_mkStr4(v___x_2886_, v___x_2887_, v___x_2888_, v___x_3369_);
v___x_3371_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__11));
v___x_3372_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3372_, 0, v_a_3368_);
lean_ctor_set(v___x_3372_, 1, v___x_3371_);
if (lean_obj_tag(v___y_3305_) == 0)
{
lean_object* v___x_3373_; 
v___x_3373_ = lean_mk_empty_array_with_capacity(v___x_2889_);
v___y_3047_ = v___y_3291_;
v___y_3048_ = v___x_3372_;
v___y_3049_ = v_a_3368_;
v___y_3050_ = v___y_3293_;
v___y_3051_ = v___y_3295_;
v___y_3052_ = v___y_3301_;
v___y_3053_ = v___y_3302_;
v___y_3054_ = v___x_3370_;
v___y_3055_ = v___y_3304_;
v___y_3056_ = v___y_3296_;
v___y_3057_ = v___x_3373_;
goto v___jp_3046_;
}
else
{
lean_object* v_val_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; 
v_val_3374_ = lean_ctor_get(v___y_3305_, 0);
lean_inc(v_val_3374_);
lean_dec_ref_known(v___y_3305_, 1);
v___x_3375_ = lean_mk_empty_array_with_capacity(v___x_2889_);
v___x_3376_ = lean_array_push(v___x_3375_, v_val_3374_);
v___y_3047_ = v___y_3291_;
v___y_3048_ = v___x_3372_;
v___y_3049_ = v_a_3368_;
v___y_3050_ = v___y_3293_;
v___y_3051_ = v___y_3295_;
v___y_3052_ = v___y_3301_;
v___y_3053_ = v___y_3302_;
v___y_3054_ = v___x_3370_;
v___y_3055_ = v___y_3304_;
v___y_3056_ = v___y_3296_;
v___y_3057_ = v___x_3376_;
goto v___jp_3046_;
}
}
else
{
lean_object* v_a_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3384_; 
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
lean_dec(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec(v___y_3293_);
lean_dec(v___y_3291_);
lean_dec(v___x_2891_);
lean_dec(v___x_2889_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v___x_2886_);
lean_dec(v_tk_2885_);
v_a_3377_ = lean_ctor_get(v___x_3367_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v___x_3367_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3379_ = v___x_3367_;
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_a_3377_);
lean_dec(v___x_3367_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3382_; 
if (v_isShared_3380_ == 0)
{
v___x_3382_ = v___x_3379_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_a_3377_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
}
}
}
v___jp_3385_:
{
lean_object* v___x_3402_; lean_object* v___x_3403_; uint8_t v___x_3404_; 
v___x_3402_ = lean_unsigned_to_nat(5u);
v___x_3403_ = l_Lean_Syntax_getArg(v___y_3391_, v___x_3402_);
lean_dec(v___y_3391_);
v___x_3404_ = l_Lean_Syntax_matchesNull(v___x_3403_, v___x_2889_);
if (v___x_3404_ == 0)
{
lean_object* v___x_3405_; lean_object* v___x_3406_; 
lean_dec(v_args_3393_);
lean_dec(v___y_3392_);
lean_dec(v___y_3389_);
lean_dec(v___y_3388_);
lean_dec(v___y_3386_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___f_2894_);
lean_dec(v___x_2892_);
lean_dec(v___x_2891_);
lean_dec(v___x_2889_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v___x_2886_);
v___x_3405_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3406_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3405_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_object* v_a_3407_; 
v_a_3407_ = lean_ctor_get(v___x_3406_, 0);
lean_inc(v_a_3407_);
lean_dec_ref_known(v___x_3406_, 1);
v___y_2948_ = v___y_3390_;
v_stx_2949_ = v_a_3407_;
v___y_2950_ = v___y_3400_;
v___y_2951_ = v___y_3401_;
goto v___jp_2947_;
}
else
{
lean_object* v_a_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3415_; 
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec_ref(v___y_3390_);
lean_dec(v_tk_2885_);
v_a_3408_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3410_ = v___x_3406_;
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_a_3408_);
lean_dec(v___x_3406_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3413_; 
if (v_isShared_3411_ == 0)
{
v___x_3413_ = v___x_3410_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_a_3408_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
}
}
}
}
else
{
lean_object* v___x_3416_; 
v___x_3416_ = l_Lean_Syntax_getOptional_x3f(v___y_3388_);
lean_dec(v___y_3388_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v___x_3417_; 
v___x_3417_ = lean_box(0);
v___y_3291_ = v___y_3386_;
v___y_3292_ = v___y_3395_;
v___y_3293_ = v_args_3393_;
v___y_3294_ = v___y_3398_;
v___y_3295_ = v___y_3389_;
v___y_3296_ = v___y_3401_;
v___y_3297_ = v___y_3387_;
v___y_3298_ = v___y_3394_;
v___y_3299_ = v___y_3396_;
v___y_3300_ = v___y_3397_;
v___y_3301_ = v___y_3390_;
v___y_3302_ = v___y_3392_;
v___y_3303_ = v___y_3399_;
v___y_3304_ = v___y_3400_;
v___y_3305_ = v___x_3417_;
goto v___jp_3290_;
}
else
{
lean_object* v_val_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3425_; 
v_val_3418_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3420_ = v___x_3416_;
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_val_3418_);
lean_dec(v___x_3416_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3423_; 
if (v_isShared_3421_ == 0)
{
v___x_3423_ = v___x_3420_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_val_3418_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
v___y_3291_ = v___y_3386_;
v___y_3292_ = v___y_3395_;
v___y_3293_ = v_args_3393_;
v___y_3294_ = v___y_3398_;
v___y_3295_ = v___y_3389_;
v___y_3296_ = v___y_3401_;
v___y_3297_ = v___y_3387_;
v___y_3298_ = v___y_3394_;
v___y_3299_ = v___y_3396_;
v___y_3300_ = v___y_3397_;
v___y_3301_ = v___y_3390_;
v___y_3302_ = v___y_3392_;
v___y_3303_ = v___y_3399_;
v___y_3304_ = v___y_3400_;
v___y_3305_ = v___x_3423_;
goto v___jp_3290_;
}
}
}
}
}
v___jp_3426_:
{
lean_object* v___x_3442_; uint8_t v___x_3443_; 
v___x_3442_ = l_Lean_Syntax_getArg(v___y_3432_, v___x_2896_);
v___x_3443_ = l_Lean_Syntax_isNone(v___x_3442_);
if (v___x_3443_ == 0)
{
uint8_t v___x_3444_; 
lean_inc(v___x_3442_);
v___x_3444_ = l_Lean_Syntax_matchesNull(v___x_3442_, v___x_2897_);
if (v___x_3444_ == 0)
{
lean_object* v___x_3445_; lean_object* v___x_3446_; 
lean_dec(v___x_3442_);
lean_dec(v_only_3433_);
lean_dec(v___y_3432_);
lean_dec(v___y_3431_);
lean_dec(v___y_3429_);
lean_dec(v___y_3427_);
lean_dec(v___x_2898_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___f_2894_);
lean_dec(v___x_2892_);
lean_dec(v___x_2891_);
lean_dec(v___x_2889_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v___x_2886_);
v___x_3445_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3446_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3445_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_);
lean_dec(v___y_3439_);
lean_dec_ref(v___y_3438_);
lean_dec(v___y_3437_);
lean_dec_ref(v___y_3436_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
if (lean_obj_tag(v___x_3446_) == 0)
{
lean_object* v_a_3447_; 
v_a_3447_ = lean_ctor_get(v___x_3446_, 0);
lean_inc(v_a_3447_);
lean_dec_ref_known(v___x_3446_, 1);
v___y_2948_ = v___y_3430_;
v_stx_2949_ = v_a_3447_;
v___y_2950_ = v___y_3440_;
v___y_2951_ = v___y_3441_;
goto v___jp_2947_;
}
else
{
lean_object* v_a_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3455_; 
lean_dec(v___y_3441_);
lean_dec_ref(v___y_3440_);
lean_dec_ref(v___y_3430_);
lean_dec(v_tk_2885_);
v_a_3448_ = lean_ctor_get(v___x_3446_, 0);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3446_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3450_ = v___x_3446_;
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_a_3448_);
lean_dec(v___x_3446_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3453_; 
if (v_isShared_3451_ == 0)
{
v___x_3453_ = v___x_3450_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_a_3448_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
return v___x_3453_;
}
}
}
}
else
{
lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; 
v___x_3456_ = l_Lean_Syntax_getArg(v___x_3442_, v___x_2898_);
lean_dec(v___x_2898_);
lean_dec(v___x_3442_);
v___x_3457_ = l_Lean_Syntax_getArgs(v___x_3456_);
lean_dec(v___x_3456_);
v___x_3458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3457_);
v___y_3386_ = v___y_3427_;
v___y_3387_ = v___y_3428_;
v___y_3388_ = v___y_3429_;
v___y_3389_ = v_only_3433_;
v___y_3390_ = v___y_3430_;
v___y_3391_ = v___y_3432_;
v___y_3392_ = v___y_3431_;
v_args_3393_ = v___x_3458_;
v___y_3394_ = v___y_3434_;
v___y_3395_ = v___y_3435_;
v___y_3396_ = v___y_3436_;
v___y_3397_ = v___y_3437_;
v___y_3398_ = v___y_3438_;
v___y_3399_ = v___y_3439_;
v___y_3400_ = v___y_3440_;
v___y_3401_ = v___y_3441_;
goto v___jp_3385_;
}
}
else
{
lean_object* v___x_3459_; 
lean_dec(v___x_3442_);
lean_dec(v___x_2898_);
v___x_3459_ = lean_box(0);
v___y_3386_ = v___y_3427_;
v___y_3387_ = v___y_3428_;
v___y_3388_ = v___y_3429_;
v___y_3389_ = v_only_3433_;
v___y_3390_ = v___y_3430_;
v___y_3391_ = v___y_3432_;
v___y_3392_ = v___y_3431_;
v_args_3393_ = v___x_3459_;
v___y_3394_ = v___y_3434_;
v___y_3395_ = v___y_3435_;
v___y_3396_ = v___y_3436_;
v___y_3397_ = v___y_3437_;
v___y_3398_ = v___y_3438_;
v___y_3399_ = v___y_3439_;
v___y_3400_ = v___y_3440_;
v___y_3401_ = v___y_3441_;
goto v___jp_3385_;
}
}
v___jp_3460_:
{
lean_object* v_usedTheorems_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; 
v_usedTheorems_3465_ = lean_ctor_get(v___y_3463_, 0);
v___x_3466_ = l_Lean_Syntax_unsetTrailing(v___y_3462_);
v___x_3467_ = l_Lean_Elab_Tactic_mkSimpOnly(v___x_3466_, v_usedTheorems_3465_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
if (lean_obj_tag(v___x_3467_) == 0)
{
lean_object* v_a_3468_; uint8_t v___x_3469_; 
v_a_3468_ = lean_ctor_get(v___x_3467_, 0);
lean_inc_n(v_a_3468_, 2);
lean_dec_ref_known(v___x_3467_, 1);
v___x_3469_ = l_Lean_Syntax_isOfKind(v_a_3468_, v___x_2981_);
lean_dec(v___x_2981_);
if (v___x_3469_ == 0)
{
lean_object* v___x_3470_; lean_object* v___x_3471_; 
lean_inc(v_ref_2977_);
lean_dec(v_a_3468_);
lean_dec(v___y_3464_);
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
v___x_3470_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3471_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3470_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
if (lean_obj_tag(v___x_3471_) == 0)
{
lean_object* v_a_3472_; 
v_a_3472_ = lean_ctor_get(v___x_3471_, 0);
lean_inc(v_a_3472_);
lean_dec_ref_known(v___x_3471_, 1);
v___y_2925_ = v___y_3463_;
v_stx_2926_ = v_a_3472_;
v___y_2927_ = v___y_2917_;
v_ref_2928_ = v_ref_2977_;
v___y_2929_ = v___y_2918_;
goto v___jp_2924_;
}
else
{
lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3480_; 
lean_dec_ref(v___y_3463_);
lean_dec(v_ref_2977_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec(v_tk_2885_);
v_a_3473_ = lean_ctor_get(v___x_3471_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3471_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3475_ = v___x_3471_;
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3471_);
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
else
{
lean_object* v___x_3481_; uint8_t v___x_3482_; 
v___x_3481_ = l_Lean_Syntax_getArg(v_a_3468_, v___x_2898_);
lean_inc(v___x_3481_);
v___x_3482_ = l_Lean_Syntax_isOfKind(v___x_3481_, v___x_2899_);
if (v___x_3482_ == 0)
{
lean_object* v___x_3483_; lean_object* v___x_3484_; 
lean_inc(v_ref_2977_);
lean_dec(v___x_3481_);
lean_dec(v_a_3468_);
lean_dec(v___y_3464_);
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
v___x_3483_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3484_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3483_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
if (lean_obj_tag(v___x_3484_) == 0)
{
lean_object* v_a_3485_; 
v_a_3485_ = lean_ctor_get(v___x_3484_, 0);
lean_inc(v_a_3485_);
lean_dec_ref_known(v___x_3484_, 1);
v___y_2925_ = v___y_3463_;
v_stx_2926_ = v_a_3485_;
v___y_2927_ = v___y_2917_;
v_ref_2928_ = v_ref_2977_;
v___y_2929_ = v___y_2918_;
goto v___jp_2924_;
}
else
{
lean_object* v_a_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3493_; 
lean_dec_ref(v___y_3463_);
lean_dec(v_ref_2977_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec(v_tk_2885_);
v_a_3486_ = lean_ctor_get(v___x_3484_, 0);
v_isSharedCheck_3493_ = !lean_is_exclusive(v___x_3484_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3488_ = v___x_3484_;
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_a_3486_);
lean_dec(v___x_3484_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___x_3491_; 
if (v_isShared_3489_ == 0)
{
v___x_3491_ = v___x_3488_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v_a_3486_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
return v___x_3491_;
}
}
}
}
else
{
lean_object* v___x_3494_; lean_object* v___x_3495_; uint8_t v___x_3496_; 
v___x_3494_ = l_Lean_Syntax_getArg(v_a_3468_, v___x_2900_);
lean_dec(v___x_2900_);
v___x_3495_ = l_Lean_Syntax_getArg(v_a_3468_, v___x_2897_);
v___x_3496_ = l_Lean_Syntax_isNone(v___x_3495_);
if (v___x_3496_ == 0)
{
uint8_t v___x_3497_; 
lean_inc(v___x_3495_);
v___x_3497_ = l_Lean_Syntax_matchesNull(v___x_3495_, v___x_2898_);
if (v___x_3497_ == 0)
{
lean_object* v___x_3498_; lean_object* v___x_3499_; 
lean_inc(v_ref_2977_);
lean_dec(v___x_3495_);
lean_dec(v___x_3494_);
lean_dec(v___x_3481_);
lean_dec(v_a_3468_);
lean_dec(v___y_3464_);
lean_dec(v___x_2898_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___f_2894_);
lean_dec(v___x_2892_);
lean_dec(v___x_2891_);
lean_dec(v___x_2889_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v___x_2886_);
v___x_3498_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3499_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3498_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
if (lean_obj_tag(v___x_3499_) == 0)
{
lean_object* v_a_3500_; 
v_a_3500_ = lean_ctor_get(v___x_3499_, 0);
lean_inc(v_a_3500_);
lean_dec_ref_known(v___x_3499_, 1);
v___y_2925_ = v___y_3463_;
v_stx_2926_ = v_a_3500_;
v___y_2927_ = v___y_2917_;
v_ref_2928_ = v_ref_2977_;
v___y_2929_ = v___y_2918_;
goto v___jp_2924_;
}
else
{
lean_object* v_a_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3508_; 
lean_dec_ref(v___y_3463_);
lean_dec(v_ref_2977_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec(v_tk_2885_);
v_a_3501_ = lean_ctor_get(v___x_3499_, 0);
v_isSharedCheck_3508_ = !lean_is_exclusive(v___x_3499_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3503_ = v___x_3499_;
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_a_3501_);
lean_dec(v___x_3499_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___x_3506_; 
if (v_isShared_3504_ == 0)
{
v___x_3506_ = v___x_3503_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_a_3501_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
}
else
{
lean_object* v___x_3509_; lean_object* v___x_3510_; 
v___x_3509_ = l_Lean_Syntax_getArg(v___x_3495_, v___x_2889_);
lean_dec(v___x_3495_);
v___x_3510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3510_, 0, v___x_3509_);
v___y_3427_ = v___x_3481_;
v___y_3428_ = v___y_3461_;
v___y_3429_ = v___x_3494_;
v___y_3430_ = v___y_3463_;
v___y_3431_ = v___y_3464_;
v___y_3432_ = v_a_3468_;
v_only_3433_ = v___x_3510_;
v___y_3434_ = v___y_2911_;
v___y_3435_ = v___y_2912_;
v___y_3436_ = v___y_2913_;
v___y_3437_ = v___y_2914_;
v___y_3438_ = v___y_2915_;
v___y_3439_ = v___y_2916_;
v___y_3440_ = v___y_2917_;
v___y_3441_ = v___y_2918_;
goto v___jp_3426_;
}
}
else
{
lean_object* v___x_3511_; 
lean_dec(v___x_3495_);
v___x_3511_ = lean_box(0);
v___y_3427_ = v___x_3481_;
v___y_3428_ = v___y_3461_;
v___y_3429_ = v___x_3494_;
v___y_3430_ = v___y_3463_;
v___y_3431_ = v___y_3464_;
v___y_3432_ = v_a_3468_;
v_only_3433_ = v___x_3511_;
v___y_3434_ = v___y_2911_;
v___y_3435_ = v___y_2912_;
v___y_3436_ = v___y_2913_;
v___y_3437_ = v___y_2914_;
v___y_3438_ = v___y_2915_;
v___y_3439_ = v___y_2916_;
v___y_3440_ = v___y_2917_;
v___y_3441_ = v___y_2918_;
goto v___jp_3426_;
}
}
}
}
else
{
lean_object* v_a_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3519_; 
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
lean_dec(v___x_2981_);
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
v_a_3512_ = lean_ctor_get(v___x_3467_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3514_ = v___x_3467_;
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_a_3512_);
lean_dec(v___x_3467_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v___x_3517_; 
if (v_isShared_3515_ == 0)
{
v___x_3517_ = v___x_3514_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v_a_3512_);
v___x_3517_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
return v___x_3517_;
}
}
}
}
v___jp_3520_:
{
if (lean_obj_tag(v_usingArg_2901_) == 0)
{
v___y_3461_ = v___y_3521_;
v___y_3462_ = v___y_3522_;
v___y_3463_ = v___y_3523_;
v___y_3464_ = v_usingArg_2901_;
goto v___jp_3460_;
}
else
{
lean_object* v_val_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3532_; 
v_val_3524_ = lean_ctor_get(v_usingArg_2901_, 0);
v_isSharedCheck_3532_ = !lean_is_exclusive(v_usingArg_2901_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3526_ = v_usingArg_2901_;
v_isShared_3527_ = v_isSharedCheck_3532_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_val_3524_);
lean_dec(v_usingArg_2901_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3532_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v___x_3528_; lean_object* v___x_3530_; 
v___x_3528_ = l_Lean_Syntax_unsetTrailing(v_val_3524_);
if (v_isShared_3527_ == 0)
{
lean_ctor_set(v___x_3526_, 0, v___x_3528_);
v___x_3530_ = v___x_3526_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v___x_3528_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
v___y_3461_ = v___y_3521_;
v___y_3462_ = v___y_3522_;
v___y_3463_ = v___y_3523_;
v___y_3464_ = v___x_3530_;
goto v___jp_3460_;
}
}
}
}
v___jp_3533_:
{
if (v___y_3537_ == 0)
{
lean_dec(v___y_3535_);
lean_dec(v___x_2981_);
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
v___y_2921_ = v___y_3536_;
goto v___jp_2920_;
}
else
{
v___y_3521_ = v___y_3534_;
v___y_3522_ = v___y_3535_;
v___y_3523_ = v___y_3536_;
goto v___jp_3520_;
}
}
v___jp_3538_:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___f_3549_; lean_object* v___x_3550_; 
v___x_3544_ = l_Lean_Meta_Simp_Context_setFailIfUnchanged(v___y_3543_, v___x_2978_);
v___x_3545_ = lean_box(v___x_2890_);
v___x_3546_ = lean_box(v___x_2978_);
v___x_3547_ = lean_box(v_useReducible_2893_);
v___x_3548_ = lean_box(v___x_2903_);
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
v___f_3549_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___boxed), 30, 20);
lean_closure_set(v___f_3549_, 0, v___x_2900_);
lean_closure_set(v___f_3549_, 1, v_tk_2885_);
lean_closure_set(v___f_3549_, 2, v___x_2983_);
lean_closure_set(v___f_3549_, 3, v___x_2889_);
lean_closure_set(v___f_3549_, 4, v___x_3544_);
lean_closure_set(v___f_3549_, 5, v___y_3539_);
lean_closure_set(v___f_3549_, 6, v___x_3545_);
lean_closure_set(v___f_3549_, 7, v_usingArg_2901_);
lean_closure_set(v___f_3549_, 8, v___x_3546_);
lean_closure_set(v___f_3549_, 9, v___x_2895_);
lean_closure_set(v___f_3549_, 10, v___x_3547_);
lean_closure_set(v___f_3549_, 11, v___x_3548_);
lean_closure_set(v___f_3549_, 12, v___x_2898_);
lean_closure_set(v___f_3549_, 13, v___f_2894_);
lean_closure_set(v___f_3549_, 14, v___x_2886_);
lean_closure_set(v___f_3549_, 15, v___x_2887_);
lean_closure_set(v___f_3549_, 16, v___x_2888_);
lean_closure_set(v___f_3549_, 17, v___f_2904_);
lean_closure_set(v___f_3549_, 18, v_a_2975_);
lean_closure_set(v___f_3549_, 19, v_usingTk_x3f_2905_);
v___x_3550_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v___y_3542_, v___f_3549_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
lean_dec(v___y_3542_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v_a_3551_; lean_object* v___x_3552_; uint8_t v___x_3553_; 
v_a_3551_ = lean_ctor_get(v___x_3550_, 0);
lean_inc(v_a_3551_);
lean_dec_ref_known(v___x_3550_, 1);
v___x_3552_ = l_Lean_Elab_Tactic_tactic_simp_trace;
v___x_3553_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__3(v_options_2976_, v___x_3552_);
if (v___x_3553_ == 0)
{
if (lean_obj_tag(v_squeeze_2906_) == 0)
{
v___y_3534_ = v___y_3540_;
v___y_3535_ = v___y_3541_;
v___y_3536_ = v_a_3551_;
v___y_3537_ = v___x_3553_;
goto v___jp_3533_;
}
else
{
v___y_3534_ = v___y_3540_;
v___y_3535_ = v___y_3541_;
v___y_3536_ = v_a_3551_;
v___y_3537_ = v___x_2903_;
goto v___jp_3533_;
}
}
else
{
v___y_3521_ = v___y_3540_;
v___y_3522_ = v___y_3541_;
v___y_3523_ = v_a_3551_;
goto v___jp_3520_;
}
}
else
{
lean_object* v_a_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3561_; 
lean_dec(v___y_3541_);
lean_dec(v___x_2981_);
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
v_a_3554_ = lean_ctor_get(v___x_3550_, 0);
v_isSharedCheck_3561_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3556_ = v___x_3550_;
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_a_3554_);
lean_dec(v___x_3550_);
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
v___x_3566_ = l_Array_append___redArg(v___x_2984_, v___y_3565_);
lean_dec_ref(v___y_3565_);
lean_inc_n(v___x_2979_, 2);
v___x_3567_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3567_, 0, v___x_2979_);
lean_ctor_set(v___x_3567_, 1, v___x_2983_);
lean_ctor_set(v___x_3567_, 2, v___x_3566_);
v___x_3568_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3568_, 0, v___x_2979_);
lean_ctor_set(v___x_3568_, 1, v___x_2983_);
lean_ctor_set(v___x_3568_, 2, v___x_2984_);
lean_inc(v___x_2981_);
v___x_3569_ = l_Lean_Syntax_node6(v___x_2979_, v___x_2981_, v___x_2982_, v___x_2902_, v___y_3564_, v___y_3563_, v___x_3567_, v___x_3568_);
v___x_3570_ = 0;
v___x_3571_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__13));
v___x_3572_ = lean_box(v___x_2978_);
v___x_3573_ = lean_box(v___x_3570_);
v___x_3574_ = lean_box(v___x_2978_);
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
v___y_3539_ = v_simprocs_3579_;
v___y_3540_ = v___x_2978_;
v___y_3541_ = v___x_3569_;
v___y_3542_ = v_dischargeWrapper_3580_;
v___y_3543_ = v_ctx_3578_;
goto v___jp_3538_;
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
v___y_3539_ = v_simprocs_3582_;
v___y_3540_ = v___x_2903_;
v___y_3541_ = v___x_3569_;
v___y_3542_ = v_dischargeWrapper_3583_;
v___y_3543_ = v_ctx_3581_;
goto v___jp_3538_;
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
v___y_3539_ = v_simprocs_3585_;
v___y_3540_ = v___x_2903_;
v___y_3541_ = v___x_3569_;
v___y_3542_ = v_dischargeWrapper_3586_;
v___y_3543_ = v___x_3587_;
goto v___jp_3538_;
}
}
}
else
{
lean_object* v_a_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3595_; 
lean_dec(v___x_3569_);
lean_dec(v___x_2981_);
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
v___x_3599_ = l_Array_append___redArg(v___x_2984_, v___y_3598_);
lean_dec_ref(v___y_3598_);
lean_inc(v___x_2979_);
v___x_3600_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3600_, 0, v___x_2979_);
lean_ctor_set(v___x_3600_, 1, v___x_2983_);
lean_ctor_set(v___x_3600_, 2, v___x_3599_);
if (lean_obj_tag(v_args_2908_) == 1)
{
lean_object* v_val_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; 
v_val_3601_ = lean_ctor_get(v_args_2908_, 0);
v___x_3602_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___x_2979_, 3);
v___x_3603_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3603_, 0, v___x_2979_);
lean_ctor_set(v___x_3603_, 1, v___x_3602_);
v___x_3604_ = l_Array_append___redArg(v___x_2984_, v_val_3601_);
v___x_3605_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3605_, 0, v___x_2979_);
lean_ctor_set(v___x_3605_, 1, v___x_2983_);
lean_ctor_set(v___x_3605_, 2, v___x_3604_);
v___x_3606_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_3607_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3607_, 0, v___x_2979_);
lean_ctor_set(v___x_3607_, 1, v___x_3606_);
v___x_3608_ = l_Array_mkArray3___redArg(v___x_3603_, v___x_3605_, v___x_3607_);
v___y_3563_ = v___x_3600_;
v___y_3564_ = v___y_3597_;
v___y_3565_ = v___x_3608_;
goto v___jp_3562_;
}
else
{
lean_object* v___x_3609_; 
v___x_3609_ = lean_mk_empty_array_with_capacity(v___x_2889_);
v___y_3563_ = v___x_3600_;
v___y_3564_ = v___y_3597_;
v___y_3565_ = v___x_3609_;
goto v___jp_3562_;
}
}
v___jp_3610_:
{
lean_object* v___x_3612_; lean_object* v___x_3613_; 
v___x_3612_ = l_Array_append___redArg(v___x_2984_, v___y_3611_);
lean_dec_ref(v___y_3611_);
lean_inc(v___x_2979_);
v___x_3613_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3613_, 0, v___x_2979_);
lean_ctor_set(v___x_3613_, 1, v___x_2983_);
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
v_ref_2952_ = lean_ctor_get(v___y_2950_, 4);
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
uint8_t v___x_96693__boxed_3667_; uint8_t v_useReducible_boxed_3668_; uint8_t v___x_96704__boxed_3669_; lean_object* v_res_3670_; 
v___x_96693__boxed_3667_ = lean_unbox(v___x_3637_);
v_useReducible_boxed_3668_ = lean_unbox(v_useReducible_3640_);
v___x_96704__boxed_3669_ = lean_unbox(v___x_3650_);
v_res_3670_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7(v_tk_3632_, v___x_3633_, v___x_3634_, v___x_3635_, v___x_3636_, v___x_96693__boxed_3667_, v___x_3638_, v___x_3639_, v_useReducible_boxed_3668_, v___f_3641_, v___x_3642_, v___x_3643_, v___x_3644_, v___x_3645_, v___x_3646_, v___x_3647_, v_usingArg_3648_, v___x_3649_, v___x_96704__boxed_3669_, v___f_3651_, v_usingTk_x3f_3652_, v_squeeze_3653_, v_unfold_3654_, v_args_3655_, v_only_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_);
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
lean_object* v___f_3714_; lean_object* v___x_3715_; lean_object* v_tk_3716_; lean_object* v___x_3717_; lean_object* v___y_3719_; lean_object* v___y_3720_; lean_object* v___y_3721_; lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v___y_3724_; lean_object* v___y_3725_; lean_object* v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3730_; uint8_t v___y_3731_; lean_object* v___y_3732_; lean_object* v___y_3733_; lean_object* v___y_3734_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v___y_3737_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___y_3763_; uint8_t v___y_3764_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v_usingTk_x3f_3771_; lean_object* v_usingArg_3772_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3793_; lean_object* v___y_3794_; uint8_t v___y_3795_; lean_object* v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v_args_3804_; lean_object* v___y_3816_; uint8_t v___y_3817_; lean_object* v___y_3818_; lean_object* v___y_3819_; lean_object* v___y_3820_; lean_object* v___y_3821_; lean_object* v___y_3822_; lean_object* v___y_3823_; lean_object* v___y_3824_; lean_object* v___y_3825_; lean_object* v___y_3826_; lean_object* v___y_3827_; lean_object* v_only_3828_; lean_object* v___y_3829_; lean_object* v___y_3830_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3850_; lean_object* v___y_3851_; lean_object* v___y_3852_; lean_object* v___y_3853_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v___y_3857_; lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v_unfold_3860_; lean_object* v_squeeze_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3886_; lean_object* v___y_3887_; lean_object* v___x_3896_; uint8_t v___x_3897_; 
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
v___x_3742_ = lean_box(v___y_3731_);
lean_inc(v___y_3736_);
lean_inc(v___y_3737_);
lean_inc(v___y_3740_);
lean_inc(v___y_3722_);
lean_inc(v___y_3723_);
lean_inc(v___y_3729_);
v___f_3743_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___boxed), 22, 12);
lean_closure_set(v___f_3743_, 0, v___y_3729_);
lean_closure_set(v___f_3743_, 1, v___x_3715_);
lean_closure_set(v___f_3743_, 2, v___y_3723_);
lean_closure_set(v___f_3743_, 3, v___y_3722_);
lean_closure_set(v___f_3743_, 4, v___x_3741_);
lean_closure_set(v___f_3743_, 5, v___x_3707_);
lean_closure_set(v___f_3743_, 6, v___x_3708_);
lean_closure_set(v___f_3743_, 7, v___x_3709_);
lean_closure_set(v___f_3743_, 8, v___y_3740_);
lean_closure_set(v___f_3743_, 9, v___y_3737_);
lean_closure_set(v___f_3743_, 10, v___x_3742_);
lean_closure_set(v___f_3743_, 11, v___y_3736_);
v___x_3744_ = lean_box(v___x_3712_);
v___x_3745_ = lean_box(v_useReducible_3696_);
v___x_3746_ = lean_box(v___y_3731_);
lean_inc(v___y_3724_);
lean_inc(v___y_3734_);
v___f_3747_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___boxed), 35, 26);
lean_closure_set(v___f_3747_, 0, v_tk_3716_);
lean_closure_set(v___f_3747_, 1, v___x_3707_);
lean_closure_set(v___f_3747_, 2, v___x_3708_);
lean_closure_set(v___f_3747_, 3, v___x_3709_);
lean_closure_set(v___f_3747_, 4, v___x_3715_);
lean_closure_set(v___f_3747_, 5, v___x_3744_);
lean_closure_set(v___f_3747_, 6, v___y_3734_);
lean_closure_set(v___f_3747_, 7, v___x_3711_);
lean_closure_set(v___f_3747_, 8, v___x_3745_);
lean_closure_set(v___f_3747_, 9, v___f_3714_);
lean_closure_set(v___f_3747_, 10, v___x_3710_);
lean_closure_set(v___f_3747_, 11, v___y_3730_);
lean_closure_set(v___f_3747_, 12, v___y_3735_);
lean_closure_set(v___f_3747_, 13, v___x_3717_);
lean_closure_set(v___f_3747_, 14, v___y_3724_);
lean_closure_set(v___f_3747_, 15, v___y_3725_);
lean_closure_set(v___f_3747_, 16, v___y_3739_);
lean_closure_set(v___f_3747_, 17, v___y_3729_);
lean_closure_set(v___f_3747_, 18, v___x_3746_);
lean_closure_set(v___f_3747_, 19, v___f_3743_);
lean_closure_set(v___f_3747_, 20, v___y_3733_);
lean_closure_set(v___f_3747_, 21, v___y_3736_);
lean_closure_set(v___f_3747_, 22, v___y_3737_);
lean_closure_set(v___f_3747_, 23, v___y_3723_);
lean_closure_set(v___f_3747_, 24, v___y_3722_);
lean_closure_set(v___f_3747_, 25, v___y_3740_);
v___x_3748_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_3748_, 0, v___f_3747_);
v___x_3749_ = l_Lean_Elab_Tactic_focus___redArg(v___x_3748_, v___y_3727_, v___y_3726_, v___y_3732_, v___y_3738_, v___y_3720_, v___y_3728_, v___y_3719_, v___y_3721_);
return v___x_3749_;
}
v___jp_3750_:
{
lean_object* v___x_3773_; 
v___x_3773_ = l_Lean_Syntax_getOptional_x3f(v___y_3757_);
lean_dec(v___y_3757_);
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
v___y_3725_ = v___y_3758_;
v___y_3726_ = v___y_3759_;
v___y_3727_ = v___y_3760_;
v___y_3728_ = v___y_3761_;
v___y_3729_ = v___y_3762_;
v___y_3730_ = v___y_3763_;
v___y_3731_ = v___y_3764_;
v___y_3732_ = v___y_3765_;
v___y_3733_ = v_usingTk_x3f_3771_;
v___y_3734_ = v___y_3766_;
v___y_3735_ = v___y_3767_;
v___y_3736_ = v___y_3768_;
v___y_3737_ = v___y_3769_;
v___y_3738_ = v___y_3770_;
v___y_3739_ = v_usingArg_3772_;
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
v___y_3725_ = v___y_3758_;
v___y_3726_ = v___y_3759_;
v___y_3727_ = v___y_3760_;
v___y_3728_ = v___y_3761_;
v___y_3729_ = v___y_3762_;
v___y_3730_ = v___y_3763_;
v___y_3731_ = v___y_3764_;
v___y_3732_ = v___y_3765_;
v___y_3733_ = v_usingTk_x3f_3771_;
v___y_3734_ = v___y_3766_;
v___y_3735_ = v___y_3767_;
v___y_3736_ = v___y_3768_;
v___y_3737_ = v___y_3769_;
v___y_3738_ = v___y_3770_;
v___y_3739_ = v_usingArg_3772_;
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
v___x_3806_ = l_Lean_Syntax_getArg(v___y_3803_, v___x_3805_);
lean_dec(v___y_3803_);
v___x_3807_ = l_Lean_Syntax_isNone(v___x_3806_);
if (v___x_3807_ == 0)
{
uint8_t v___x_3808_; 
lean_inc(v___x_3806_);
v___x_3808_ = l_Lean_Syntax_matchesNull(v___x_3806_, v___y_3796_);
lean_dec(v___y_3796_);
if (v___x_3808_ == 0)
{
lean_object* v___x_3809_; 
lean_dec(v___x_3806_);
lean_dec(v_args_3804_);
lean_dec(v___y_3801_);
lean_dec(v___y_3800_);
lean_dec(v___y_3799_);
lean_dec(v___y_3794_);
lean_dec(v___y_3790_);
lean_dec(v___y_3789_);
lean_dec(v___y_3787_);
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
v___y_3753_ = v___y_3786_;
v___y_3754_ = v___y_3787_;
v___y_3755_ = v_args_3804_;
v___y_3756_ = v___y_3788_;
v___y_3757_ = v___y_3789_;
v___y_3758_ = v___y_3790_;
v___y_3759_ = v___y_3791_;
v___y_3760_ = v___y_3792_;
v___y_3761_ = v___y_3793_;
v___y_3762_ = v___y_3794_;
v___y_3763_ = v___x_3805_;
v___y_3764_ = v___y_3795_;
v___y_3765_ = v___y_3797_;
v___y_3766_ = v___y_3798_;
v___y_3767_ = v___y_3799_;
v___y_3768_ = v___y_3800_;
v___y_3769_ = v___y_3801_;
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
lean_dec(v___y_3796_);
v___x_3814_ = lean_box(0);
v___y_3751_ = v___y_3784_;
v___y_3752_ = v___y_3785_;
v___y_3753_ = v___y_3786_;
v___y_3754_ = v___y_3787_;
v___y_3755_ = v_args_3804_;
v___y_3756_ = v___y_3788_;
v___y_3757_ = v___y_3789_;
v___y_3758_ = v___y_3790_;
v___y_3759_ = v___y_3791_;
v___y_3760_ = v___y_3792_;
v___y_3761_ = v___y_3793_;
v___y_3762_ = v___y_3794_;
v___y_3763_ = v___x_3805_;
v___y_3764_ = v___y_3795_;
v___y_3765_ = v___y_3797_;
v___y_3766_ = v___y_3798_;
v___y_3767_ = v___y_3799_;
v___y_3768_ = v___y_3800_;
v___y_3769_ = v___y_3801_;
v___y_3770_ = v___y_3802_;
v_usingTk_x3f_3771_ = v___x_3814_;
v_usingArg_3772_ = v___x_3814_;
goto v___jp_3750_;
}
}
v___jp_3815_:
{
lean_object* v___x_3837_; uint8_t v___x_3838_; 
v___x_3837_ = l_Lean_Syntax_getArg(v___y_3824_, v___y_3826_);
lean_dec(v___y_3826_);
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
lean_dec(v___y_3827_);
lean_dec(v___y_3825_);
lean_dec(v___y_3824_);
lean_dec(v___y_3823_);
lean_dec(v___y_3822_);
lean_dec(v___y_3821_);
lean_dec(v___y_3819_);
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
lean_dec(v___y_3827_);
lean_dec(v___y_3825_);
lean_dec(v___y_3824_);
lean_dec(v___y_3823_);
lean_dec(v___y_3822_);
lean_dec(v___y_3821_);
lean_dec(v___y_3819_);
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
v___y_3784_ = v___y_3835_;
v___y_3785_ = v___y_3833_;
v___y_3786_ = v___y_3836_;
v___y_3787_ = v_only_3828_;
v___y_3788_ = v___y_3820_;
v___y_3789_ = v___y_3825_;
v___y_3790_ = v___y_3823_;
v___y_3791_ = v___y_3830_;
v___y_3792_ = v___y_3829_;
v___y_3793_ = v___y_3834_;
v___y_3794_ = v___y_3816_;
v___y_3795_ = v___y_3817_;
v___y_3796_ = v___y_3827_;
v___y_3797_ = v___y_3831_;
v___y_3798_ = v___y_3818_;
v___y_3799_ = v___y_3819_;
v___y_3800_ = v___y_3821_;
v___y_3801_ = v___y_3822_;
v___y_3802_ = v___y_3832_;
v___y_3803_ = v___y_3824_;
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
v___y_3784_ = v___y_3835_;
v___y_3785_ = v___y_3833_;
v___y_3786_ = v___y_3836_;
v___y_3787_ = v_only_3828_;
v___y_3788_ = v___y_3820_;
v___y_3789_ = v___y_3825_;
v___y_3790_ = v___y_3823_;
v___y_3791_ = v___y_3830_;
v___y_3792_ = v___y_3829_;
v___y_3793_ = v___y_3834_;
v___y_3794_ = v___y_3816_;
v___y_3795_ = v___y_3817_;
v___y_3796_ = v___y_3827_;
v___y_3797_ = v___y_3831_;
v___y_3798_ = v___y_3818_;
v___y_3799_ = v___y_3819_;
v___y_3800_ = v___y_3821_;
v___y_3801_ = v___y_3822_;
v___y_3802_ = v___y_3832_;
v___y_3803_ = v___y_3824_;
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
lean_dec(v___y_3857_);
lean_dec(v___y_3856_);
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
lean_dec(v___y_3857_);
lean_dec(v___y_3856_);
lean_dec(v_tk_3716_);
v___x_3869_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3869_;
}
else
{
lean_object* v___x_3870_; lean_object* v___x_3871_; uint8_t v___x_3872_; 
v___x_3870_ = l_Lean_Syntax_getArg(v___x_3862_, v___x_3717_);
v___x_3871_ = l_Lean_Syntax_getArg(v___x_3862_, v___y_3857_);
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
lean_dec(v___y_3857_);
lean_dec(v___y_3856_);
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
lean_inc(v___y_3857_);
v___y_3816_ = v___x_3866_;
v___y_3817_ = v___x_3864_;
v___y_3818_ = v___x_3863_;
v___y_3819_ = v___x_3861_;
v___y_3820_ = v___x_3867_;
v___y_3821_ = v___y_3856_;
v___y_3822_ = v_unfold_3860_;
v___y_3823_ = v___y_3857_;
v___y_3824_ = v___x_3862_;
v___y_3825_ = v___x_3870_;
v___y_3826_ = v___x_3861_;
v___y_3827_ = v___y_3857_;
v_only_3828_ = v___x_3876_;
v___y_3829_ = v___y_3854_;
v___y_3830_ = v___y_3850_;
v___y_3831_ = v___y_3853_;
v___y_3832_ = v___y_3855_;
v___y_3833_ = v___y_3852_;
v___y_3834_ = v___y_3851_;
v___y_3835_ = v___y_3859_;
v___y_3836_ = v___y_3858_;
goto v___jp_3815_;
}
}
else
{
lean_object* v___x_3877_; 
lean_dec(v___x_3871_);
v___x_3877_ = lean_box(0);
lean_inc(v___y_3857_);
v___y_3816_ = v___x_3866_;
v___y_3817_ = v___x_3864_;
v___y_3818_ = v___x_3863_;
v___y_3819_ = v___x_3861_;
v___y_3820_ = v___x_3867_;
v___y_3821_ = v___y_3856_;
v___y_3822_ = v_unfold_3860_;
v___y_3823_ = v___y_3857_;
v___y_3824_ = v___x_3862_;
v___y_3825_ = v___x_3870_;
v___y_3826_ = v___x_3861_;
v___y_3827_ = v___y_3857_;
v_only_3828_ = v___x_3877_;
v___y_3829_ = v___y_3854_;
v___y_3830_ = v___y_3850_;
v___y_3831_ = v___y_3853_;
v___y_3832_ = v___y_3855_;
v___y_3833_ = v___y_3852_;
v___y_3834_ = v___y_3851_;
v___y_3835_ = v___y_3859_;
v___y_3836_ = v___y_3858_;
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
v___y_3850_ = v___y_3881_;
v___y_3851_ = v___y_3885_;
v___y_3852_ = v___y_3884_;
v___y_3853_ = v___y_3882_;
v___y_3854_ = v___y_3880_;
v___y_3855_ = v___y_3883_;
v___y_3856_ = v_squeeze_3879_;
v___y_3857_ = v___x_3888_;
v___y_3858_ = v___y_3887_;
v___y_3859_ = v___y_3886_;
v_unfold_3860_ = v___x_3894_;
goto v___jp_3849_;
}
}
else
{
lean_object* v___x_3895_; 
lean_dec(v___x_3889_);
v___x_3895_ = lean_box(0);
v___y_3850_ = v___y_3881_;
v___y_3851_ = v___y_3885_;
v___y_3852_ = v___y_3884_;
v___y_3853_ = v___y_3882_;
v___y_3854_ = v___y_3880_;
v___y_3855_ = v___y_3883_;
v___y_3856_ = v_squeeze_3879_;
v___y_3857_ = v___x_3888_;
v___y_3858_ = v___y_3887_;
v___y_3859_ = v___y_3886_;
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
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(lean_object* v_mvarId_3916_, lean_object* v_val_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_){
_start:
{
lean_object* v___x_3927_; 
v___x_3927_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(v_mvarId_3916_, v_val_3917_, v___y_3923_);
return v___x_3927_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___boxed(lean_object* v_mvarId_3928_, lean_object* v_val_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_){
_start:
{
lean_object* v_res_3939_; 
v_res_3939_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(v_mvarId_3928_, v_val_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_);
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
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5(lean_object* v_o_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_){
_start:
{
lean_object* v___x_3950_; 
v___x_3950_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(v_o_3940_, v___y_3948_);
return v___x_3950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___boxed(lean_object* v_o_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_){
_start:
{
lean_object* v_res_3961_; 
v_res_3961_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5(v_o_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3(lean_object* v_00_u03b2_4012_, lean_object* v_x_4013_, lean_object* v_x_4014_, lean_object* v_x_4015_){
_start:
{
lean_object* v___x_4016_; 
v___x_4016_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(v_x_4013_, v_x_4014_, v_x_4015_);
return v___x_4016_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5(lean_object* v_00_u03b2_4017_, lean_object* v_m_4018_, lean_object* v_a_4019_){
_start:
{
uint8_t v___x_4020_; 
v___x_4020_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(v_m_4018_, v_a_4019_);
return v___x_4020_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___boxed(lean_object* v_00_u03b2_4021_, lean_object* v_m_4022_, lean_object* v_a_4023_){
_start:
{
uint8_t v_res_4024_; lean_object* v_r_4025_; 
v_res_4024_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5(v_00_u03b2_4021_, v_m_4022_, v_a_4023_);
lean_dec_ref(v_a_4023_);
lean_dec_ref(v_m_4022_);
v_r_4025_ = lean_box(v_res_4024_);
return v_r_4025_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6(lean_object* v_00_u03b2_4026_, lean_object* v_m_4027_, lean_object* v_a_4028_, lean_object* v_b_4029_){
_start:
{
lean_object* v___x_4030_; 
v___x_4030_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(v_m_4027_, v_a_4028_, v_b_4029_);
return v___x_4030_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__15(lean_object* v_mvarId_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_){
_start:
{
lean_object* v___x_4042_; 
v___x_4042_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__15___redArg(v_mvarId_4031_, v___y_4032_, v___y_4038_);
return v___x_4042_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__15___boxed(lean_object* v_mvarId_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_){
_start:
{
lean_object* v_res_4054_; 
v_res_4054_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__15(v_mvarId_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_);
lean_dec(v___y_4052_);
lean_dec_ref(v___y_4051_);
lean_dec(v___y_4050_);
lean_dec_ref(v___y_4049_);
lean_dec(v___y_4048_);
lean_dec_ref(v___y_4047_);
lean_dec(v___y_4046_);
lean_dec_ref(v___y_4045_);
lean_dec(v_mvarId_4043_);
return v_res_4054_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16(lean_object* v_mvarId_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_){
_start:
{
lean_object* v___x_4066_; 
v___x_4066_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg(v_mvarId_4055_, v___y_4056_, v___y_4062_);
return v___x_4066_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___boxed(lean_object* v_mvarId_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_){
_start:
{
lean_object* v_res_4078_; 
v_res_4078_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16(v_mvarId_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_);
lean_dec(v___y_4076_);
lean_dec_ref(v___y_4075_);
lean_dec(v___y_4074_);
lean_dec_ref(v___y_4073_);
lean_dec(v___y_4072_);
lean_dec_ref(v___y_4071_);
lean_dec(v___y_4070_);
lean_dec_ref(v___y_4069_);
lean_dec(v_mvarId_4067_);
return v_res_4078_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10(lean_object* v_00_u03b2_4079_, lean_object* v_x_4080_, size_t v_x_4081_, size_t v_x_4082_, lean_object* v_x_4083_, lean_object* v_x_4084_){
_start:
{
lean_object* v___x_4085_; 
v___x_4085_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___redArg(v_x_4080_, v_x_4081_, v_x_4082_, v_x_4083_, v_x_4084_);
return v___x_4085_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___boxed(lean_object* v_00_u03b2_4086_, lean_object* v_x_4087_, lean_object* v_x_4088_, lean_object* v_x_4089_, lean_object* v_x_4090_, lean_object* v_x_4091_){
_start:
{
size_t v_x_98923__boxed_4092_; size_t v_x_98924__boxed_4093_; lean_object* v_res_4094_; 
v_x_98923__boxed_4092_ = lean_unbox_usize(v_x_4088_);
lean_dec(v_x_4088_);
v_x_98924__boxed_4093_ = lean_unbox_usize(v_x_4089_);
lean_dec(v_x_4089_);
v_res_4094_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10(v_00_u03b2_4086_, v_x_4087_, v_x_98923__boxed_4092_, v_x_98924__boxed_4093_, v_x_4090_, v_x_4091_);
return v_res_4094_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11(lean_object* v_00_u03b2_4095_, lean_object* v_a_4096_, lean_object* v_x_4097_){
_start:
{
uint8_t v___x_4098_; 
v___x_4098_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___redArg(v_a_4096_, v_x_4097_);
return v___x_4098_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___boxed(lean_object* v_00_u03b2_4099_, lean_object* v_a_4100_, lean_object* v_x_4101_){
_start:
{
uint8_t v_res_4102_; lean_object* v_r_4103_; 
v_res_4102_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11(v_00_u03b2_4099_, v_a_4100_, v_x_4101_);
lean_dec(v_x_4101_);
lean_dec_ref(v_a_4100_);
v_r_4103_ = lean_box(v_res_4102_);
return v_r_4103_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13(lean_object* v_00_u03b2_4104_, lean_object* v_data_4105_){
_start:
{
lean_object* v___x_4106_; 
v___x_4106_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13___redArg(v_data_4105_);
return v___x_4106_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__19(lean_object* v_00_u03b2_4107_, lean_object* v_n_4108_, lean_object* v_k_4109_, lean_object* v_v_4110_){
_start:
{
lean_object* v___x_4111_; 
v___x_4111_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__19___redArg(v_n_4108_, v_k_4109_, v_v_4110_);
return v___x_4111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__20(lean_object* v_00_u03b2_4112_, size_t v_depth_4113_, lean_object* v_keys_4114_, lean_object* v_vals_4115_, lean_object* v_heq_4116_, lean_object* v_i_4117_, lean_object* v_entries_4118_){
_start:
{
lean_object* v___x_4119_; 
v___x_4119_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__20___redArg(v_depth_4113_, v_keys_4114_, v_vals_4115_, v_i_4117_, v_entries_4118_);
return v___x_4119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__20___boxed(lean_object* v_00_u03b2_4120_, lean_object* v_depth_4121_, lean_object* v_keys_4122_, lean_object* v_vals_4123_, lean_object* v_heq_4124_, lean_object* v_i_4125_, lean_object* v_entries_4126_){
_start:
{
size_t v_depth_boxed_4127_; lean_object* v_res_4128_; 
v_depth_boxed_4127_ = lean_unbox_usize(v_depth_4121_);
lean_dec(v_depth_4121_);
v_res_4128_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__20(v_00_u03b2_4120_, v_depth_boxed_4127_, v_keys_4122_, v_vals_4123_, v_heq_4124_, v_i_4125_, v_entries_4126_);
lean_dec_ref(v_vals_4123_);
lean_dec_ref(v_keys_4122_);
return v_res_4128_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13_spec__15(lean_object* v_00_u03b2_4129_, lean_object* v_i_4130_, lean_object* v_source_4131_, lean_object* v_target_4132_){
_start:
{
lean_object* v___x_4133_; 
v___x_4133_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13_spec__15___redArg(v_i_4130_, v_source_4131_, v_target_4132_);
return v___x_4133_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__19_spec__21(lean_object* v_00_u03b2_4134_, lean_object* v_x_4135_, lean_object* v_x_4136_, lean_object* v_x_4137_, lean_object* v_x_4138_){
_start:
{
lean_object* v___x_4139_; 
v___x_4139_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__19_spec__21___redArg(v_x_4135_, v_x_4136_, v_x_4137_, v_x_4138_);
return v___x_4139_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13_spec__15_spec__20(lean_object* v_00_u03b2_4140_, lean_object* v_x_4141_, lean_object* v_x_4142_){
_start:
{
lean_object* v___x_4143_; 
v___x_4143_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13_spec__15_spec__20___redArg(v_x_4141_, v_x_4142_);
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
lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; lean_object* v___y_4253_; uint8_t v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v___y_4263_; lean_object* v___x_4272_; uint8_t v___x_4273_; 
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
lean_object* v___x_4275_; lean_object* v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; uint8_t v___y_4290_; lean_object* v___y_4291_; lean_object* v___y_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4297_; lean_object* v___y_4298_; lean_object* v___y_4313_; lean_object* v___y_4314_; lean_object* v___y_4315_; lean_object* v___y_4316_; lean_object* v___y_4317_; lean_object* v___y_4318_; lean_object* v___y_4319_; lean_object* v___y_4320_; lean_object* v___y_4321_; lean_object* v___y_4322_; lean_object* v___y_4323_; lean_object* v___y_4324_; lean_object* v___y_4325_; uint8_t v___y_4326_; lean_object* v___y_4327_; lean_object* v___y_4328_; lean_object* v___y_4329_; lean_object* v___y_4330_; lean_object* v___y_4331_; lean_object* v___y_4332_; lean_object* v___y_4333_; lean_object* v___y_4334_; lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v___y_4346_; lean_object* v___y_4347_; lean_object* v___y_4348_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v___y_4351_; lean_object* v___y_4352_; lean_object* v___y_4353_; lean_object* v___y_4354_; lean_object* v___y_4355_; uint8_t v___y_4356_; lean_object* v___y_4357_; lean_object* v___y_4358_; lean_object* v___y_4359_; lean_object* v___y_4360_; lean_object* v___y_4361_; lean_object* v___y_4362_; lean_object* v___y_4363_; lean_object* v___y_4364_; lean_object* v___y_4373_; lean_object* v___y_4374_; lean_object* v___y_4375_; lean_object* v___y_4376_; lean_object* v___y_4377_; lean_object* v___y_4378_; lean_object* v___y_4379_; lean_object* v___y_4380_; lean_object* v___y_4381_; lean_object* v___y_4382_; lean_object* v___y_4383_; lean_object* v___y_4384_; uint8_t v___y_4385_; lean_object* v___y_4386_; lean_object* v___y_4387_; lean_object* v___y_4388_; lean_object* v___y_4389_; lean_object* v___y_4390_; lean_object* v___y_4391_; lean_object* v___y_4392_; lean_object* v___y_4393_; lean_object* v_tk_4402_; lean_object* v___y_4404_; lean_object* v___y_4405_; lean_object* v___y_4406_; lean_object* v___y_4407_; lean_object* v___y_4408_; lean_object* v___y_4409_; lean_object* v___y_4410_; lean_object* v___y_4411_; lean_object* v___y_4412_; lean_object* v___y_4413_; lean_object* v___y_4414_; lean_object* v___y_4415_; lean_object* v___y_4416_; lean_object* v___y_4417_; lean_object* v___y_4418_; lean_object* v___y_4435_; lean_object* v___y_4436_; lean_object* v___y_4437_; lean_object* v___y_4438_; lean_object* v___y_4439_; lean_object* v___y_4440_; lean_object* v_args_4441_; lean_object* v___y_4442_; lean_object* v___y_4443_; lean_object* v___y_4444_; lean_object* v___y_4445_; lean_object* v___y_4446_; lean_object* v___y_4447_; lean_object* v___y_4448_; lean_object* v___y_4449_; lean_object* v___x_4462_; lean_object* v___y_4464_; lean_object* v___y_4465_; lean_object* v___y_4466_; lean_object* v___y_4467_; lean_object* v___y_4468_; lean_object* v___y_4469_; lean_object* v_only_4470_; lean_object* v___y_4471_; lean_object* v___y_4472_; lean_object* v___y_4473_; lean_object* v___y_4474_; lean_object* v___y_4475_; lean_object* v___y_4476_; lean_object* v___y_4477_; lean_object* v___y_4478_; lean_object* v___y_4492_; lean_object* v___y_4493_; lean_object* v_unfold_4494_; lean_object* v___y_4495_; lean_object* v___y_4496_; lean_object* v___y_4497_; lean_object* v___y_4498_; lean_object* v___y_4499_; lean_object* v___y_4500_; lean_object* v___y_4501_; lean_object* v___y_4502_; lean_object* v_squeeze_4521_; lean_object* v___y_4522_; lean_object* v___y_4523_; lean_object* v___y_4524_; lean_object* v___y_4525_; lean_object* v___y_4526_; lean_object* v___y_4527_; lean_object* v___y_4528_; lean_object* v___y_4529_; lean_object* v___x_4538_; uint8_t v___x_4539_; 
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
lean_inc_ref(v___y_4295_);
v___x_4299_ = l_Array_append___redArg(v___y_4295_, v___y_4298_);
lean_dec_ref(v___y_4298_);
lean_inc(v___y_4293_);
lean_inc(v___y_4287_);
v___x_4300_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4300_, 0, v___y_4287_);
lean_ctor_set(v___x_4300_, 1, v___y_4293_);
lean_ctor_set(v___x_4300_, 2, v___x_4299_);
if (lean_obj_tag(v___y_4284_) == 1)
{
lean_object* v_val_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; 
v_val_4301_ = lean_ctor_get(v___y_4284_, 0);
lean_inc(v_val_4301_);
lean_dec_ref_known(v___y_4284_, 1);
v___x_4302_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
v___x_4303_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_4287_, 4);
v___x_4304_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4304_, 0, v___y_4287_);
lean_ctor_set(v___x_4304_, 1, v___x_4303_);
lean_inc_ref(v___y_4295_);
v___x_4305_ = l_Array_append___redArg(v___y_4295_, v_val_4301_);
lean_dec(v_val_4301_);
lean_inc(v___y_4293_);
v___x_4306_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4306_, 0, v___y_4287_);
lean_ctor_set(v___x_4306_, 1, v___y_4293_);
lean_ctor_set(v___x_4306_, 2, v___x_4305_);
v___x_4307_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_4308_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4308_, 0, v___y_4287_);
lean_ctor_set(v___x_4308_, 1, v___x_4307_);
v___x_4309_ = l_Lean_Syntax_node3(v___y_4287_, v___x_4302_, v___x_4304_, v___x_4306_, v___x_4308_);
v___x_4310_ = l_Array_mkArray1___redArg(v___x_4309_);
v___y_4242_ = v___y_4277_;
v___y_4243_ = v___y_4278_;
v___y_4244_ = v___y_4279_;
v___y_4245_ = v___y_4280_;
v___y_4246_ = v___y_4281_;
v___y_4247_ = v___y_4282_;
v___y_4248_ = v___y_4283_;
v___y_4249_ = v___y_4285_;
v___y_4250_ = v___y_4286_;
v___y_4251_ = v___y_4287_;
v___y_4252_ = v___y_4288_;
v___y_4253_ = v___y_4289_;
v___y_4254_ = v___y_4290_;
v___y_4255_ = v___y_4291_;
v___y_4256_ = v___x_4300_;
v___y_4257_ = v___y_4292_;
v___y_4258_ = v___y_4293_;
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
lean_dec(v___y_4284_);
v___x_4311_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___y_4242_ = v___y_4277_;
v___y_4243_ = v___y_4278_;
v___y_4244_ = v___y_4279_;
v___y_4245_ = v___y_4280_;
v___y_4246_ = v___y_4281_;
v___y_4247_ = v___y_4282_;
v___y_4248_ = v___y_4283_;
v___y_4249_ = v___y_4285_;
v___y_4250_ = v___y_4286_;
v___y_4251_ = v___y_4287_;
v___y_4252_ = v___y_4288_;
v___y_4253_ = v___y_4289_;
v___y_4254_ = v___y_4290_;
v___y_4255_ = v___y_4291_;
v___y_4256_ = v___x_4300_;
v___y_4257_ = v___y_4292_;
v___y_4258_ = v___y_4293_;
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
lean_inc_ref(v___y_4331_);
v___x_4335_ = l_Array_append___redArg(v___y_4331_, v___y_4334_);
lean_dec_ref(v___y_4334_);
lean_inc(v___y_4329_);
lean_inc(v___y_4323_);
v___x_4336_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4336_, 0, v___y_4323_);
lean_ctor_set(v___x_4336_, 1, v___y_4329_);
lean_ctor_set(v___x_4336_, 2, v___x_4335_);
if (lean_obj_tag(v___y_4315_) == 1)
{
lean_object* v_val_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; 
v_val_4337_ = lean_ctor_get(v___y_4315_, 0);
lean_inc(v_val_4337_);
lean_dec_ref_known(v___y_4315_, 1);
v___x_4338_ = l_Lean_SourceInfo_fromRef(v_val_4337_, v___x_4273_);
lean_dec(v_val_4337_);
v___x_4339_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_4340_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4340_, 0, v___x_4338_);
lean_ctor_set(v___x_4340_, 1, v___x_4339_);
v___x_4341_ = l_Array_mkArray1___redArg(v___x_4340_);
v___y_4277_ = v___y_4313_;
v___y_4278_ = v___y_4314_;
v___y_4279_ = v___y_4316_;
v___y_4280_ = v___x_4336_;
v___y_4281_ = v___y_4317_;
v___y_4282_ = v___y_4318_;
v___y_4283_ = v___y_4319_;
v___y_4284_ = v___y_4320_;
v___y_4285_ = v___y_4321_;
v___y_4286_ = v___y_4322_;
v___y_4287_ = v___y_4323_;
v___y_4288_ = v___y_4324_;
v___y_4289_ = v___y_4325_;
v___y_4290_ = v___y_4326_;
v___y_4291_ = v___y_4327_;
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
v___x_4342_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_4315_);
lean_dec(v___y_4315_);
v___y_4277_ = v___y_4313_;
v___y_4278_ = v___y_4314_;
v___y_4279_ = v___y_4316_;
v___y_4280_ = v___x_4336_;
v___y_4281_ = v___y_4317_;
v___y_4282_ = v___y_4318_;
v___y_4283_ = v___y_4319_;
v___y_4284_ = v___y_4320_;
v___y_4285_ = v___y_4321_;
v___y_4286_ = v___y_4322_;
v___y_4287_ = v___y_4323_;
v___y_4288_ = v___y_4324_;
v___y_4289_ = v___y_4325_;
v___y_4290_ = v___y_4326_;
v___y_4291_ = v___y_4327_;
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
lean_inc_ref(v___y_4362_);
v___x_4365_ = l_Array_append___redArg(v___y_4362_, v___y_4364_);
lean_dec_ref(v___y_4364_);
lean_inc(v___y_4359_);
lean_inc(v___y_4353_);
v___x_4366_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4366_, 0, v___y_4353_);
lean_ctor_set(v___x_4366_, 1, v___y_4359_);
lean_ctor_set(v___x_4366_, 2, v___x_4365_);
v___x_4367_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6));
if (lean_obj_tag(v___y_4360_) == 0)
{
lean_object* v___x_4368_; 
v___x_4368_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___y_4313_ = v___y_4344_;
v___y_4314_ = v___y_4345_;
v___y_4315_ = v___y_4346_;
v___y_4316_ = v___y_4347_;
v___y_4317_ = v___y_4348_;
v___y_4318_ = v___y_4349_;
v___y_4319_ = v___x_4366_;
v___y_4320_ = v___y_4350_;
v___y_4321_ = v___y_4351_;
v___y_4322_ = v___y_4352_;
v___y_4323_ = v___y_4353_;
v___y_4324_ = v___y_4354_;
v___y_4325_ = v___y_4355_;
v___y_4326_ = v___y_4356_;
v___y_4327_ = v___y_4357_;
v___y_4328_ = v___y_4358_;
v___y_4329_ = v___y_4359_;
v___y_4330_ = v___y_4361_;
v___y_4331_ = v___y_4362_;
v___y_4332_ = v___y_4363_;
v___y_4333_ = v___x_4367_;
v___y_4334_ = v___x_4368_;
goto v___jp_4312_;
}
else
{
lean_object* v_val_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; 
v_val_4369_ = lean_ctor_get(v___y_4360_, 0);
lean_inc(v_val_4369_);
lean_dec_ref_known(v___y_4360_, 1);
v___x_4370_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___x_4371_ = lean_array_push(v___x_4370_, v_val_4369_);
v___y_4313_ = v___y_4344_;
v___y_4314_ = v___y_4345_;
v___y_4315_ = v___y_4346_;
v___y_4316_ = v___y_4347_;
v___y_4317_ = v___y_4348_;
v___y_4318_ = v___y_4349_;
v___y_4319_ = v___x_4366_;
v___y_4320_ = v___y_4350_;
v___y_4321_ = v___y_4351_;
v___y_4322_ = v___y_4352_;
v___y_4323_ = v___y_4353_;
v___y_4324_ = v___y_4354_;
v___y_4325_ = v___y_4355_;
v___y_4326_ = v___y_4356_;
v___y_4327_ = v___y_4357_;
v___y_4328_ = v___y_4358_;
v___y_4329_ = v___y_4359_;
v___y_4330_ = v___y_4361_;
v___y_4331_ = v___y_4362_;
v___y_4332_ = v___y_4363_;
v___y_4333_ = v___x_4367_;
v___y_4334_ = v___x_4371_;
goto v___jp_4312_;
}
}
v___jp_4372_:
{
lean_object* v___x_4394_; lean_object* v___x_4395_; 
lean_inc_ref(v___y_4392_);
v___x_4394_ = l_Array_append___redArg(v___y_4392_, v___y_4393_);
lean_dec_ref(v___y_4393_);
lean_inc(v___y_4389_);
lean_inc(v___y_4382_);
v___x_4395_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4395_, 0, v___y_4382_);
lean_ctor_set(v___x_4395_, 1, v___y_4389_);
lean_ctor_set(v___x_4395_, 2, v___x_4394_);
if (lean_obj_tag(v___y_4387_) == 1)
{
lean_object* v_val_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; 
v_val_4396_ = lean_ctor_get(v___y_4387_, 0);
lean_inc(v_val_4396_);
lean_dec_ref_known(v___y_4387_, 1);
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
v___y_4350_ = v___y_4379_;
v___y_4351_ = v___y_4380_;
v___y_4352_ = v___y_4381_;
v___y_4353_ = v___y_4382_;
v___y_4354_ = v___y_4383_;
v___y_4355_ = v___y_4384_;
v___y_4356_ = v___y_4385_;
v___y_4357_ = v___y_4386_;
v___y_4358_ = v___y_4388_;
v___y_4359_ = v___y_4389_;
v___y_4360_ = v___y_4390_;
v___y_4361_ = v___y_4391_;
v___y_4362_ = v___y_4392_;
v___y_4363_ = v___x_4395_;
v___y_4364_ = v___x_4400_;
goto v___jp_4343_;
}
else
{
lean_object* v___x_4401_; 
v___x_4401_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_4387_);
lean_dec(v___y_4387_);
v___y_4344_ = v___y_4373_;
v___y_4345_ = v___y_4374_;
v___y_4346_ = v___y_4375_;
v___y_4347_ = v___y_4376_;
v___y_4348_ = v___y_4377_;
v___y_4349_ = v___y_4378_;
v___y_4350_ = v___y_4379_;
v___y_4351_ = v___y_4380_;
v___y_4352_ = v___y_4381_;
v___y_4353_ = v___y_4382_;
v___y_4354_ = v___y_4383_;
v___y_4355_ = v___y_4384_;
v___y_4356_ = v___y_4385_;
v___y_4357_ = v___y_4386_;
v___y_4358_ = v___y_4388_;
v___y_4359_ = v___y_4389_;
v___y_4360_ = v___y_4390_;
v___y_4361_ = v___y_4391_;
v___y_4362_ = v___y_4392_;
v___y_4363_ = v___x_4395_;
v___y_4364_ = v___x_4401_;
goto v___jp_4343_;
}
}
v___jp_4403_:
{
lean_object* v_ref_4419_; uint8_t v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; 
v_ref_4419_ = lean_ctor_get(v___y_4413_, 4);
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
if (lean_obj_tag(v___y_4414_) == 1)
{
lean_object* v_val_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; 
v_val_4428_ = lean_ctor_get(v___y_4414_, 0);
lean_inc(v_val_4428_);
lean_dec_ref_known(v___y_4414_, 1);
v___x_4429_ = l_Lean_SourceInfo_fromRef(v_val_4428_, v___x_4273_);
lean_dec(v_val_4428_);
v___x_4430_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__1));
v___x_4431_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4431_, 0, v___x_4429_);
lean_ctor_set(v___x_4431_, 1, v___x_4430_);
v___x_4432_ = l_Array_mkArray1___redArg(v___x_4431_);
v___y_4373_ = v___y_4404_;
v___y_4374_ = v___y_4405_;
v___y_4375_ = v___y_4406_;
v___y_4376_ = v___y_4407_;
v___y_4377_ = v___y_4408_;
v___y_4378_ = v___x_4423_;
v___y_4379_ = v___y_4409_;
v___y_4380_ = v___y_4410_;
v___y_4381_ = v___x_4425_;
v___y_4382_ = v___x_4421_;
v___y_4383_ = v___y_4411_;
v___y_4384_ = v___y_4412_;
v___y_4385_ = v___x_4420_;
v___y_4386_ = v___y_4413_;
v___y_4387_ = v___y_4415_;
v___y_4388_ = v___y_4416_;
v___y_4389_ = v___x_4426_;
v___y_4390_ = v___y_4418_;
v___y_4391_ = v___y_4417_;
v___y_4392_ = v___x_4427_;
v___y_4393_ = v___x_4432_;
goto v___jp_4372_;
}
else
{
lean_object* v___x_4433_; 
v___x_4433_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_4414_);
lean_dec(v___y_4414_);
v___y_4373_ = v___y_4404_;
v___y_4374_ = v___y_4405_;
v___y_4375_ = v___y_4406_;
v___y_4376_ = v___y_4407_;
v___y_4377_ = v___y_4408_;
v___y_4378_ = v___x_4423_;
v___y_4379_ = v___y_4409_;
v___y_4380_ = v___y_4410_;
v___y_4381_ = v___x_4425_;
v___y_4382_ = v___x_4421_;
v___y_4383_ = v___y_4411_;
v___y_4384_ = v___y_4412_;
v___y_4385_ = v___x_4420_;
v___y_4386_ = v___y_4413_;
v___y_4387_ = v___y_4415_;
v___y_4388_ = v___y_4416_;
v___y_4389_ = v___x_4426_;
v___y_4390_ = v___y_4418_;
v___y_4391_ = v___y_4417_;
v___y_4392_ = v___x_4427_;
v___y_4393_ = v___x_4433_;
goto v___jp_4372_;
}
}
v___jp_4434_:
{
lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; 
v___x_4450_ = lean_unsigned_to_nat(5u);
v___x_4451_ = l_Lean_Syntax_getArg(v___y_4439_, v___x_4450_);
lean_dec(v___y_4439_);
v___x_4452_ = l_Lean_Syntax_getOptional_x3f(v___y_4440_);
lean_dec(v___y_4440_);
if (lean_obj_tag(v___x_4452_) == 0)
{
lean_object* v___x_4453_; 
v___x_4453_ = lean_box(0);
v___y_4404_ = v___y_4444_;
v___y_4405_ = v___x_4451_;
v___y_4406_ = v___y_4435_;
v___y_4407_ = v___y_4447_;
v___y_4408_ = v___y_4443_;
v___y_4409_ = v_args_4441_;
v___y_4410_ = v___y_4438_;
v___y_4411_ = v___y_4442_;
v___y_4412_ = v___y_4449_;
v___y_4413_ = v___y_4448_;
v___y_4414_ = v___y_4437_;
v___y_4415_ = v___y_4436_;
v___y_4416_ = v___y_4446_;
v___y_4417_ = v___y_4445_;
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
v___y_4404_ = v___y_4444_;
v___y_4405_ = v___x_4451_;
v___y_4406_ = v___y_4435_;
v___y_4407_ = v___y_4447_;
v___y_4408_ = v___y_4443_;
v___y_4409_ = v_args_4441_;
v___y_4410_ = v___y_4438_;
v___y_4411_ = v___y_4442_;
v___y_4412_ = v___y_4449_;
v___y_4413_ = v___y_4448_;
v___y_4414_ = v___y_4437_;
v___y_4415_ = v___y_4436_;
v___y_4416_ = v___y_4446_;
v___y_4417_ = v___y_4445_;
v___y_4418_ = v___x_4459_;
goto v___jp_4403_;
}
}
}
}
v___jp_4463_:
{
lean_object* v___x_4479_; uint8_t v___x_4480_; 
v___x_4479_ = l_Lean_Syntax_getArg(v___y_4466_, v___y_4468_);
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
lean_dec(v___y_4469_);
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
lean_dec(v___y_4469_);
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
v___y_4438_ = v___y_4467_;
v___y_4439_ = v___y_4466_;
v___y_4440_ = v___y_4469_;
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
v___y_4438_ = v___y_4467_;
v___y_4439_ = v___y_4466_;
v___y_4440_ = v___y_4469_;
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
v___y_4466_ = v___x_4504_;
v___y_4467_ = v___x_4508_;
v___y_4468_ = v___x_4503_;
v___y_4469_ = v___x_4512_;
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
v___y_4466_ = v___x_4504_;
v___y_4467_ = v___x_4508_;
v___y_4468_ = v___x_4503_;
v___y_4469_ = v___x_4512_;
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
lean_inc_ref(v___y_4260_);
v___x_4264_ = l_Array_append___redArg(v___y_4260_, v___y_4263_);
lean_dec_ref(v___y_4263_);
lean_inc_n(v___y_4258_, 2);
lean_inc_n(v___y_4251_, 4);
v___x_4265_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4265_, 0, v___y_4251_);
lean_ctor_set(v___x_4265_, 1, v___y_4258_);
lean_ctor_set(v___x_4265_, 2, v___x_4264_);
v___x_4266_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__5));
v___x_4267_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4267_, 0, v___y_4251_);
lean_ctor_set(v___x_4267_, 1, v___x_4266_);
v___x_4268_ = l_Lean_Syntax_node2(v___y_4251_, v___y_4258_, v___x_4267_, v___y_4243_);
lean_inc(v___y_4262_);
v___x_4269_ = l_Lean_Syntax_node5(v___y_4251_, v___y_4262_, v___y_4249_, v___y_4245_, v___y_4256_, v___x_4265_, v___x_4268_);
lean_inc(v___y_4247_);
v___x_4270_ = l_Lean_Syntax_node4(v___y_4251_, v___y_4247_, v___y_4250_, v___y_4261_, v___y_4248_, v___x_4269_);
v___x_4271_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v___y_4254_, v___x_4270_, v___y_4252_, v___y_4246_, v___y_4242_, v___y_4259_, v___y_4257_, v___y_4244_, v___y_4255_, v___y_4253_);
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
