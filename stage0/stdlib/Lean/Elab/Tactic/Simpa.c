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
uint8_t v_suppressElabErrors_boxed_116_; uint8_t v___y_4844__boxed_117_; uint8_t v_res_118_; lean_object* v_r_119_; 
v_suppressElabErrors_boxed_116_ = lean_unbox(v_suppressElabErrors_113_);
v___y_4844__boxed_117_ = lean_unbox(v___y_114_);
v_res_118_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0(v_suppressElabErrors_boxed_116_, v___y_4844__boxed_117_, v_x_115_);
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
lean_object* v___y_154_; lean_object* v___y_155_; uint8_t v___y_156_; lean_object* v___y_157_; lean_object* v___y_158_; lean_object* v___y_159_; uint8_t v___y_160_; lean_object* v_currNamespace_161_; lean_object* v_openDecls_162_; lean_object* v___y_163_; lean_object* v___y_189_; lean_object* v___y_190_; lean_object* v___y_191_; lean_object* v___y_192_; uint8_t v___y_193_; lean_object* v___y_194_; uint8_t v___y_195_; lean_object* v___y_196_; uint8_t v___y_197_; lean_object* v___y_198_; lean_object* v___y_216_; lean_object* v___y_217_; lean_object* v___y_218_; lean_object* v___y_219_; uint8_t v___y_220_; uint8_t v___y_221_; lean_object* v___y_222_; lean_object* v___y_223_; uint8_t v___y_224_; lean_object* v___y_225_; lean_object* v___y_229_; lean_object* v___y_230_; lean_object* v___y_231_; lean_object* v___y_232_; lean_object* v___y_233_; uint8_t v___y_234_; lean_object* v___y_235_; uint8_t v___y_236_; uint8_t v___y_237_; uint8_t v___x_242_; lean_object* v___y_244_; lean_object* v___y_245_; lean_object* v___y_246_; lean_object* v___y_247_; lean_object* v___y_248_; lean_object* v___y_249_; uint8_t v___y_250_; uint8_t v___y_251_; uint8_t v___y_252_; uint8_t v___y_254_; uint8_t v___x_272_; 
v___x_242_ = 2;
v___x_272_ = l_Lean_instBEqMessageSeverity_beq(v_severity_146_, v___x_242_);
if (v___x_272_ == 0)
{
v___y_254_ = v___x_272_;
goto v___jp_253_;
}
else
{
uint8_t v___x_273_; 
lean_inc_ref(v_msgData_145_);
v___x_273_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_145_);
v___y_254_ = v___x_273_;
goto v___jp_253_;
}
v___jp_153_:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v_env_168_; lean_object* v_nextMacroScope_169_; lean_object* v_ngen_170_; lean_object* v_auxDeclNGen_171_; lean_object* v_traceState_172_; lean_object* v_cache_173_; lean_object* v_messages_174_; lean_object* v_infoState_175_; lean_object* v_snapshotTasks_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_187_; 
lean_inc(v_openDecls_162_);
lean_inc(v_currNamespace_161_);
v___x_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_164_, 0, v_currNamespace_161_);
lean_ctor_set(v___x_164_, 1, v_openDecls_162_);
v___x_165_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
lean_ctor_set(v___x_165_, 1, v___y_159_);
lean_inc_ref(v___y_155_);
lean_inc_ref(v___y_158_);
v___x_166_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_166_, 0, v___y_158_);
lean_ctor_set(v___x_166_, 1, v___y_157_);
lean_ctor_set(v___x_166_, 2, v___y_154_);
lean_ctor_set(v___x_166_, 3, v___y_155_);
lean_ctor_set(v___x_166_, 4, v___x_165_);
lean_ctor_set_uint8(v___x_166_, sizeof(void*)*5, v___y_160_);
lean_ctor_set_uint8(v___x_166_, sizeof(void*)*5 + 1, v___y_156_);
lean_ctor_set_uint8(v___x_166_, sizeof(void*)*5 + 2, v_isSilent_147_);
v___x_167_ = lean_st_ref_take(v___y_163_);
v_env_168_ = lean_ctor_get(v___x_167_, 0);
v_nextMacroScope_169_ = lean_ctor_get(v___x_167_, 1);
v_ngen_170_ = lean_ctor_get(v___x_167_, 2);
v_auxDeclNGen_171_ = lean_ctor_get(v___x_167_, 3);
v_traceState_172_ = lean_ctor_get(v___x_167_, 4);
v_cache_173_ = lean_ctor_get(v___x_167_, 5);
v_messages_174_ = lean_ctor_get(v___x_167_, 6);
v_infoState_175_ = lean_ctor_get(v___x_167_, 7);
v_snapshotTasks_176_ = lean_ctor_get(v___x_167_, 8);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_187_ == 0)
{
v___x_178_ = v___x_167_;
v_isShared_179_ = v_isSharedCheck_187_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_snapshotTasks_176_);
lean_inc(v_infoState_175_);
lean_inc(v_messages_174_);
lean_inc(v_cache_173_);
lean_inc(v_traceState_172_);
lean_inc(v_auxDeclNGen_171_);
lean_inc(v_ngen_170_);
lean_inc(v_nextMacroScope_169_);
lean_inc(v_env_168_);
lean_dec(v___x_167_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_187_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_183_; 
v___x_180_ = lean_box(0);
v___x_181_ = l_Lean_MessageLog_add(v___x_166_, v_messages_174_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 6, v___x_181_);
v___x_183_ = v___x_178_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_env_168_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v_nextMacroScope_169_);
lean_ctor_set(v_reuseFailAlloc_186_, 2, v_ngen_170_);
lean_ctor_set(v_reuseFailAlloc_186_, 3, v_auxDeclNGen_171_);
lean_ctor_set(v_reuseFailAlloc_186_, 4, v_traceState_172_);
lean_ctor_set(v_reuseFailAlloc_186_, 5, v_cache_173_);
lean_ctor_set(v_reuseFailAlloc_186_, 6, v___x_181_);
lean_ctor_set(v_reuseFailAlloc_186_, 7, v_infoState_175_);
lean_ctor_set(v_reuseFailAlloc_186_, 8, v_snapshotTasks_176_);
v___x_183_ = v_reuseFailAlloc_186_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = lean_st_ref_put(v___y_163_, v___x_183_);
v___x_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_185_, 0, v___x_180_);
return v___x_185_;
}
}
}
v___jp_188_:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_214_; 
v___x_199_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_145_);
v___x_200_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__2(v___x_199_, v___y_148_, v___y_149_, v___y_150_, v___y_151_);
v_a_201_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_214_ == 0)
{
v___x_203_ = v___x_200_;
v_isShared_204_ = v_isSharedCheck_214_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_200_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_214_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
lean_inc_ref_n(v___y_192_, 2);
v___x_205_ = l_Lean_FileMap_toPosition(v___y_192_, v___y_196_);
lean_dec(v___y_196_);
v___x_206_ = l_Lean_FileMap_toPosition(v___y_192_, v___y_198_);
lean_dec(v___y_198_);
v___x_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
v___x_208_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___closed__0));
if (v___y_193_ == 0)
{
lean_del_object(v___x_203_);
lean_dec_ref(v___y_189_);
v___y_154_ = v___x_207_;
v___y_155_ = v___x_208_;
v___y_156_ = v___y_195_;
v___y_157_ = v___x_205_;
v___y_158_ = v___y_194_;
v___y_159_ = v_a_201_;
v___y_160_ = v___y_197_;
v_currNamespace_161_ = v___y_190_;
v_openDecls_162_ = v___y_191_;
v___y_163_ = v___y_151_;
goto v___jp_153_;
}
else
{
uint8_t v___x_209_; 
lean_inc(v_a_201_);
v___x_209_ = l_Lean_MessageData_hasTag(v___y_189_, v_a_201_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; lean_object* v___x_212_; 
lean_dec_ref_known(v___x_207_, 1);
lean_dec_ref(v___x_205_);
lean_dec(v_a_201_);
v___x_210_ = lean_box(0);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 0, v___x_210_);
v___x_212_ = v___x_203_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v___x_210_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
else
{
lean_del_object(v___x_203_);
v___y_154_ = v___x_207_;
v___y_155_ = v___x_208_;
v___y_156_ = v___y_195_;
v___y_157_ = v___x_205_;
v___y_158_ = v___y_194_;
v___y_159_ = v_a_201_;
v___y_160_ = v___y_197_;
v_currNamespace_161_ = v___y_190_;
v_openDecls_162_ = v___y_191_;
v___y_163_ = v___y_151_;
goto v___jp_153_;
}
}
}
}
v___jp_215_:
{
lean_object* v___x_226_; 
v___x_226_ = l_Lean_Syntax_getTailPos_x3f(v___y_223_, v___y_224_);
lean_dec(v___y_223_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_inc(v___y_225_);
v___y_189_ = v___y_216_;
v___y_190_ = v___y_217_;
v___y_191_ = v___y_218_;
v___y_192_ = v___y_219_;
v___y_193_ = v___y_220_;
v___y_194_ = v___y_222_;
v___y_195_ = v___y_221_;
v___y_196_ = v___y_225_;
v___y_197_ = v___y_224_;
v___y_198_ = v___y_225_;
goto v___jp_188_;
}
else
{
lean_object* v_val_227_; 
v_val_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_val_227_);
lean_dec_ref_known(v___x_226_, 1);
v___y_189_ = v___y_216_;
v___y_190_ = v___y_217_;
v___y_191_ = v___y_218_;
v___y_192_ = v___y_219_;
v___y_193_ = v___y_220_;
v___y_194_ = v___y_222_;
v___y_195_ = v___y_221_;
v___y_196_ = v___y_225_;
v___y_197_ = v___y_224_;
v___y_198_ = v_val_227_;
goto v___jp_188_;
}
}
v___jp_228_:
{
lean_object* v_ref_238_; lean_object* v___x_239_; 
v_ref_238_ = l_Lean_replaceRef(v_ref_144_, v___y_233_);
v___x_239_ = l_Lean_Syntax_getPos_x3f(v_ref_238_, v___y_236_);
if (lean_obj_tag(v___x_239_) == 0)
{
lean_object* v___x_240_; 
v___x_240_ = lean_unsigned_to_nat(0u);
v___y_216_ = v___y_229_;
v___y_217_ = v___y_230_;
v___y_218_ = v___y_231_;
v___y_219_ = v___y_232_;
v___y_220_ = v___y_234_;
v___y_221_ = v___y_237_;
v___y_222_ = v___y_235_;
v___y_223_ = v_ref_238_;
v___y_224_ = v___y_236_;
v___y_225_ = v___x_240_;
goto v___jp_215_;
}
else
{
lean_object* v_val_241_; 
v_val_241_ = lean_ctor_get(v___x_239_, 0);
lean_inc(v_val_241_);
lean_dec_ref_known(v___x_239_, 1);
v___y_216_ = v___y_229_;
v___y_217_ = v___y_230_;
v___y_218_ = v___y_231_;
v___y_219_ = v___y_232_;
v___y_220_ = v___y_234_;
v___y_221_ = v___y_237_;
v___y_222_ = v___y_235_;
v___y_223_ = v_ref_238_;
v___y_224_ = v___y_236_;
v___y_225_ = v_val_241_;
goto v___jp_215_;
}
}
v___jp_243_:
{
if (v___y_252_ == 0)
{
v___y_229_ = v___y_244_;
v___y_230_ = v___y_246_;
v___y_231_ = v___y_248_;
v___y_232_ = v___y_245_;
v___y_233_ = v___y_249_;
v___y_234_ = v___y_250_;
v___y_235_ = v___y_247_;
v___y_236_ = v___y_251_;
v___y_237_ = v_severity_146_;
goto v___jp_228_;
}
else
{
v___y_229_ = v___y_244_;
v___y_230_ = v___y_246_;
v___y_231_ = v___y_248_;
v___y_232_ = v___y_245_;
v___y_233_ = v___y_249_;
v___y_234_ = v___y_250_;
v___y_235_ = v___y_247_;
v___y_236_ = v___y_251_;
v___y_237_ = v___x_242_;
goto v___jp_228_;
}
}
v___jp_253_:
{
if (v___y_254_ == 0)
{
lean_object* v_toCold_255_; lean_object* v_ref_256_; uint8_t v_suppressElabErrors_257_; lean_object* v_fileName_258_; lean_object* v_fileMap_259_; lean_object* v_options_260_; lean_object* v_currNamespace_261_; lean_object* v_openDecls_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___f_265_; uint8_t v___x_266_; uint8_t v___x_267_; 
v_toCold_255_ = lean_ctor_get(v___y_150_, 0);
v_ref_256_ = lean_ctor_get(v___y_150_, 2);
v_suppressElabErrors_257_ = lean_ctor_get_uint8(v___y_150_, sizeof(void*)*3 + 1);
v_fileName_258_ = lean_ctor_get(v_toCold_255_, 0);
v_fileMap_259_ = lean_ctor_get(v_toCold_255_, 1);
v_options_260_ = lean_ctor_get(v_toCold_255_, 2);
v_currNamespace_261_ = lean_ctor_get(v_toCold_255_, 4);
v_openDecls_262_ = lean_ctor_get(v_toCold_255_, 5);
v___x_263_ = lean_box(v_suppressElabErrors_257_);
v___x_264_ = lean_box(v___y_254_);
v___f_265_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_265_, 0, v___x_263_);
lean_closure_set(v___f_265_, 1, v___x_264_);
v___x_266_ = 1;
v___x_267_ = l_Lean_instBEqMessageSeverity_beq(v_severity_146_, v___x_266_);
if (v___x_267_ == 0)
{
v___y_244_ = v___f_265_;
v___y_245_ = v_fileMap_259_;
v___y_246_ = v_currNamespace_261_;
v___y_247_ = v_fileName_258_;
v___y_248_ = v_openDecls_262_;
v___y_249_ = v_ref_256_;
v___y_250_ = v_suppressElabErrors_257_;
v___y_251_ = v___y_254_;
v___y_252_ = v___x_267_;
goto v___jp_243_;
}
else
{
lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_268_ = l_Lean_warningAsError;
v___x_269_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__3(v_options_260_, v___x_268_);
v___y_244_ = v___f_265_;
v___y_245_ = v_fileMap_259_;
v___y_246_ = v_currNamespace_261_;
v___y_247_ = v_fileName_258_;
v___y_248_ = v_openDecls_262_;
v___y_249_ = v_ref_256_;
v___y_250_ = v_suppressElabErrors_257_;
v___y_251_ = v___y_254_;
v___y_252_ = v___x_269_;
goto v___jp_243_;
}
}
else
{
lean_object* v___x_270_; lean_object* v___x_271_; 
lean_dec_ref(v_msgData_145_);
v___x_270_ = lean_box(0);
v___x_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
return v___x_271_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_274_, lean_object* v_msgData_275_, lean_object* v_severity_276_, lean_object* v_isSilent_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
uint8_t v_severity_boxed_283_; uint8_t v_isSilent_boxed_284_; lean_object* v_res_285_; 
v_severity_boxed_283_ = lean_unbox(v_severity_276_);
v_isSilent_boxed_284_ = lean_unbox(v_isSilent_277_);
v_res_285_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg(v_ref_274_, v_msgData_275_, v_severity_boxed_283_, v_isSilent_boxed_284_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v_ref_274_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0(lean_object* v_ref_286_, lean_object* v_msgData_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
uint8_t v___x_297_; uint8_t v___x_298_; lean_object* v___x_299_; 
v___x_297_ = 1;
v___x_298_ = 0;
v___x_299_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg(v_ref_286_, v_msgData_287_, v___x_297_, v___x_298_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0___boxed(lean_object* v_ref_300_, lean_object* v_msgData_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0(v_ref_300_, v_msgData_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v_ref_300_);
return v_res_311_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__1(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__0));
v___x_314_ = l_Lean_stringToMessageData(v___x_313_);
return v___x_314_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__3(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__2));
v___x_317_ = l_Lean_stringToMessageData(v___x_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0(lean_object* v_linterOption_318_, lean_object* v_stx_319_, lean_object* v_msg_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
lean_object* v_name_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_348_; 
v_name_330_ = lean_ctor_get(v_linterOption_318_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v_linterOption_318_);
if (v_isSharedCheck_348_ == 0)
{
lean_object* v_unused_349_; 
v_unused_349_ = lean_ctor_get(v_linterOption_318_, 1);
lean_dec(v_unused_349_);
v___x_332_ = v_linterOption_318_;
v_isShared_333_ = v_isSharedCheck_348_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_name_330_);
lean_dec(v_linterOption_318_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_348_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_337_; 
v___x_334_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__1, &l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__1_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__1);
lean_inc(v_name_330_);
v___x_335_ = l_Lean_MessageData_ofName(v_name_330_);
if (v_isShared_333_ == 0)
{
lean_ctor_set_tag(v___x_332_, 7);
lean_ctor_set(v___x_332_, 1, v___x_335_);
lean_ctor_set(v___x_332_, 0, v___x_334_);
v___x_337_ = v___x_332_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_334_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v___x_335_);
v___x_337_ = v_reuseFailAlloc_347_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v_disable_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_338_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__3, &l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__3_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__3);
v___x_339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_337_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
v_disable_340_ = l_Lean_MessageData_note(v___x_339_);
v___x_341_ = l_Lean_Linter_linterMessageTag;
v___x_342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_342_, 0, v_msg_320_);
lean_ctor_set(v___x_342_, 1, v_disable_340_);
v___x_343_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_341_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
v___x_344_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_344_, 0, v_name_330_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
lean_inc(v_stx_319_);
v___x_345_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_345_, 0, v_stx_319_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
v___x_346_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0(v_stx_319_, v___x_345_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
lean_dec(v_stx_319_);
return v___x_346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___boxed(lean_object* v_linterOption_350_, lean_object* v_stx_351_, lean_object* v_msg_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0(v_linterOption_350_, v_stx_351_, v_msg_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
return v_res_362_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__1(void){
_start:
{
lean_object* v___x_364_; lean_object* v_msg_365_; 
v___x_364_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__0));
v_msg_365_ = l_Lean_stringToMessageData(v___x_364_);
return v_msg_365_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__6(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__5));
v___x_373_ = l_Lean_MessageData_ofFormat(v___x_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa(lean_object* v_initialState_374_, lean_object* v_ref_375_, lean_object* v_replacement_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_){
_start:
{
lean_object* v_msg_387_; lean_object* v___y_388_; lean_object* v___y_389_; lean_object* v___y_390_; lean_object* v___y_391_; lean_object* v___y_392_; lean_object* v___y_393_; lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v_msg_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v_msg_398_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__1, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__1_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__1);
v___x_399_ = lean_box(0);
lean_inc(v_replacement_376_);
v___x_400_ = l_Lean_Meta_Tactic_TryThis_isValidTactic(v_initialState_374_, v_replacement_376_, v___x_399_, v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_a_401_; uint8_t v___x_402_; 
v_a_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_a_401_);
lean_dec_ref_known(v___x_400_, 1);
v___x_402_ = lean_unbox(v_a_401_);
lean_dec(v_a_401_);
if (v___x_402_ == 0)
{
lean_dec(v_replacement_376_);
v_msg_387_ = v_msg_398_;
v___y_388_ = v_a_377_;
v___y_389_ = v_a_378_;
v___y_390_ = v_a_379_;
v___y_391_ = v_a_380_;
v___y_392_ = v_a_381_;
v___y_393_ = v_a_382_;
v___y_394_ = v_a_383_;
v___y_395_ = v_a_384_;
goto v___jp_386_;
}
else
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; uint8_t v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; uint8_t v___x_413_; lean_object* v___x_414_; 
v___x_403_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__3));
v___x_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set(v___x_404_, 1, v_replacement_376_);
v___x_405_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v___x_399_);
lean_ctor_set(v___x_405_, 2, v___x_399_);
lean_ctor_set(v___x_405_, 3, v___x_399_);
lean_ctor_set(v___x_405_, 4, v___x_399_);
lean_ctor_set(v___x_405_, 5, v___x_399_);
lean_inc(v_ref_375_);
v___x_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_406_, 0, v_ref_375_);
v___x_407_ = 4;
lean_inc_ref(v___x_406_);
v___x_408_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_408_, 0, v___x_405_);
lean_ctor_set(v___x_408_, 1, v___x_406_);
lean_ctor_set(v___x_408_, 2, v___x_399_);
lean_ctor_set_uint8(v___x_408_, sizeof(void*)*3, v___x_407_);
v___x_409_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__6);
v___x_410_ = lean_unsigned_to_nat(1u);
v___x_411_ = lean_mk_empty_array_with_capacity(v___x_410_);
v___x_412_ = lean_array_push(v___x_411_, v___x_408_);
v___x_413_ = 0;
v___x_414_ = l_Lean_MessageData_hint(v___x_409_, v___x_412_, v___x_406_, v___x_399_, v___x_413_, v_a_383_, v_a_384_);
lean_dec_ref(v___x_412_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v_a_415_; lean_object* v___x_416_; 
v_a_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc(v_a_415_);
lean_dec_ref_known(v___x_414_, 1);
v___x_416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_416_, 0, v_msg_398_);
lean_ctor_set(v___x_416_, 1, v_a_415_);
v_msg_387_ = v___x_416_;
v___y_388_ = v_a_377_;
v___y_389_ = v_a_378_;
v___y_390_ = v_a_379_;
v___y_391_ = v_a_380_;
v___y_392_ = v_a_381_;
v___y_393_ = v_a_382_;
v___y_394_ = v_a_383_;
v___y_395_ = v_a_384_;
goto v___jp_386_;
}
else
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_424_; 
lean_dec(v_ref_375_);
v_a_417_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_424_ == 0)
{
v___x_419_ = v___x_414_;
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_414_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_422_; 
if (v_isShared_420_ == 0)
{
v___x_422_ = v___x_419_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_a_417_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
}
else
{
lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_432_; 
lean_dec(v_replacement_376_);
lean_dec(v_ref_375_);
v_a_425_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_432_ == 0)
{
v___x_427_ = v___x_400_;
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_dec(v___x_400_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_430_; 
if (v_isShared_428_ == 0)
{
v___x_430_ = v___x_427_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_a_425_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
v___jp_386_:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = l_Lean_linter_unnecessarySimpa;
v___x_397_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0(v___x_396_, v_ref_375_, v_msg_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
return v___x_397_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___boxed(lean_object* v_initialState_433_, lean_object* v_ref_434_, lean_object* v_replacement_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa(v_initialState_433_, v_ref_434_, v_replacement_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_);
lean_dec(v_a_443_);
lean_dec_ref(v_a_442_);
lean_dec(v_a_441_);
lean_dec_ref(v_a_440_);
lean_dec(v_a_439_);
lean_dec_ref(v_a_438_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1(lean_object* v_ref_446_, lean_object* v_msgData_447_, uint8_t v_severity_448_, uint8_t v_isSilent_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg(v_ref_446_, v_msgData_447_, v_severity_448_, v_isSilent_449_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_460_, lean_object* v_msgData_461_, lean_object* v_severity_462_, lean_object* v_isSilent_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
uint8_t v_severity_boxed_473_; uint8_t v_isSilent_boxed_474_; lean_object* v_res_475_; 
v_severity_boxed_473_ = lean_unbox(v_severity_462_);
v_isSilent_boxed_474_ = lean_unbox(v_isSilent_463_);
v_res_475_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1(v_ref_460_, v_msgData_461_, v_severity_boxed_473_, v_isSilent_boxed_474_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
lean_dec(v_ref_460_);
return v_res_475_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_476_ = lean_box(0);
v___x_477_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
lean_ctor_set(v___x_478_, 1, v___x_476_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg(){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0);
v___x_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___boxed(lean_object* v___y_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0(lean_object* v_00_u03b1_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___boxed(lean_object* v_00_u03b1_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0(v_00_u03b1_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg___lam__0(lean_object* v_x_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
lean_object* v___x_516_; 
lean_inc(v___y_510_);
lean_inc_ref(v___y_509_);
lean_inc(v___y_508_);
lean_inc_ref(v___y_507_);
v___x_516_ = lean_apply_9(v_x_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, lean_box(0));
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg___lam__0___boxed(lean_object* v_x_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg___lam__0(v_x_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg(lean_object* v_mvarId_528_, lean_object* v_x_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
lean_object* v___f_539_; lean_object* v___x_540_; 
lean_inc(v___y_533_);
lean_inc_ref(v___y_532_);
lean_inc(v___y_531_);
lean_inc_ref(v___y_530_);
v___f_539_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_539_, 0, v_x_529_);
lean_closure_set(v___f_539_, 1, v___y_530_);
lean_closure_set(v___f_539_, 2, v___y_531_);
lean_closure_set(v___f_539_, 3, v___y_532_);
lean_closure_set(v___f_539_, 4, v___y_533_);
v___x_540_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_528_, v___f_539_, v___y_534_, v___y_535_, v___y_536_, v___y_537_);
if (lean_obj_tag(v___x_540_) == 0)
{
return v___x_540_;
}
else
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
v_a_541_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_540_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_540_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(lean_object* v_00_u03b1_561_, lean_object* v_mvarId_562_, lean_object* v_x_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg(v_mvarId_562_, v_x_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___boxed(lean_object* v_00_u03b1_574_, lean_object* v_mvarId_575_, lean_object* v_x_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(v_00_u03b1_574_, v_mvarId_575_, v_x_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
return v_res_586_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_587_ = lean_unsigned_to_nat(32u);
v___x_588_ = lean_mk_empty_array_with_capacity(v___x_587_);
v___x_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
return v___x_589_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__1(void){
_start:
{
size_t v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_590_ = ((size_t)5ULL);
v___x_591_ = lean_unsigned_to_nat(0u);
v___x_592_ = lean_unsigned_to_nat(32u);
v___x_593_ = lean_mk_empty_array_with_capacity(v___x_592_);
v___x_594_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__0);
v___x_595_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_595_, 0, v___x_594_);
lean_ctor_set(v___x_595_, 1, v___x_593_);
lean_ctor_set(v___x_595_, 2, v___x_591_);
lean_ctor_set(v___x_595_, 3, v___x_591_);
lean_ctor_set_usize(v___x_595_, 4, v___x_590_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(lean_object* v___y_596_){
_start:
{
lean_object* v___x_598_; lean_object* v_infoState_599_; lean_object* v_trees_600_; lean_object* v___x_601_; lean_object* v_infoState_602_; lean_object* v_env_603_; lean_object* v_nextMacroScope_604_; lean_object* v_ngen_605_; lean_object* v_auxDeclNGen_606_; lean_object* v_traceState_607_; lean_object* v_cache_608_; lean_object* v_messages_609_; lean_object* v_snapshotTasks_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_631_; 
v___x_598_ = lean_st_ref_get(v___y_596_);
v_infoState_599_ = lean_ctor_get(v___x_598_, 7);
lean_inc_ref(v_infoState_599_);
lean_dec(v___x_598_);
v_trees_600_ = lean_ctor_get(v_infoState_599_, 2);
lean_inc_ref(v_trees_600_);
lean_dec_ref(v_infoState_599_);
v___x_601_ = lean_st_ref_take(v___y_596_);
v_infoState_602_ = lean_ctor_get(v___x_601_, 7);
v_env_603_ = lean_ctor_get(v___x_601_, 0);
v_nextMacroScope_604_ = lean_ctor_get(v___x_601_, 1);
v_ngen_605_ = lean_ctor_get(v___x_601_, 2);
v_auxDeclNGen_606_ = lean_ctor_get(v___x_601_, 3);
v_traceState_607_ = lean_ctor_get(v___x_601_, 4);
v_cache_608_ = lean_ctor_get(v___x_601_, 5);
v_messages_609_ = lean_ctor_get(v___x_601_, 6);
v_snapshotTasks_610_ = lean_ctor_get(v___x_601_, 8);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_631_ == 0)
{
v___x_612_ = v___x_601_;
v_isShared_613_ = v_isSharedCheck_631_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_snapshotTasks_610_);
lean_inc(v_infoState_602_);
lean_inc(v_messages_609_);
lean_inc(v_cache_608_);
lean_inc(v_traceState_607_);
lean_inc(v_auxDeclNGen_606_);
lean_inc(v_ngen_605_);
lean_inc(v_nextMacroScope_604_);
lean_inc(v_env_603_);
lean_dec(v___x_601_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_631_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
uint8_t v_enabled_614_; lean_object* v_assignment_615_; lean_object* v_lazyAssignment_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_629_; 
v_enabled_614_ = lean_ctor_get_uint8(v_infoState_602_, sizeof(void*)*3);
v_assignment_615_ = lean_ctor_get(v_infoState_602_, 0);
v_lazyAssignment_616_ = lean_ctor_get(v_infoState_602_, 1);
v_isSharedCheck_629_ = !lean_is_exclusive(v_infoState_602_);
if (v_isSharedCheck_629_ == 0)
{
lean_object* v_unused_630_; 
v_unused_630_ = lean_ctor_get(v_infoState_602_, 2);
lean_dec(v_unused_630_);
v___x_618_ = v_infoState_602_;
v_isShared_619_ = v_isSharedCheck_629_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_lazyAssignment_616_);
lean_inc(v_assignment_615_);
lean_dec(v_infoState_602_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_629_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_620_; lean_object* v___x_622_; 
v___x_620_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__1);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 2, v___x_620_);
v___x_622_ = v___x_618_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_assignment_615_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v_lazyAssignment_616_);
lean_ctor_set(v_reuseFailAlloc_628_, 2, v___x_620_);
lean_ctor_set_uint8(v_reuseFailAlloc_628_, sizeof(void*)*3, v_enabled_614_);
v___x_622_ = v_reuseFailAlloc_628_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
lean_object* v___x_624_; 
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 7, v___x_622_);
v___x_624_ = v___x_612_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_env_603_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v_nextMacroScope_604_);
lean_ctor_set(v_reuseFailAlloc_627_, 2, v_ngen_605_);
lean_ctor_set(v_reuseFailAlloc_627_, 3, v_auxDeclNGen_606_);
lean_ctor_set(v_reuseFailAlloc_627_, 4, v_traceState_607_);
lean_ctor_set(v_reuseFailAlloc_627_, 5, v_cache_608_);
lean_ctor_set(v_reuseFailAlloc_627_, 6, v_messages_609_);
lean_ctor_set(v_reuseFailAlloc_627_, 7, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_627_, 8, v_snapshotTasks_610_);
v___x_624_ = v_reuseFailAlloc_627_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = lean_st_ref_put(v___y_596_, v___x_624_);
v___x_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_626_, 0, v_trees_600_);
return v___x_626_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___boxed(lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___y_632_);
lean_dec(v___y_632_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6(lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___y_642_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___boxed(lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6(v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(lean_object* v_msg_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v___f_666_; lean_object* v___x_83782__overap_667_; lean_object* v___x_668_; 
v___f_666_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___closed__0));
v___x_83782__overap_667_ = lean_panic_fn_borrowed(v___f_666_, v_msg_656_);
lean_inc(v___y_664_);
lean_inc_ref(v___y_663_);
lean_inc(v___y_662_);
lean_inc_ref(v___y_661_);
lean_inc(v___y_660_);
lean_inc_ref(v___y_659_);
lean_inc(v___y_658_);
lean_inc_ref(v___y_657_);
v___x_668_ = lean_apply_9(v___x_83782__overap_667_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, lean_box(0));
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___boxed(lean_object* v_msg_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v_msg_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0(lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v_ref_689_; uint8_t v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v_ref_689_ = lean_ctor_get(v___y_686_, 2);
v___x_690_ = 0;
v___x_691_ = l_Lean_SourceInfo_fromRef(v_ref_689_, v___x_690_);
v___x_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0___boxed(lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0(v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
return v_res_702_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6(void){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_Array_mkArray0___redArg();
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1(lean_object* v___x_719_, lean_object* v___x_720_, lean_object* v_args_721_, lean_object* v_only_722_, uint8_t v___x_723_, lean_object* v___x_724_, lean_object* v___x_725_, lean_object* v___x_726_, lean_object* v___y_727_, lean_object* v_unfold_728_, uint8_t v___x_729_, lean_object* v_squeeze_730_, lean_object* v_loc_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v___y_773_; lean_object* v___y_774_; lean_object* v___y_775_; lean_object* v___y_776_; lean_object* v___y_789_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; uint8_t v___y_804_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_869_; uint8_t v___y_879_; 
if (lean_obj_tag(v_squeeze_730_) == 0)
{
uint8_t v___x_892_; 
v___x_892_ = 0;
v___y_879_ = v___x_892_;
goto v___jp_878_;
}
else
{
lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_1028_; 
v_isSharedCheck_1028_ = !lean_is_exclusive(v_squeeze_730_);
if (v_isSharedCheck_1028_ == 0)
{
lean_object* v_unused_1029_; 
v_unused_1029_ = lean_ctor_get(v_squeeze_730_, 0);
lean_dec(v_unused_1029_);
v___x_894_ = v_squeeze_730_;
v_isShared_895_ = v_isSharedCheck_1028_;
goto v_resetjp_893_;
}
else
{
lean_dec(v_squeeze_730_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_1028_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
if (v___x_729_ == 0)
{
lean_del_object(v___x_894_);
v___y_879_ = v___x_729_;
goto v___jp_878_;
}
else
{
if (lean_obj_tag(v_unfold_728_) == 0)
{
lean_object* v_ref_896_; uint8_t v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v___y_930_; lean_object* v___y_931_; lean_object* v___y_947_; 
v_ref_896_ = lean_ctor_get(v___y_738_, 2);
v___x_897_ = 0;
v___x_898_ = l_Lean_SourceInfo_fromRef(v_ref_896_, v___x_897_);
v___x_899_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__9));
lean_inc_ref_n(v___x_726_, 2);
lean_inc_ref_n(v___x_725_, 2);
lean_inc_ref_n(v___x_724_, 2);
v___x_900_ = l_Lean_Name_mkStr4(v___x_724_, v___x_725_, v___x_726_, v___x_899_);
v___x_901_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__10));
lean_inc_n(v___x_898_, 2);
v___x_902_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_898_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_904_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6);
v___x_905_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_905_, 0, v___x_898_);
lean_ctor_set(v___x_905_, 1, v___x_903_);
lean_ctor_set(v___x_905_, 2, v___x_904_);
v___x_906_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__11));
v___x_907_ = l_Lean_Name_mkStr4(v___x_724_, v___x_725_, v___x_726_, v___x_906_);
if (lean_obj_tag(v___y_727_) == 0)
{
lean_object* v___x_956_; 
v___x_956_ = lean_mk_empty_array_with_capacity(v___x_720_);
v___y_947_ = v___x_956_;
goto v___jp_946_;
}
else
{
lean_object* v_val_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v_val_957_ = lean_ctor_get(v___y_727_, 0);
lean_inc(v_val_957_);
lean_dec_ref_known(v___y_727_, 1);
v___x_958_ = lean_mk_empty_array_with_capacity(v___x_720_);
v___x_959_ = lean_array_push(v___x_958_, v_val_957_);
v___y_947_ = v___x_959_;
goto v___jp_946_;
}
v___jp_908_:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_918_; 
v___x_913_ = l_Array_append___redArg(v___x_904_, v___y_912_);
lean_dec_ref(v___y_912_);
lean_inc_n(v___x_898_, 2);
v___x_914_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_914_, 0, v___x_898_);
lean_ctor_set(v___x_914_, 1, v___x_903_);
lean_ctor_set(v___x_914_, 2, v___x_913_);
v___x_915_ = l_Lean_Syntax_node5(v___x_898_, v___x_907_, v___x_719_, v___y_911_, v___y_910_, v___y_909_, v___x_914_);
v___x_916_ = l_Lean_Syntax_node3(v___x_898_, v___x_900_, v___x_902_, v___x_905_, v___x_915_);
if (v_isShared_895_ == 0)
{
lean_ctor_set_tag(v___x_894_, 0);
lean_ctor_set(v___x_894_, 0, v___x_916_);
v___x_918_ = v___x_894_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_916_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
v___jp_920_:
{
lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_924_ = l_Array_append___redArg(v___x_904_, v___y_923_);
lean_dec_ref(v___y_923_);
lean_inc(v___x_898_);
v___x_925_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_925_, 0, v___x_898_);
lean_ctor_set(v___x_925_, 1, v___x_903_);
lean_ctor_set(v___x_925_, 2, v___x_924_);
if (lean_obj_tag(v_loc_731_) == 1)
{
lean_object* v_val_926_; lean_object* v___x_927_; 
v_val_926_ = lean_ctor_get(v_loc_731_, 0);
lean_inc(v_val_926_);
lean_dec_ref_known(v_loc_731_, 1);
v___x_927_ = l_Array_mkArray1___redArg(v_val_926_);
v___y_909_ = v___x_925_;
v___y_910_ = v___y_921_;
v___y_911_ = v___y_922_;
v___y_912_ = v___x_927_;
goto v___jp_908_;
}
else
{
lean_object* v___x_928_; 
lean_dec(v_loc_731_);
v___x_928_ = lean_mk_empty_array_with_capacity(v___x_720_);
v___y_909_ = v___x_925_;
v___y_910_ = v___y_921_;
v___y_911_ = v___y_922_;
v___y_912_ = v___x_928_;
goto v___jp_908_;
}
}
v___jp_929_:
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = l_Array_append___redArg(v___x_904_, v___y_931_);
lean_dec_ref(v___y_931_);
lean_inc(v___x_898_);
v___x_933_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_933_, 0, v___x_898_);
lean_ctor_set(v___x_933_, 1, v___x_903_);
lean_ctor_set(v___x_933_, 2, v___x_932_);
if (lean_obj_tag(v_args_721_) == 1)
{
lean_object* v_val_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v_val_934_ = lean_ctor_get(v_args_721_, 0);
v___x_935_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_936_ = l_Lean_Name_mkStr4(v___x_724_, v___x_725_, v___x_726_, v___x_935_);
v___x_937_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___x_898_, 4);
v___x_938_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_898_);
lean_ctor_set(v___x_938_, 1, v___x_937_);
v___x_939_ = l_Array_append___redArg(v___x_904_, v_val_934_);
v___x_940_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_940_, 0, v___x_898_);
lean_ctor_set(v___x_940_, 1, v___x_903_);
lean_ctor_set(v___x_940_, 2, v___x_939_);
v___x_941_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_942_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_898_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
v___x_943_ = l_Lean_Syntax_node3(v___x_898_, v___x_936_, v___x_938_, v___x_940_, v___x_942_);
v___x_944_ = l_Array_mkArray1___redArg(v___x_943_);
v___y_921_ = v___x_933_;
v___y_922_ = v___y_930_;
v___y_923_ = v___x_944_;
goto v___jp_920_;
}
else
{
lean_object* v___x_945_; 
lean_dec_ref(v___x_726_);
lean_dec_ref(v___x_725_);
lean_dec_ref(v___x_724_);
v___x_945_ = lean_mk_empty_array_with_capacity(v___x_720_);
v___y_921_ = v___x_933_;
v___y_922_ = v___y_930_;
v___y_923_ = v___x_945_;
goto v___jp_920_;
}
}
v___jp_946_:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = l_Array_append___redArg(v___x_904_, v___y_947_);
lean_dec_ref(v___y_947_);
lean_inc(v___x_898_);
v___x_949_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_949_, 0, v___x_898_);
lean_ctor_set(v___x_949_, 1, v___x_903_);
lean_ctor_set(v___x_949_, 2, v___x_948_);
if (lean_obj_tag(v_only_722_) == 1)
{
lean_object* v_val_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v_val_950_ = lean_ctor_get(v_only_722_, 0);
v___x_951_ = l_Lean_SourceInfo_fromRef(v_val_950_, v___x_723_);
v___x_952_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_953_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_951_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
v___x_954_ = l_Array_mkArray1___redArg(v___x_953_);
v___y_930_ = v___x_949_;
v___y_931_ = v___x_954_;
goto v___jp_929_;
}
else
{
lean_object* v___x_955_; 
v___x_955_ = lean_mk_empty_array_with_capacity(v___x_720_);
v___y_930_ = v___x_949_;
v___y_931_ = v___x_955_;
goto v___jp_929_;
}
}
}
else
{
lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_1026_; 
lean_del_object(v___x_894_);
v_isSharedCheck_1026_ = !lean_is_exclusive(v_unfold_728_);
if (v_isSharedCheck_1026_ == 0)
{
lean_object* v_unused_1027_; 
v_unused_1027_ = lean_ctor_get(v_unfold_728_, 0);
lean_dec(v_unused_1027_);
v___x_961_ = v_unfold_728_;
v_isShared_962_ = v_isSharedCheck_1026_;
goto v_resetjp_960_;
}
else
{
lean_dec(v_unfold_728_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_1026_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v_ref_963_; uint8_t v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_996_; lean_object* v___y_997_; lean_object* v___y_1013_; 
v_ref_963_ = lean_ctor_get(v___y_738_, 2);
v___x_964_ = 0;
v___x_965_ = l_Lean_SourceInfo_fromRef(v_ref_963_, v___x_964_);
v___x_966_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__13));
lean_inc_ref_n(v___x_726_, 2);
lean_inc_ref_n(v___x_725_, 2);
lean_inc_ref_n(v___x_724_, 2);
v___x_967_ = l_Lean_Name_mkStr4(v___x_724_, v___x_725_, v___x_726_, v___x_966_);
v___x_968_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__14));
lean_inc(v___x_965_);
v___x_969_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_965_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
v___x_970_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__11));
v___x_971_ = l_Lean_Name_mkStr4(v___x_724_, v___x_725_, v___x_726_, v___x_970_);
v___x_972_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_973_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6);
if (lean_obj_tag(v___y_727_) == 0)
{
lean_object* v___x_1022_; 
v___x_1022_ = lean_mk_empty_array_with_capacity(v___x_720_);
v___y_1013_ = v___x_1022_;
goto v___jp_1012_;
}
else
{
lean_object* v_val_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v_val_1023_ = lean_ctor_get(v___y_727_, 0);
lean_inc(v_val_1023_);
lean_dec_ref_known(v___y_727_, 1);
v___x_1024_ = lean_mk_empty_array_with_capacity(v___x_720_);
v___x_1025_ = lean_array_push(v___x_1024_, v_val_1023_);
v___y_1013_ = v___x_1025_;
goto v___jp_1012_;
}
v___jp_974_:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_984_; 
v___x_979_ = l_Array_append___redArg(v___x_973_, v___y_978_);
lean_dec_ref(v___y_978_);
lean_inc_n(v___x_965_, 2);
v___x_980_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_980_, 0, v___x_965_);
lean_ctor_set(v___x_980_, 1, v___x_972_);
lean_ctor_set(v___x_980_, 2, v___x_979_);
v___x_981_ = l_Lean_Syntax_node5(v___x_965_, v___x_971_, v___x_719_, v___y_977_, v___y_975_, v___y_976_, v___x_980_);
v___x_982_ = l_Lean_Syntax_node2(v___x_965_, v___x_967_, v___x_969_, v___x_981_);
if (v_isShared_962_ == 0)
{
lean_ctor_set_tag(v___x_961_, 0);
lean_ctor_set(v___x_961_, 0, v___x_982_);
v___x_984_ = v___x_961_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_982_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
v___jp_986_:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = l_Array_append___redArg(v___x_973_, v___y_989_);
lean_dec_ref(v___y_989_);
lean_inc(v___x_965_);
v___x_991_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_991_, 0, v___x_965_);
lean_ctor_set(v___x_991_, 1, v___x_972_);
lean_ctor_set(v___x_991_, 2, v___x_990_);
if (lean_obj_tag(v_loc_731_) == 1)
{
lean_object* v_val_992_; lean_object* v___x_993_; 
v_val_992_ = lean_ctor_get(v_loc_731_, 0);
lean_inc(v_val_992_);
lean_dec_ref_known(v_loc_731_, 1);
v___x_993_ = l_Array_mkArray1___redArg(v_val_992_);
v___y_975_ = v___y_987_;
v___y_976_ = v___x_991_;
v___y_977_ = v___y_988_;
v___y_978_ = v___x_993_;
goto v___jp_974_;
}
else
{
lean_object* v___x_994_; 
lean_dec(v_loc_731_);
v___x_994_ = lean_mk_empty_array_with_capacity(v___x_720_);
v___y_975_ = v___y_987_;
v___y_976_ = v___x_991_;
v___y_977_ = v___y_988_;
v___y_978_ = v___x_994_;
goto v___jp_974_;
}
}
v___jp_995_:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = l_Array_append___redArg(v___x_973_, v___y_997_);
lean_dec_ref(v___y_997_);
lean_inc(v___x_965_);
v___x_999_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_999_, 0, v___x_965_);
lean_ctor_set(v___x_999_, 1, v___x_972_);
lean_ctor_set(v___x_999_, 2, v___x_998_);
if (lean_obj_tag(v_args_721_) == 1)
{
lean_object* v_val_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v_val_1000_ = lean_ctor_get(v_args_721_, 0);
v___x_1001_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_1002_ = l_Lean_Name_mkStr4(v___x_724_, v___x_725_, v___x_726_, v___x_1001_);
v___x_1003_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___x_965_, 4);
v___x_1004_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_965_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = l_Array_append___redArg(v___x_973_, v_val_1000_);
v___x_1006_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1006_, 0, v___x_965_);
lean_ctor_set(v___x_1006_, 1, v___x_972_);
lean_ctor_set(v___x_1006_, 2, v___x_1005_);
v___x_1007_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_1008_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_965_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
v___x_1009_ = l_Lean_Syntax_node3(v___x_965_, v___x_1002_, v___x_1004_, v___x_1006_, v___x_1008_);
v___x_1010_ = l_Array_mkArray1___redArg(v___x_1009_);
v___y_987_ = v___x_999_;
v___y_988_ = v___y_996_;
v___y_989_ = v___x_1010_;
goto v___jp_986_;
}
else
{
lean_object* v___x_1011_; 
lean_dec_ref(v___x_726_);
lean_dec_ref(v___x_725_);
lean_dec_ref(v___x_724_);
v___x_1011_ = lean_mk_empty_array_with_capacity(v___x_720_);
v___y_987_ = v___x_999_;
v___y_988_ = v___y_996_;
v___y_989_ = v___x_1011_;
goto v___jp_986_;
}
}
v___jp_1012_:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = l_Array_append___redArg(v___x_973_, v___y_1013_);
lean_dec_ref(v___y_1013_);
lean_inc(v___x_965_);
v___x_1015_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1015_, 0, v___x_965_);
lean_ctor_set(v___x_1015_, 1, v___x_972_);
lean_ctor_set(v___x_1015_, 2, v___x_1014_);
if (lean_obj_tag(v_only_722_) == 1)
{
lean_object* v_val_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v_val_1016_ = lean_ctor_get(v_only_722_, 0);
v___x_1017_ = l_Lean_SourceInfo_fromRef(v_val_1016_, v___x_723_);
v___x_1018_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_1019_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1017_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = l_Array_mkArray1___redArg(v___x_1019_);
v___y_996_ = v___x_1015_;
v___y_997_ = v___x_1020_;
goto v___jp_995_;
}
else
{
lean_object* v___x_1021_; 
v___x_1021_ = lean_mk_empty_array_with_capacity(v___x_720_);
v___y_996_ = v___x_1015_;
v___y_997_ = v___x_1021_;
goto v___jp_995_;
}
}
}
}
}
}
}
v___jp_741_:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
lean_inc_ref(v___y_743_);
v___x_751_ = l_Array_append___redArg(v___y_743_, v___y_750_);
lean_dec_ref(v___y_750_);
lean_inc(v___y_747_);
lean_inc(v___y_749_);
v___x_752_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_752_, 0, v___y_749_);
lean_ctor_set(v___x_752_, 1, v___y_747_);
lean_ctor_set(v___x_752_, 2, v___x_751_);
v___x_753_ = l_Lean_Syntax_node6(v___y_749_, v___y_744_, v___y_746_, v___x_719_, v___y_742_, v___y_748_, v___y_745_, v___x_752_);
v___x_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
return v___x_754_;
}
v___jp_755_:
{
lean_object* v___x_764_; lean_object* v___x_765_; 
lean_inc_ref(v___y_757_);
v___x_764_ = l_Array_append___redArg(v___y_757_, v___y_763_);
lean_dec_ref(v___y_763_);
lean_inc(v___y_760_);
lean_inc(v___y_762_);
v___x_765_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_765_, 0, v___y_762_);
lean_ctor_set(v___x_765_, 1, v___y_760_);
lean_ctor_set(v___x_765_, 2, v___x_764_);
if (lean_obj_tag(v_loc_731_) == 1)
{
lean_object* v_val_766_; lean_object* v___x_767_; 
v_val_766_ = lean_ctor_get(v_loc_731_, 0);
lean_inc(v_val_766_);
lean_dec_ref_known(v_loc_731_, 1);
v___x_767_ = l_Array_mkArray1___redArg(v_val_766_);
v___y_742_ = v___y_756_;
v___y_743_ = v___y_757_;
v___y_744_ = v___y_758_;
v___y_745_ = v___x_765_;
v___y_746_ = v___y_759_;
v___y_747_ = v___y_760_;
v___y_748_ = v___y_761_;
v___y_749_ = v___y_762_;
v___y_750_ = v___x_767_;
goto v___jp_741_;
}
else
{
lean_object* v___x_768_; 
lean_dec(v_loc_731_);
v___x_768_ = lean_mk_empty_array_with_capacity(v___x_720_);
v___y_742_ = v___y_756_;
v___y_743_ = v___y_757_;
v___y_744_ = v___y_758_;
v___y_745_ = v___x_765_;
v___y_746_ = v___y_759_;
v___y_747_ = v___y_760_;
v___y_748_ = v___y_761_;
v___y_749_ = v___y_762_;
v___y_750_ = v___x_768_;
goto v___jp_741_;
}
}
v___jp_769_:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
lean_inc_ref(v___y_771_);
v___x_777_ = l_Array_append___redArg(v___y_771_, v___y_776_);
lean_dec_ref(v___y_776_);
lean_inc(v___y_774_);
lean_inc(v___y_775_);
v___x_778_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_778_, 0, v___y_775_);
lean_ctor_set(v___x_778_, 1, v___y_774_);
lean_ctor_set(v___x_778_, 2, v___x_777_);
if (lean_obj_tag(v_args_721_) == 1)
{
lean_object* v_val_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v_val_779_ = lean_ctor_get(v_args_721_, 0);
v___x_780_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_775_, 3);
v___x_781_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_781_, 0, v___y_775_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
lean_inc_ref(v___y_771_);
v___x_782_ = l_Array_append___redArg(v___y_771_, v_val_779_);
lean_inc(v___y_774_);
v___x_783_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_783_, 0, v___y_775_);
lean_ctor_set(v___x_783_, 1, v___y_774_);
lean_ctor_set(v___x_783_, 2, v___x_782_);
v___x_784_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_785_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_785_, 0, v___y_775_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
v___x_786_ = l_Array_mkArray3___redArg(v___x_781_, v___x_783_, v___x_785_);
v___y_756_ = v___y_770_;
v___y_757_ = v___y_771_;
v___y_758_ = v___y_772_;
v___y_759_ = v___y_773_;
v___y_760_ = v___y_774_;
v___y_761_ = v___x_778_;
v___y_762_ = v___y_775_;
v___y_763_ = v___x_786_;
goto v___jp_755_;
}
else
{
lean_object* v___x_787_; 
v___x_787_ = lean_mk_empty_array_with_capacity(v___x_720_);
v___y_756_ = v___y_770_;
v___y_757_ = v___y_771_;
v___y_758_ = v___y_772_;
v___y_759_ = v___y_773_;
v___y_760_ = v___y_774_;
v___y_761_ = v___x_778_;
v___y_762_ = v___y_775_;
v___y_763_ = v___x_787_;
goto v___jp_755_;
}
}
v___jp_788_:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
lean_inc_ref(v___y_789_);
v___x_795_ = l_Array_append___redArg(v___y_789_, v___y_794_);
lean_dec_ref(v___y_794_);
lean_inc(v___y_792_);
lean_inc(v___y_793_);
v___x_796_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_796_, 0, v___y_793_);
lean_ctor_set(v___x_796_, 1, v___y_792_);
lean_ctor_set(v___x_796_, 2, v___x_795_);
if (lean_obj_tag(v_only_722_) == 1)
{
lean_object* v_val_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v_val_797_ = lean_ctor_get(v_only_722_, 0);
v___x_798_ = l_Lean_SourceInfo_fromRef(v_val_797_, v___x_723_);
v___x_799_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_800_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_798_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
v___x_801_ = l_Array_mkArray1___redArg(v___x_800_);
v___y_770_ = v___x_796_;
v___y_771_ = v___y_789_;
v___y_772_ = v___y_790_;
v___y_773_ = v___y_791_;
v___y_774_ = v___y_792_;
v___y_775_ = v___y_793_;
v___y_776_ = v___x_801_;
goto v___jp_769_;
}
else
{
lean_object* v___x_802_; 
v___x_802_ = lean_mk_empty_array_with_capacity(v___x_720_);
v___y_770_ = v___x_796_;
v___y_771_ = v___y_789_;
v___y_772_ = v___y_790_;
v___y_773_ = v___y_791_;
v___y_774_ = v___y_792_;
v___y_775_ = v___y_793_;
v___y_776_ = v___x_802_;
goto v___jp_769_;
}
}
v___jp_803_:
{
lean_object* v_ref_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v_ref_805_ = lean_ctor_get(v___y_738_, 2);
v___x_806_ = l_Lean_SourceInfo_fromRef(v_ref_805_, v___y_804_);
v___x_807_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__3));
v___x_808_ = l_Lean_Name_mkStr4(v___x_724_, v___x_725_, v___x_726_, v___x_807_);
lean_inc(v___x_806_);
v___x_809_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_806_);
lean_ctor_set(v___x_809_, 1, v___x_807_);
v___x_810_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_811_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6);
if (lean_obj_tag(v___y_727_) == 0)
{
lean_object* v___x_812_; 
v___x_812_ = lean_mk_empty_array_with_capacity(v___x_720_);
v___y_789_ = v___x_811_;
v___y_790_ = v___x_808_;
v___y_791_ = v___x_809_;
v___y_792_ = v___x_810_;
v___y_793_ = v___x_806_;
v___y_794_ = v___x_812_;
goto v___jp_788_;
}
else
{
lean_object* v_val_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v_val_813_ = lean_ctor_get(v___y_727_, 0);
lean_inc(v_val_813_);
lean_dec_ref_known(v___y_727_, 1);
v___x_814_ = lean_mk_empty_array_with_capacity(v___x_720_);
v___x_815_ = lean_array_push(v___x_814_, v_val_813_);
v___y_789_ = v___x_811_;
v___y_790_ = v___x_808_;
v___y_791_ = v___x_809_;
v___y_792_ = v___x_810_;
v___y_793_ = v___x_806_;
v___y_794_ = v___x_815_;
goto v___jp_788_;
}
}
v___jp_816_:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
lean_inc_ref(v___y_824_);
v___x_826_ = l_Array_append___redArg(v___y_824_, v___y_825_);
lean_dec_ref(v___y_825_);
lean_inc(v___y_818_);
lean_inc(v___y_822_);
v___x_827_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_827_, 0, v___y_822_);
lean_ctor_set(v___x_827_, 1, v___y_818_);
lean_ctor_set(v___x_827_, 2, v___x_826_);
v___x_828_ = l_Lean_Syntax_node6(v___y_822_, v___y_821_, v___y_817_, v___x_719_, v___y_820_, v___y_823_, v___y_819_, v___x_827_);
v___x_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
return v___x_829_;
}
v___jp_830_:
{
lean_object* v___x_839_; lean_object* v___x_840_; 
lean_inc_ref(v___y_837_);
v___x_839_ = l_Array_append___redArg(v___y_837_, v___y_838_);
lean_dec_ref(v___y_838_);
lean_inc(v___y_832_);
lean_inc(v___y_835_);
v___x_840_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_840_, 0, v___y_835_);
lean_ctor_set(v___x_840_, 1, v___y_832_);
lean_ctor_set(v___x_840_, 2, v___x_839_);
if (lean_obj_tag(v_loc_731_) == 1)
{
lean_object* v_val_841_; lean_object* v___x_842_; 
v_val_841_ = lean_ctor_get(v_loc_731_, 0);
lean_inc(v_val_841_);
lean_dec_ref_known(v_loc_731_, 1);
v___x_842_ = l_Array_mkArray1___redArg(v_val_841_);
v___y_817_ = v___y_831_;
v___y_818_ = v___y_832_;
v___y_819_ = v___x_840_;
v___y_820_ = v___y_833_;
v___y_821_ = v___y_834_;
v___y_822_ = v___y_835_;
v___y_823_ = v___y_836_;
v___y_824_ = v___y_837_;
v___y_825_ = v___x_842_;
goto v___jp_816_;
}
else
{
lean_object* v___x_843_; 
lean_dec(v_loc_731_);
v___x_843_ = lean_mk_empty_array_with_capacity(v___x_720_);
v___y_817_ = v___y_831_;
v___y_818_ = v___y_832_;
v___y_819_ = v___x_840_;
v___y_820_ = v___y_833_;
v___y_821_ = v___y_834_;
v___y_822_ = v___y_835_;
v___y_823_ = v___y_836_;
v___y_824_ = v___y_837_;
v___y_825_ = v___x_843_;
goto v___jp_816_;
}
}
v___jp_844_:
{
lean_object* v___x_852_; lean_object* v___x_853_; 
lean_inc_ref(v___y_850_);
v___x_852_ = l_Array_append___redArg(v___y_850_, v___y_851_);
lean_dec_ref(v___y_851_);
lean_inc(v___y_846_);
lean_inc(v___y_849_);
v___x_853_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_853_, 0, v___y_849_);
lean_ctor_set(v___x_853_, 1, v___y_846_);
lean_ctor_set(v___x_853_, 2, v___x_852_);
if (lean_obj_tag(v_args_721_) == 1)
{
lean_object* v_val_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v_val_854_ = lean_ctor_get(v_args_721_, 0);
v___x_855_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_849_, 3);
v___x_856_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_856_, 0, v___y_849_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
lean_inc_ref(v___y_850_);
v___x_857_ = l_Array_append___redArg(v___y_850_, v_val_854_);
lean_inc(v___y_846_);
v___x_858_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_858_, 0, v___y_849_);
lean_ctor_set(v___x_858_, 1, v___y_846_);
lean_ctor_set(v___x_858_, 2, v___x_857_);
v___x_859_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_860_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_860_, 0, v___y_849_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
v___x_861_ = l_Array_mkArray3___redArg(v___x_856_, v___x_858_, v___x_860_);
v___y_831_ = v___y_845_;
v___y_832_ = v___y_846_;
v___y_833_ = v___y_847_;
v___y_834_ = v___y_848_;
v___y_835_ = v___y_849_;
v___y_836_ = v___x_853_;
v___y_837_ = v___y_850_;
v___y_838_ = v___x_861_;
goto v___jp_830_;
}
else
{
lean_object* v___x_862_; 
v___x_862_ = lean_mk_empty_array_with_capacity(v___x_720_);
v___y_831_ = v___y_845_;
v___y_832_ = v___y_846_;
v___y_833_ = v___y_847_;
v___y_834_ = v___y_848_;
v___y_835_ = v___y_849_;
v___y_836_ = v___x_853_;
v___y_837_ = v___y_850_;
v___y_838_ = v___x_862_;
goto v___jp_830_;
}
}
v___jp_863_:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
lean_inc_ref(v___y_868_);
v___x_870_ = l_Array_append___redArg(v___y_868_, v___y_869_);
lean_dec_ref(v___y_869_);
lean_inc(v___y_865_);
lean_inc(v___y_867_);
v___x_871_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_871_, 0, v___y_867_);
lean_ctor_set(v___x_871_, 1, v___y_865_);
lean_ctor_set(v___x_871_, 2, v___x_870_);
if (lean_obj_tag(v_only_722_) == 1)
{
lean_object* v_val_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v_val_872_ = lean_ctor_get(v_only_722_, 0);
v___x_873_ = l_Lean_SourceInfo_fromRef(v_val_872_, v___x_723_);
v___x_874_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_875_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_873_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
v___x_876_ = l_Array_mkArray1___redArg(v___x_875_);
v___y_845_ = v___y_864_;
v___y_846_ = v___y_865_;
v___y_847_ = v___x_871_;
v___y_848_ = v___y_866_;
v___y_849_ = v___y_867_;
v___y_850_ = v___y_868_;
v___y_851_ = v___x_876_;
goto v___jp_844_;
}
else
{
lean_object* v___x_877_; 
v___x_877_ = lean_mk_empty_array_with_capacity(v___x_720_);
v___y_845_ = v___y_864_;
v___y_846_ = v___y_865_;
v___y_847_ = v___x_871_;
v___y_848_ = v___y_866_;
v___y_849_ = v___y_867_;
v___y_850_ = v___y_868_;
v___y_851_ = v___x_877_;
goto v___jp_844_;
}
}
v___jp_878_:
{
if (lean_obj_tag(v_unfold_728_) == 0)
{
v___y_804_ = v___y_879_;
goto v___jp_803_;
}
else
{
lean_dec_ref_known(v_unfold_728_, 1);
if (v___x_729_ == 0)
{
v___y_804_ = v___x_729_;
goto v___jp_803_;
}
else
{
lean_object* v_ref_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v_ref_880_ = lean_ctor_get(v___y_738_, 2);
v___x_881_ = l_Lean_SourceInfo_fromRef(v_ref_880_, v___y_879_);
v___x_882_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__7));
v___x_883_ = l_Lean_Name_mkStr4(v___x_724_, v___x_725_, v___x_726_, v___x_882_);
v___x_884_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__8));
lean_inc(v___x_881_);
v___x_885_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_881_);
lean_ctor_set(v___x_885_, 1, v___x_884_);
v___x_886_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_887_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6);
if (lean_obj_tag(v___y_727_) == 0)
{
lean_object* v___x_888_; 
v___x_888_ = lean_mk_empty_array_with_capacity(v___x_720_);
v___y_864_ = v___x_885_;
v___y_865_ = v___x_886_;
v___y_866_ = v___x_883_;
v___y_867_ = v___x_881_;
v___y_868_ = v___x_887_;
v___y_869_ = v___x_888_;
goto v___jp_863_;
}
else
{
lean_object* v_val_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v_val_889_ = lean_ctor_get(v___y_727_, 0);
lean_inc(v_val_889_);
lean_dec_ref_known(v___y_727_, 1);
v___x_890_ = lean_mk_empty_array_with_capacity(v___x_720_);
v___x_891_ = lean_array_push(v___x_890_, v_val_889_);
v___y_864_ = v___x_885_;
v___y_865_ = v___x_886_;
v___y_866_ = v___x_883_;
v___y_867_ = v___x_881_;
v___y_868_ = v___x_887_;
v___y_869_ = v___x_891_;
goto v___jp_863_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___boxed(lean_object** _args){
lean_object* v___x_1030_ = _args[0];
lean_object* v___x_1031_ = _args[1];
lean_object* v_args_1032_ = _args[2];
lean_object* v_only_1033_ = _args[3];
lean_object* v___x_1034_ = _args[4];
lean_object* v___x_1035_ = _args[5];
lean_object* v___x_1036_ = _args[6];
lean_object* v___x_1037_ = _args[7];
lean_object* v___y_1038_ = _args[8];
lean_object* v_unfold_1039_ = _args[9];
lean_object* v___x_1040_ = _args[10];
lean_object* v_squeeze_1041_ = _args[11];
lean_object* v_loc_1042_ = _args[12];
lean_object* v___y_1043_ = _args[13];
lean_object* v___y_1044_ = _args[14];
lean_object* v___y_1045_ = _args[15];
lean_object* v___y_1046_ = _args[16];
lean_object* v___y_1047_ = _args[17];
lean_object* v___y_1048_ = _args[18];
lean_object* v___y_1049_ = _args[19];
lean_object* v___y_1050_ = _args[20];
lean_object* v___y_1051_ = _args[21];
_start:
{
uint8_t v___x_93030__boxed_1052_; uint8_t v___x_93035__boxed_1053_; lean_object* v_res_1054_; 
v___x_93030__boxed_1052_ = lean_unbox(v___x_1034_);
v___x_93035__boxed_1053_ = lean_unbox(v___x_1040_);
v_res_1054_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1(v___x_1030_, v___x_1031_, v_args_1032_, v_only_1033_, v___x_93030__boxed_1052_, v___x_1035_, v___x_1036_, v___x_1037_, v___y_1038_, v_unfold_1039_, v___x_93035__boxed_1053_, v_squeeze_1041_, v_loc_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v_only_1033_);
lean_dec(v_args_1032_);
lean_dec(v___x_1031_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2(lean_object* v_a_1055_, lean_object* v_trees_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v___x_1066_; 
lean_inc(v___y_1064_);
lean_inc_ref(v___y_1063_);
lean_inc(v___y_1062_);
lean_inc_ref(v___y_1061_);
lean_inc(v___y_1060_);
lean_inc_ref(v___y_1059_);
lean_inc(v___y_1058_);
lean_inc_ref(v___y_1057_);
v___x_1066_ = lean_apply_9(v_a_1055_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, lean_box(0));
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1075_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1069_ = v___x_1066_;
v_isShared_1070_ = v_isSharedCheck_1075_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1066_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1075_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1071_; lean_object* v___x_1073_; 
v___x_1071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1071_, 0, v_a_1067_);
lean_ctor_set(v___x_1071_, 1, v_trees_1056_);
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 0, v___x_1071_);
v___x_1073_ = v___x_1069_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1071_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
else
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
lean_dec_ref(v_trees_1056_);
v_a_1076_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1078_ = v___x_1066_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1066_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1076_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___boxed(lean_object* v_a_1084_, lean_object* v_trees_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2(v_a_1084_, v_trees_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
return v_res_1095_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__0));
v___x_1098_ = l_Lean_stringToMessageData(v___x_1097_);
return v___x_1098_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__3(void){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__2));
v___x_1101_ = l_Lean_stringToMessageData(v___x_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3(lean_object* v_a_1102_, lean_object* v_a_1103_, uint8_t v___x_1104_, lean_object* v_a_1105_, lean_object* v_mvarCounter_1106_, lean_object* v___x_1107_, uint8_t v___x_1108_, lean_object* v___x_1109_, uint8_t v_useReducible_1110_, uint8_t v___x_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v___x_1121_; 
lean_inc(v_a_1102_);
v___x_1121_ = l_Lean_MVarId_getType(v_a_1102_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc_n(v_a_1122_, 2);
lean_dec_ref_known(v___x_1121_, 1);
v___x_1123_ = l_Lean_mkIdent(v_a_1103_);
v___x_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1124_, 0, v_a_1122_);
v___x_1125_ = l_Lean_Elab_Term_elabTerm(v___x_1123_, v___x_1124_, v___x_1104_, v___x_1104_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v_a_1126_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1134_; lean_object* v___y_1135_; lean_object* v___x_1160_; 
v_a_1126_ = lean_ctor_get(v___x_1125_, 0);
lean_inc(v_a_1126_);
lean_dec_ref_known(v___x_1125_, 1);
v___x_1160_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_1108_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1343_; 
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1343_ == 0)
{
lean_object* v_unused_1344_; 
v_unused_1344_ = lean_ctor_get(v___x_1160_, 0);
lean_dec(v_unused_1344_);
v___x_1162_ = v___x_1160_;
v_isShared_1163_ = v_isSharedCheck_1343_;
goto v_resetjp_1161_;
}
else
{
lean_dec(v___x_1160_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1343_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1164_; 
lean_inc(v___y_1119_);
lean_inc_ref(v___y_1118_);
lean_inc(v___y_1117_);
lean_inc_ref(v___y_1116_);
lean_inc(v_a_1126_);
v___x_1164_ = lean_infer_type(v_a_1126_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1165_; uint8_t v_____do__lift_1167_; lean_object* v___y_1168_; lean_object* v___y_1169_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1174_; lean_object* v___y_1175_; lean_object* v___y_1186_; 
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
lean_inc(v_a_1165_);
lean_dec_ref_known(v___x_1164_, 1);
if (v_useReducible_1110_ == 0)
{
lean_object* v___x_1197_; uint8_t v_foApprox_1198_; uint8_t v_ctxApprox_1199_; uint8_t v_quasiPatternApprox_1200_; uint8_t v_constApprox_1201_; uint8_t v_isDefEqStuckEx_1202_; uint8_t v_unificationHints_1203_; uint8_t v_proofIrrelevance_1204_; uint8_t v_offsetCnstrs_1205_; uint8_t v_transparency_1206_; uint8_t v_etaStruct_1207_; uint8_t v_univApprox_1208_; uint8_t v_iota_1209_; uint8_t v_beta_1210_; uint8_t v_proj_1211_; uint8_t v_zeta_1212_; uint8_t v_zetaDelta_1213_; uint8_t v_zetaUnused_1214_; uint8_t v_zetaHave_1215_; uint8_t v_canUnfoldPredicateConfig_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1247_; 
v___x_1197_ = l_Lean_Meta_Context_config(v___y_1116_);
v_foApprox_1198_ = lean_ctor_get_uint8(v___x_1197_, 0);
v_ctxApprox_1199_ = lean_ctor_get_uint8(v___x_1197_, 1);
v_quasiPatternApprox_1200_ = lean_ctor_get_uint8(v___x_1197_, 2);
v_constApprox_1201_ = lean_ctor_get_uint8(v___x_1197_, 3);
v_isDefEqStuckEx_1202_ = lean_ctor_get_uint8(v___x_1197_, 4);
v_unificationHints_1203_ = lean_ctor_get_uint8(v___x_1197_, 5);
v_proofIrrelevance_1204_ = lean_ctor_get_uint8(v___x_1197_, 6);
v_offsetCnstrs_1205_ = lean_ctor_get_uint8(v___x_1197_, 8);
v_transparency_1206_ = lean_ctor_get_uint8(v___x_1197_, 9);
v_etaStruct_1207_ = lean_ctor_get_uint8(v___x_1197_, 10);
v_univApprox_1208_ = lean_ctor_get_uint8(v___x_1197_, 11);
v_iota_1209_ = lean_ctor_get_uint8(v___x_1197_, 12);
v_beta_1210_ = lean_ctor_get_uint8(v___x_1197_, 13);
v_proj_1211_ = lean_ctor_get_uint8(v___x_1197_, 14);
v_zeta_1212_ = lean_ctor_get_uint8(v___x_1197_, 15);
v_zetaDelta_1213_ = lean_ctor_get_uint8(v___x_1197_, 16);
v_zetaUnused_1214_ = lean_ctor_get_uint8(v___x_1197_, 17);
v_zetaHave_1215_ = lean_ctor_get_uint8(v___x_1197_, 18);
v_canUnfoldPredicateConfig_1216_ = lean_ctor_get_uint8(v___x_1197_, 19);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1218_ = v___x_1197_;
v_isShared_1219_ = v_isSharedCheck_1247_;
goto v_resetjp_1217_;
}
else
{
lean_dec(v___x_1197_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1247_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
uint8_t v_trackZetaDelta_1220_; lean_object* v_zetaDeltaSet_1221_; lean_object* v_lctx_1222_; lean_object* v_localInstances_1223_; lean_object* v_defEqCtx_x3f_1224_; lean_object* v_synthPendingDepth_1225_; lean_object* v_customCanUnfoldPredicate_x3f_1226_; uint8_t v_univApprox_1227_; uint8_t v_inTypeClassResolution_1228_; uint8_t v_cacheInferType_1229_; lean_object* v___x_1231_; 
v_trackZetaDelta_1220_ = lean_ctor_get_uint8(v___y_1116_, sizeof(void*)*7);
v_zetaDeltaSet_1221_ = lean_ctor_get(v___y_1116_, 1);
v_lctx_1222_ = lean_ctor_get(v___y_1116_, 2);
v_localInstances_1223_ = lean_ctor_get(v___y_1116_, 3);
v_defEqCtx_x3f_1224_ = lean_ctor_get(v___y_1116_, 4);
v_synthPendingDepth_1225_ = lean_ctor_get(v___y_1116_, 5);
v_customCanUnfoldPredicate_x3f_1226_ = lean_ctor_get(v___y_1116_, 6);
v_univApprox_1227_ = lean_ctor_get_uint8(v___y_1116_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1228_ = lean_ctor_get_uint8(v___y_1116_, sizeof(void*)*7 + 2);
v_cacheInferType_1229_ = lean_ctor_get_uint8(v___y_1116_, sizeof(void*)*7 + 3);
if (v_isShared_1219_ == 0)
{
v___x_1231_ = v___x_1218_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_1246_, 0, v_foApprox_1198_);
lean_ctor_set_uint8(v_reuseFailAlloc_1246_, 1, v_ctxApprox_1199_);
lean_ctor_set_uint8(v_reuseFailAlloc_1246_, 2, v_quasiPatternApprox_1200_);
lean_ctor_set_uint8(v_reuseFailAlloc_1246_, 3, v_constApprox_1201_);
lean_ctor_set_uint8(v_reuseFailAlloc_1246_, 4, v_isDefEqStuckEx_1202_);
lean_ctor_set_uint8(v_reuseFailAlloc_1246_, 5, v_unificationHints_1203_);
lean_ctor_set_uint8(v_reuseFailAlloc_1246_, 6, v_proofIrrelevance_1204_);
lean_ctor_set_uint8(v_reuseFailAlloc_1246_, 8, v_offsetCnstrs_1205_);
lean_ctor_set_uint8(v_reuseFailAlloc_1246_, 9, v_transparency_1206_);
lean_ctor_set_uint8(v_reuseFailAlloc_1246_, 10, v_etaStruct_1207_);
lean_ctor_set_uint8(v_reuseFailAlloc_1246_, 11, v_univApprox_1208_);
lean_ctor_set_uint8(v_reuseFailAlloc_1246_, 12, v_iota_1209_);
lean_ctor_set_uint8(v_reuseFailAlloc_1246_, 13, v_beta_1210_);
lean_ctor_set_uint8(v_reuseFailAlloc_1246_, 14, v_proj_1211_);
lean_ctor_set_uint8(v_reuseFailAlloc_1246_, 15, v_zeta_1212_);
lean_ctor_set_uint8(v_reuseFailAlloc_1246_, 16, v_zetaDelta_1213_);
lean_ctor_set_uint8(v_reuseFailAlloc_1246_, 17, v_zetaUnused_1214_);
lean_ctor_set_uint8(v_reuseFailAlloc_1246_, 18, v_zetaHave_1215_);
lean_ctor_set_uint8(v_reuseFailAlloc_1246_, 19, v_canUnfoldPredicateConfig_1216_);
v___x_1231_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
uint64_t v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
lean_ctor_set_uint8(v___x_1231_, 7, v___x_1111_);
v___x_1232_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1231_);
v___x_1233_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1233_, 0, v___x_1231_);
lean_ctor_set_uint64(v___x_1233_, sizeof(void*)*1, v___x_1232_);
lean_inc(v_customCanUnfoldPredicate_x3f_1226_);
lean_inc(v_synthPendingDepth_1225_);
lean_inc(v_defEqCtx_x3f_1224_);
lean_inc_ref(v_localInstances_1223_);
lean_inc_ref(v_lctx_1222_);
lean_inc(v_zetaDeltaSet_1221_);
v___x_1234_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1234_, 0, v___x_1233_);
lean_ctor_set(v___x_1234_, 1, v_zetaDeltaSet_1221_);
lean_ctor_set(v___x_1234_, 2, v_lctx_1222_);
lean_ctor_set(v___x_1234_, 3, v_localInstances_1223_);
lean_ctor_set(v___x_1234_, 4, v_defEqCtx_x3f_1224_);
lean_ctor_set(v___x_1234_, 5, v_synthPendingDepth_1225_);
lean_ctor_set(v___x_1234_, 6, v_customCanUnfoldPredicate_x3f_1226_);
lean_ctor_set_uint8(v___x_1234_, sizeof(void*)*7, v_trackZetaDelta_1220_);
lean_ctor_set_uint8(v___x_1234_, sizeof(void*)*7 + 1, v_univApprox_1227_);
lean_ctor_set_uint8(v___x_1234_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1228_);
lean_ctor_set_uint8(v___x_1234_, sizeof(void*)*7 + 3, v_cacheInferType_1229_);
lean_inc(v_a_1165_);
lean_inc(v_a_1122_);
v___x_1235_ = l_Lean_Meta_isExprDefEq(v_a_1122_, v_a_1165_, v___x_1234_, v___y_1117_, v___y_1118_, v___y_1119_);
lean_dec_ref_known(v___x_1234_, 7);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v_a_1236_; uint8_t v___x_1237_; 
v_a_1236_ = lean_ctor_get(v___x_1235_, 0);
lean_inc(v_a_1236_);
lean_dec_ref_known(v___x_1235_, 1);
v___x_1237_ = lean_unbox(v_a_1236_);
lean_dec(v_a_1236_);
v_____do__lift_1167_ = v___x_1237_;
v___y_1168_ = v___y_1112_;
v___y_1169_ = v___y_1113_;
v___y_1170_ = v___y_1114_;
v___y_1171_ = v___y_1115_;
v___y_1172_ = v___y_1116_;
v___y_1173_ = v___y_1117_;
v___y_1174_ = v___y_1118_;
v___y_1175_ = v___y_1119_;
goto v___jp_1166_;
}
else
{
lean_object* v_a_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1245_; 
lean_dec(v_a_1165_);
lean_del_object(v___x_1162_);
lean_dec(v_a_1126_);
lean_dec(v_a_1122_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___x_1109_);
lean_dec_ref(v___x_1107_);
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1102_);
v_a_1238_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1240_ = v___x_1235_;
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_a_1238_);
lean_dec(v___x_1235_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
if (v_isShared_1241_ == 0)
{
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_a_1238_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
}
}
else
{
lean_object* v___x_1248_; uint8_t v_foApprox_1249_; uint8_t v_ctxApprox_1250_; uint8_t v_quasiPatternApprox_1251_; uint8_t v_constApprox_1252_; uint8_t v_isDefEqStuckEx_1253_; uint8_t v_unificationHints_1254_; uint8_t v_proofIrrelevance_1255_; uint8_t v_offsetCnstrs_1256_; uint8_t v_transparency_1257_; uint8_t v_etaStruct_1258_; uint8_t v_univApprox_1259_; uint8_t v_iota_1260_; uint8_t v_beta_1261_; uint8_t v_proj_1262_; uint8_t v_zeta_1263_; uint8_t v_zetaDelta_1264_; uint8_t v_zetaUnused_1265_; uint8_t v_zetaHave_1266_; uint8_t v_canUnfoldPredicateConfig_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1334_; 
v___x_1248_ = l_Lean_Meta_Context_config(v___y_1116_);
v_foApprox_1249_ = lean_ctor_get_uint8(v___x_1248_, 0);
v_ctxApprox_1250_ = lean_ctor_get_uint8(v___x_1248_, 1);
v_quasiPatternApprox_1251_ = lean_ctor_get_uint8(v___x_1248_, 2);
v_constApprox_1252_ = lean_ctor_get_uint8(v___x_1248_, 3);
v_isDefEqStuckEx_1253_ = lean_ctor_get_uint8(v___x_1248_, 4);
v_unificationHints_1254_ = lean_ctor_get_uint8(v___x_1248_, 5);
v_proofIrrelevance_1255_ = lean_ctor_get_uint8(v___x_1248_, 6);
v_offsetCnstrs_1256_ = lean_ctor_get_uint8(v___x_1248_, 8);
v_transparency_1257_ = lean_ctor_get_uint8(v___x_1248_, 9);
v_etaStruct_1258_ = lean_ctor_get_uint8(v___x_1248_, 10);
v_univApprox_1259_ = lean_ctor_get_uint8(v___x_1248_, 11);
v_iota_1260_ = lean_ctor_get_uint8(v___x_1248_, 12);
v_beta_1261_ = lean_ctor_get_uint8(v___x_1248_, 13);
v_proj_1262_ = lean_ctor_get_uint8(v___x_1248_, 14);
v_zeta_1263_ = lean_ctor_get_uint8(v___x_1248_, 15);
v_zetaDelta_1264_ = lean_ctor_get_uint8(v___x_1248_, 16);
v_zetaUnused_1265_ = lean_ctor_get_uint8(v___x_1248_, 17);
v_zetaHave_1266_ = lean_ctor_get_uint8(v___x_1248_, 18);
v_canUnfoldPredicateConfig_1267_ = lean_ctor_get_uint8(v___x_1248_, 19);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1269_ = v___x_1248_;
v_isShared_1270_ = v_isSharedCheck_1334_;
goto v_resetjp_1268_;
}
else
{
lean_dec(v___x_1248_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1334_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
uint8_t v___x_1271_; uint8_t v___x_1272_; 
v___x_1271_ = 2;
v___x_1272_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1257_, v___x_1271_);
if (v___x_1272_ == 0)
{
lean_object* v_keyedConfig_1273_; uint8_t v_trackZetaDelta_1274_; lean_object* v_zetaDeltaSet_1275_; lean_object* v_lctx_1276_; lean_object* v_localInstances_1277_; lean_object* v_defEqCtx_x3f_1278_; lean_object* v_synthPendingDepth_1279_; lean_object* v_customCanUnfoldPredicate_x3f_1280_; uint8_t v_univApprox_1281_; uint8_t v_inTypeClassResolution_1282_; uint8_t v_cacheInferType_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; uint8_t v_foApprox_1287_; uint8_t v_ctxApprox_1288_; uint8_t v_quasiPatternApprox_1289_; uint8_t v_constApprox_1290_; uint8_t v_isDefEqStuckEx_1291_; uint8_t v_unificationHints_1292_; uint8_t v_proofIrrelevance_1293_; uint8_t v_offsetCnstrs_1294_; uint8_t v_transparency_1295_; uint8_t v_etaStruct_1296_; uint8_t v_univApprox_1297_; uint8_t v_iota_1298_; uint8_t v_beta_1299_; uint8_t v_proj_1300_; uint8_t v_zeta_1301_; uint8_t v_zetaDelta_1302_; uint8_t v_zetaUnused_1303_; uint8_t v_zetaHave_1304_; uint8_t v_canUnfoldPredicateConfig_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1316_; 
lean_del_object(v___x_1269_);
v_keyedConfig_1273_ = lean_ctor_get(v___y_1116_, 0);
v_trackZetaDelta_1274_ = lean_ctor_get_uint8(v___y_1116_, sizeof(void*)*7);
v_zetaDeltaSet_1275_ = lean_ctor_get(v___y_1116_, 1);
v_lctx_1276_ = lean_ctor_get(v___y_1116_, 2);
v_localInstances_1277_ = lean_ctor_get(v___y_1116_, 3);
v_defEqCtx_x3f_1278_ = lean_ctor_get(v___y_1116_, 4);
v_synthPendingDepth_1279_ = lean_ctor_get(v___y_1116_, 5);
v_customCanUnfoldPredicate_x3f_1280_ = lean_ctor_get(v___y_1116_, 6);
v_univApprox_1281_ = lean_ctor_get_uint8(v___y_1116_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1282_ = lean_ctor_get_uint8(v___y_1116_, sizeof(void*)*7 + 2);
v_cacheInferType_1283_ = lean_ctor_get_uint8(v___y_1116_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1273_);
v___x_1284_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1271_, v_keyedConfig_1273_);
lean_inc(v_customCanUnfoldPredicate_x3f_1280_);
lean_inc(v_synthPendingDepth_1279_);
lean_inc(v_defEqCtx_x3f_1278_);
lean_inc_ref(v_localInstances_1277_);
lean_inc_ref(v_lctx_1276_);
lean_inc(v_zetaDeltaSet_1275_);
v___x_1285_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1285_, 0, v___x_1284_);
lean_ctor_set(v___x_1285_, 1, v_zetaDeltaSet_1275_);
lean_ctor_set(v___x_1285_, 2, v_lctx_1276_);
lean_ctor_set(v___x_1285_, 3, v_localInstances_1277_);
lean_ctor_set(v___x_1285_, 4, v_defEqCtx_x3f_1278_);
lean_ctor_set(v___x_1285_, 5, v_synthPendingDepth_1279_);
lean_ctor_set(v___x_1285_, 6, v_customCanUnfoldPredicate_x3f_1280_);
lean_ctor_set_uint8(v___x_1285_, sizeof(void*)*7, v_trackZetaDelta_1274_);
lean_ctor_set_uint8(v___x_1285_, sizeof(void*)*7 + 1, v_univApprox_1281_);
lean_ctor_set_uint8(v___x_1285_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1282_);
lean_ctor_set_uint8(v___x_1285_, sizeof(void*)*7 + 3, v_cacheInferType_1283_);
v___x_1286_ = l_Lean_Meta_Context_config(v___x_1285_);
lean_dec_ref_known(v___x_1285_, 7);
v_foApprox_1287_ = lean_ctor_get_uint8(v___x_1286_, 0);
v_ctxApprox_1288_ = lean_ctor_get_uint8(v___x_1286_, 1);
v_quasiPatternApprox_1289_ = lean_ctor_get_uint8(v___x_1286_, 2);
v_constApprox_1290_ = lean_ctor_get_uint8(v___x_1286_, 3);
v_isDefEqStuckEx_1291_ = lean_ctor_get_uint8(v___x_1286_, 4);
v_unificationHints_1292_ = lean_ctor_get_uint8(v___x_1286_, 5);
v_proofIrrelevance_1293_ = lean_ctor_get_uint8(v___x_1286_, 6);
v_offsetCnstrs_1294_ = lean_ctor_get_uint8(v___x_1286_, 8);
v_transparency_1295_ = lean_ctor_get_uint8(v___x_1286_, 9);
v_etaStruct_1296_ = lean_ctor_get_uint8(v___x_1286_, 10);
v_univApprox_1297_ = lean_ctor_get_uint8(v___x_1286_, 11);
v_iota_1298_ = lean_ctor_get_uint8(v___x_1286_, 12);
v_beta_1299_ = lean_ctor_get_uint8(v___x_1286_, 13);
v_proj_1300_ = lean_ctor_get_uint8(v___x_1286_, 14);
v_zeta_1301_ = lean_ctor_get_uint8(v___x_1286_, 15);
v_zetaDelta_1302_ = lean_ctor_get_uint8(v___x_1286_, 16);
v_zetaUnused_1303_ = lean_ctor_get_uint8(v___x_1286_, 17);
v_zetaHave_1304_ = lean_ctor_get_uint8(v___x_1286_, 18);
v_canUnfoldPredicateConfig_1305_ = lean_ctor_get_uint8(v___x_1286_, 19);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1307_ = v___x_1286_;
v_isShared_1308_ = v_isSharedCheck_1316_;
goto v_resetjp_1306_;
}
else
{
lean_dec(v___x_1286_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1316_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1310_; 
if (v_isShared_1308_ == 0)
{
v___x_1310_ = v___x_1307_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_1315_, 0, v_foApprox_1287_);
lean_ctor_set_uint8(v_reuseFailAlloc_1315_, 1, v_ctxApprox_1288_);
lean_ctor_set_uint8(v_reuseFailAlloc_1315_, 2, v_quasiPatternApprox_1289_);
lean_ctor_set_uint8(v_reuseFailAlloc_1315_, 3, v_constApprox_1290_);
lean_ctor_set_uint8(v_reuseFailAlloc_1315_, 4, v_isDefEqStuckEx_1291_);
lean_ctor_set_uint8(v_reuseFailAlloc_1315_, 5, v_unificationHints_1292_);
lean_ctor_set_uint8(v_reuseFailAlloc_1315_, 6, v_proofIrrelevance_1293_);
lean_ctor_set_uint8(v_reuseFailAlloc_1315_, 8, v_offsetCnstrs_1294_);
lean_ctor_set_uint8(v_reuseFailAlloc_1315_, 9, v_transparency_1295_);
lean_ctor_set_uint8(v_reuseFailAlloc_1315_, 10, v_etaStruct_1296_);
lean_ctor_set_uint8(v_reuseFailAlloc_1315_, 11, v_univApprox_1297_);
lean_ctor_set_uint8(v_reuseFailAlloc_1315_, 12, v_iota_1298_);
lean_ctor_set_uint8(v_reuseFailAlloc_1315_, 13, v_beta_1299_);
lean_ctor_set_uint8(v_reuseFailAlloc_1315_, 14, v_proj_1300_);
lean_ctor_set_uint8(v_reuseFailAlloc_1315_, 15, v_zeta_1301_);
lean_ctor_set_uint8(v_reuseFailAlloc_1315_, 16, v_zetaDelta_1302_);
lean_ctor_set_uint8(v_reuseFailAlloc_1315_, 17, v_zetaUnused_1303_);
lean_ctor_set_uint8(v_reuseFailAlloc_1315_, 18, v_zetaHave_1304_);
lean_ctor_set_uint8(v_reuseFailAlloc_1315_, 19, v_canUnfoldPredicateConfig_1305_);
v___x_1310_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
uint64_t v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
lean_ctor_set_uint8(v___x_1310_, 7, v___x_1111_);
v___x_1311_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1310_);
v___x_1312_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1312_, 0, v___x_1310_);
lean_ctor_set_uint64(v___x_1312_, sizeof(void*)*1, v___x_1311_);
lean_inc(v_customCanUnfoldPredicate_x3f_1280_);
lean_inc(v_synthPendingDepth_1279_);
lean_inc(v_defEqCtx_x3f_1278_);
lean_inc_ref(v_localInstances_1277_);
lean_inc_ref(v_lctx_1276_);
lean_inc(v_zetaDeltaSet_1275_);
v___x_1313_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
lean_ctor_set(v___x_1313_, 1, v_zetaDeltaSet_1275_);
lean_ctor_set(v___x_1313_, 2, v_lctx_1276_);
lean_ctor_set(v___x_1313_, 3, v_localInstances_1277_);
lean_ctor_set(v___x_1313_, 4, v_defEqCtx_x3f_1278_);
lean_ctor_set(v___x_1313_, 5, v_synthPendingDepth_1279_);
lean_ctor_set(v___x_1313_, 6, v_customCanUnfoldPredicate_x3f_1280_);
lean_ctor_set_uint8(v___x_1313_, sizeof(void*)*7, v_trackZetaDelta_1274_);
lean_ctor_set_uint8(v___x_1313_, sizeof(void*)*7 + 1, v_univApprox_1281_);
lean_ctor_set_uint8(v___x_1313_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1282_);
lean_ctor_set_uint8(v___x_1313_, sizeof(void*)*7 + 3, v_cacheInferType_1283_);
lean_inc(v_a_1165_);
lean_inc(v_a_1122_);
v___x_1314_ = l_Lean_Meta_isExprDefEq(v_a_1122_, v_a_1165_, v___x_1313_, v___y_1117_, v___y_1118_, v___y_1119_);
lean_dec_ref_known(v___x_1313_, 7);
v___y_1186_ = v___x_1314_;
goto v___jp_1185_;
}
}
}
else
{
uint8_t v_trackZetaDelta_1317_; lean_object* v_zetaDeltaSet_1318_; lean_object* v_lctx_1319_; lean_object* v_localInstances_1320_; lean_object* v_defEqCtx_x3f_1321_; lean_object* v_synthPendingDepth_1322_; lean_object* v_customCanUnfoldPredicate_x3f_1323_; uint8_t v_univApprox_1324_; uint8_t v_inTypeClassResolution_1325_; uint8_t v_cacheInferType_1326_; lean_object* v___x_1328_; 
v_trackZetaDelta_1317_ = lean_ctor_get_uint8(v___y_1116_, sizeof(void*)*7);
v_zetaDeltaSet_1318_ = lean_ctor_get(v___y_1116_, 1);
v_lctx_1319_ = lean_ctor_get(v___y_1116_, 2);
v_localInstances_1320_ = lean_ctor_get(v___y_1116_, 3);
v_defEqCtx_x3f_1321_ = lean_ctor_get(v___y_1116_, 4);
v_synthPendingDepth_1322_ = lean_ctor_get(v___y_1116_, 5);
v_customCanUnfoldPredicate_x3f_1323_ = lean_ctor_get(v___y_1116_, 6);
v_univApprox_1324_ = lean_ctor_get_uint8(v___y_1116_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1325_ = lean_ctor_get_uint8(v___y_1116_, sizeof(void*)*7 + 2);
v_cacheInferType_1326_ = lean_ctor_get_uint8(v___y_1116_, sizeof(void*)*7 + 3);
if (v_isShared_1270_ == 0)
{
v___x_1328_ = v___x_1269_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_1333_, 0, v_foApprox_1249_);
lean_ctor_set_uint8(v_reuseFailAlloc_1333_, 1, v_ctxApprox_1250_);
lean_ctor_set_uint8(v_reuseFailAlloc_1333_, 2, v_quasiPatternApprox_1251_);
lean_ctor_set_uint8(v_reuseFailAlloc_1333_, 3, v_constApprox_1252_);
lean_ctor_set_uint8(v_reuseFailAlloc_1333_, 4, v_isDefEqStuckEx_1253_);
lean_ctor_set_uint8(v_reuseFailAlloc_1333_, 5, v_unificationHints_1254_);
lean_ctor_set_uint8(v_reuseFailAlloc_1333_, 6, v_proofIrrelevance_1255_);
lean_ctor_set_uint8(v_reuseFailAlloc_1333_, 8, v_offsetCnstrs_1256_);
lean_ctor_set_uint8(v_reuseFailAlloc_1333_, 9, v_transparency_1257_);
lean_ctor_set_uint8(v_reuseFailAlloc_1333_, 10, v_etaStruct_1258_);
lean_ctor_set_uint8(v_reuseFailAlloc_1333_, 11, v_univApprox_1259_);
lean_ctor_set_uint8(v_reuseFailAlloc_1333_, 12, v_iota_1260_);
lean_ctor_set_uint8(v_reuseFailAlloc_1333_, 13, v_beta_1261_);
lean_ctor_set_uint8(v_reuseFailAlloc_1333_, 14, v_proj_1262_);
lean_ctor_set_uint8(v_reuseFailAlloc_1333_, 15, v_zeta_1263_);
lean_ctor_set_uint8(v_reuseFailAlloc_1333_, 16, v_zetaDelta_1264_);
lean_ctor_set_uint8(v_reuseFailAlloc_1333_, 17, v_zetaUnused_1265_);
lean_ctor_set_uint8(v_reuseFailAlloc_1333_, 18, v_zetaHave_1266_);
lean_ctor_set_uint8(v_reuseFailAlloc_1333_, 19, v_canUnfoldPredicateConfig_1267_);
v___x_1328_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
uint64_t v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
lean_ctor_set_uint8(v___x_1328_, 7, v___x_1111_);
v___x_1329_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1328_);
v___x_1330_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1330_, 0, v___x_1328_);
lean_ctor_set_uint64(v___x_1330_, sizeof(void*)*1, v___x_1329_);
lean_inc(v_customCanUnfoldPredicate_x3f_1323_);
lean_inc(v_synthPendingDepth_1322_);
lean_inc(v_defEqCtx_x3f_1321_);
lean_inc_ref(v_localInstances_1320_);
lean_inc_ref(v_lctx_1319_);
lean_inc(v_zetaDeltaSet_1318_);
v___x_1331_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1331_, 0, v___x_1330_);
lean_ctor_set(v___x_1331_, 1, v_zetaDeltaSet_1318_);
lean_ctor_set(v___x_1331_, 2, v_lctx_1319_);
lean_ctor_set(v___x_1331_, 3, v_localInstances_1320_);
lean_ctor_set(v___x_1331_, 4, v_defEqCtx_x3f_1321_);
lean_ctor_set(v___x_1331_, 5, v_synthPendingDepth_1322_);
lean_ctor_set(v___x_1331_, 6, v_customCanUnfoldPredicate_x3f_1323_);
lean_ctor_set_uint8(v___x_1331_, sizeof(void*)*7, v_trackZetaDelta_1317_);
lean_ctor_set_uint8(v___x_1331_, sizeof(void*)*7 + 1, v_univApprox_1324_);
lean_ctor_set_uint8(v___x_1331_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1325_);
lean_ctor_set_uint8(v___x_1331_, sizeof(void*)*7 + 3, v_cacheInferType_1326_);
lean_inc(v_a_1165_);
lean_inc(v_a_1122_);
v___x_1332_ = l_Lean_Meta_isExprDefEq(v_a_1122_, v_a_1165_, v___x_1331_, v___y_1117_, v___y_1118_, v___y_1119_);
lean_dec_ref_known(v___x_1331_, 7);
v___y_1186_ = v___x_1332_;
goto v___jp_1185_;
}
}
}
}
v___jp_1166_:
{
if (v_____do__lift_1167_ == 0)
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1182_; 
v___x_1176_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__1, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__1);
lean_inc_ref(v_a_1105_);
v___x_1177_ = l_Lean_indentExpr(v_a_1105_);
v___x_1178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1176_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
v___x_1179_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__3, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__3_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__3);
v___x_1180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1178_);
lean_ctor_set(v___x_1180_, 1, v___x_1179_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set_tag(v___x_1162_, 1);
lean_ctor_set(v___x_1162_, 0, v___x_1180_);
v___x_1182_ = v___x_1162_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1180_);
v___x_1182_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
lean_object* v___x_1183_; 
lean_inc(v_a_1126_);
v___x_1183_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(v___x_1182_, v_a_1122_, v_a_1165_, v_a_1126_, v___x_1109_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
lean_dec_ref(v___x_1182_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_dec_ref_known(v___x_1183_, 1);
v___y_1128_ = v___y_1168_;
v___y_1129_ = v___y_1169_;
v___y_1130_ = v___y_1170_;
v___y_1131_ = v___y_1171_;
v___y_1132_ = v___y_1172_;
v___y_1133_ = v___y_1173_;
v___y_1134_ = v___y_1174_;
v___y_1135_ = v___y_1175_;
goto v___jp_1127_;
}
else
{
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v_a_1126_);
lean_dec_ref(v___x_1107_);
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1102_);
return v___x_1183_;
}
}
}
else
{
lean_dec(v_a_1165_);
lean_del_object(v___x_1162_);
lean_dec(v_a_1122_);
lean_dec(v___x_1109_);
v___y_1128_ = v___y_1168_;
v___y_1129_ = v___y_1169_;
v___y_1130_ = v___y_1170_;
v___y_1131_ = v___y_1171_;
v___y_1132_ = v___y_1172_;
v___y_1133_ = v___y_1173_;
v___y_1134_ = v___y_1174_;
v___y_1135_ = v___y_1175_;
goto v___jp_1127_;
}
}
v___jp_1185_:
{
if (lean_obj_tag(v___y_1186_) == 0)
{
lean_object* v_a_1187_; uint8_t v___x_1188_; 
v_a_1187_ = lean_ctor_get(v___y_1186_, 0);
lean_inc(v_a_1187_);
lean_dec_ref_known(v___y_1186_, 1);
v___x_1188_ = lean_unbox(v_a_1187_);
lean_dec(v_a_1187_);
v_____do__lift_1167_ = v___x_1188_;
v___y_1168_ = v___y_1112_;
v___y_1169_ = v___y_1113_;
v___y_1170_ = v___y_1114_;
v___y_1171_ = v___y_1115_;
v___y_1172_ = v___y_1116_;
v___y_1173_ = v___y_1117_;
v___y_1174_ = v___y_1118_;
v___y_1175_ = v___y_1119_;
goto v___jp_1166_;
}
else
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1196_; 
lean_dec(v_a_1165_);
lean_del_object(v___x_1162_);
lean_dec(v_a_1126_);
lean_dec(v_a_1122_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___x_1109_);
lean_dec_ref(v___x_1107_);
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1102_);
v_a_1189_ = lean_ctor_get(v___y_1186_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___y_1186_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1191_ = v___y_1186_;
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___y_1186_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1194_; 
if (v_isShared_1192_ == 0)
{
v___x_1194_ = v___x_1191_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_a_1189_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
}
else
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1342_; 
lean_del_object(v___x_1162_);
lean_dec(v_a_1126_);
lean_dec(v_a_1122_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___x_1109_);
lean_dec_ref(v___x_1107_);
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1102_);
v_a_1335_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1337_ = v___x_1164_;
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1164_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1335_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
}
}
else
{
lean_dec(v_a_1126_);
lean_dec(v_a_1122_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___x_1109_);
lean_dec_ref(v___x_1107_);
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1102_);
return v___x_1160_;
}
v___jp_1127_:
{
lean_object* v___x_1136_; 
v___x_1136_ = l_Lean_Meta_getMVars(v_a_1105_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v_a_1137_; lean_object* v___x_1138_; 
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc(v_a_1137_);
lean_dec_ref_known(v___x_1136_, 1);
v___x_1138_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(v_a_1137_, v_mvarCounter_1106_, v___y_1133_);
lean_dec(v_a_1137_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v_a_1139_; lean_object* v___x_1140_; 
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
lean_inc(v_a_1139_);
lean_dec_ref_known(v___x_1138_, 1);
v___x_1140_ = l_Lean_Elab_Tactic_logUnassignedAndAbort(v_a_1139_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
lean_dec(v_a_1139_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v___x_1141_; 
lean_dec_ref_known(v___x_1140_, 1);
v___x_1141_ = l_Lean_Elab_Tactic_pushGoal___redArg(v_a_1102_, v___y_1129_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
lean_dec_ref_known(v___x_1141_, 1);
v___x_1142_ = l_Lean_Name_mkStr1(v___x_1107_);
v___x_1143_ = l_Lean_Elab_Tactic_closeMainGoal___redArg(v___x_1142_, v_a_1126_, v___x_1108_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
return v___x_1143_;
}
else
{
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v_a_1126_);
lean_dec_ref(v___x_1107_);
return v___x_1141_;
}
}
else
{
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v_a_1126_);
lean_dec_ref(v___x_1107_);
lean_dec(v_a_1102_);
return v___x_1140_;
}
}
else
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v_a_1126_);
lean_dec_ref(v___x_1107_);
lean_dec(v_a_1102_);
v_a_1144_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1146_ = v___x_1138_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1138_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1147_ == 0)
{
v___x_1149_ = v___x_1146_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1144_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
else
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v_a_1126_);
lean_dec_ref(v___x_1107_);
lean_dec(v_a_1102_);
v_a_1152_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1136_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1136_);
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
}
else
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1352_; 
lean_dec(v_a_1122_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___x_1109_);
lean_dec_ref(v___x_1107_);
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1102_);
v_a_1345_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1347_ = v___x_1125_;
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1125_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1350_; 
if (v_isShared_1348_ == 0)
{
v___x_1350_ = v___x_1347_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_a_1345_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
}
else
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___x_1109_);
lean_dec_ref(v___x_1107_);
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1103_);
lean_dec(v_a_1102_);
v_a_1353_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v___x_1121_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1121_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___boxed(lean_object** _args){
lean_object* v_a_1361_ = _args[0];
lean_object* v_a_1362_ = _args[1];
lean_object* v___x_1363_ = _args[2];
lean_object* v_a_1364_ = _args[3];
lean_object* v_mvarCounter_1365_ = _args[4];
lean_object* v___x_1366_ = _args[5];
lean_object* v___x_1367_ = _args[6];
lean_object* v___x_1368_ = _args[7];
lean_object* v_useReducible_1369_ = _args[8];
lean_object* v___x_1370_ = _args[9];
lean_object* v___y_1371_ = _args[10];
lean_object* v___y_1372_ = _args[11];
lean_object* v___y_1373_ = _args[12];
lean_object* v___y_1374_ = _args[13];
lean_object* v___y_1375_ = _args[14];
lean_object* v___y_1376_ = _args[15];
lean_object* v___y_1377_ = _args[16];
lean_object* v___y_1378_ = _args[17];
lean_object* v___y_1379_ = _args[18];
_start:
{
uint8_t v___x_93745__boxed_1380_; uint8_t v___x_93748__boxed_1381_; uint8_t v_useReducible_boxed_1382_; uint8_t v___x_93750__boxed_1383_; lean_object* v_res_1384_; 
v___x_93745__boxed_1380_ = lean_unbox(v___x_1363_);
v___x_93748__boxed_1381_ = lean_unbox(v___x_1367_);
v_useReducible_boxed_1382_ = lean_unbox(v_useReducible_1369_);
v___x_93750__boxed_1383_ = lean_unbox(v___x_1370_);
v_res_1384_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3(v_a_1361_, v_a_1362_, v___x_93745__boxed_1380_, v_a_1364_, v_mvarCounter_1365_, v___x_1366_, v___x_93748__boxed_1381_, v___x_1368_, v_useReducible_boxed_1382_, v___x_93750__boxed_1383_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
lean_dec(v_mvarCounter_1365_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4(lean_object* v_a_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
lean_object* v___x_1395_; lean_object* v_infoState_1396_; lean_object* v_env_1397_; lean_object* v_nextMacroScope_1398_; lean_object* v_ngen_1399_; lean_object* v_auxDeclNGen_1400_; lean_object* v_traceState_1401_; lean_object* v_cache_1402_; lean_object* v_messages_1403_; lean_object* v_snapshotTasks_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1425_; 
v___x_1395_ = lean_st_ref_take(v___y_1393_);
v_infoState_1396_ = lean_ctor_get(v___x_1395_, 7);
v_env_1397_ = lean_ctor_get(v___x_1395_, 0);
v_nextMacroScope_1398_ = lean_ctor_get(v___x_1395_, 1);
v_ngen_1399_ = lean_ctor_get(v___x_1395_, 2);
v_auxDeclNGen_1400_ = lean_ctor_get(v___x_1395_, 3);
v_traceState_1401_ = lean_ctor_get(v___x_1395_, 4);
v_cache_1402_ = lean_ctor_get(v___x_1395_, 5);
v_messages_1403_ = lean_ctor_get(v___x_1395_, 6);
v_snapshotTasks_1404_ = lean_ctor_get(v___x_1395_, 8);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1406_ = v___x_1395_;
v_isShared_1407_ = v_isSharedCheck_1425_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_snapshotTasks_1404_);
lean_inc(v_infoState_1396_);
lean_inc(v_messages_1403_);
lean_inc(v_cache_1402_);
lean_inc(v_traceState_1401_);
lean_inc(v_auxDeclNGen_1400_);
lean_inc(v_ngen_1399_);
lean_inc(v_nextMacroScope_1398_);
lean_inc(v_env_1397_);
lean_dec(v___x_1395_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1425_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
uint8_t v_enabled_1408_; lean_object* v_assignment_1409_; lean_object* v_lazyAssignment_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1423_; 
v_enabled_1408_ = lean_ctor_get_uint8(v_infoState_1396_, sizeof(void*)*3);
v_assignment_1409_ = lean_ctor_get(v_infoState_1396_, 0);
v_lazyAssignment_1410_ = lean_ctor_get(v_infoState_1396_, 1);
v_isSharedCheck_1423_ = !lean_is_exclusive(v_infoState_1396_);
if (v_isSharedCheck_1423_ == 0)
{
lean_object* v_unused_1424_; 
v_unused_1424_ = lean_ctor_get(v_infoState_1396_, 2);
lean_dec(v_unused_1424_);
v___x_1412_ = v_infoState_1396_;
v_isShared_1413_ = v_isSharedCheck_1423_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_lazyAssignment_1410_);
lean_inc(v_assignment_1409_);
lean_dec(v_infoState_1396_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1423_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1414_; lean_object* v___x_1416_; 
v___x_1414_ = lean_box(0);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 2, v_a_1385_);
v___x_1416_ = v___x_1412_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_assignment_1409_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v_lazyAssignment_1410_);
lean_ctor_set(v_reuseFailAlloc_1422_, 2, v_a_1385_);
lean_ctor_set_uint8(v_reuseFailAlloc_1422_, sizeof(void*)*3, v_enabled_1408_);
v___x_1416_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
lean_object* v___x_1418_; 
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 7, v___x_1416_);
v___x_1418_ = v___x_1406_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_env_1397_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v_nextMacroScope_1398_);
lean_ctor_set(v_reuseFailAlloc_1421_, 2, v_ngen_1399_);
lean_ctor_set(v_reuseFailAlloc_1421_, 3, v_auxDeclNGen_1400_);
lean_ctor_set(v_reuseFailAlloc_1421_, 4, v_traceState_1401_);
lean_ctor_set(v_reuseFailAlloc_1421_, 5, v_cache_1402_);
lean_ctor_set(v_reuseFailAlloc_1421_, 6, v_messages_1403_);
lean_ctor_set(v_reuseFailAlloc_1421_, 7, v___x_1416_);
lean_ctor_set(v_reuseFailAlloc_1421_, 8, v_snapshotTasks_1404_);
v___x_1418_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1419_ = lean_st_ref_put(v___y_1393_, v___x_1418_);
v___x_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1414_);
return v___x_1420_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___boxed(lean_object* v_a_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4(v_a_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0(lean_object* v___y_1437_, lean_object* v_mkInfoTree_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v_a_1446_, lean_object* v_a_x3f_1447_){
_start:
{
lean_object* v___x_1449_; lean_object* v_infoState_1450_; lean_object* v_trees_1451_; lean_object* v___x_1452_; 
v___x_1449_ = lean_st_ref_get(v___y_1437_);
v_infoState_1450_ = lean_ctor_get(v___x_1449_, 7);
lean_inc_ref(v_infoState_1450_);
lean_dec(v___x_1449_);
v_trees_1451_ = lean_ctor_get(v_infoState_1450_, 2);
lean_inc_ref(v_trees_1451_);
lean_dec_ref(v_infoState_1450_);
lean_inc(v___y_1437_);
lean_inc_ref(v___y_1445_);
lean_inc(v___y_1444_);
lean_inc_ref(v___y_1443_);
lean_inc(v___y_1442_);
lean_inc_ref(v___y_1441_);
lean_inc(v___y_1440_);
lean_inc_ref(v___y_1439_);
v___x_1452_ = lean_apply_10(v_mkInfoTree_1438_, v_trees_1451_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1437_, lean_box(0));
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1491_; 
v_a_1453_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1455_ = v___x_1452_;
v_isShared_1456_ = v_isSharedCheck_1491_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1452_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1491_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1457_; lean_object* v_infoState_1458_; lean_object* v_env_1459_; lean_object* v_nextMacroScope_1460_; lean_object* v_ngen_1461_; lean_object* v_auxDeclNGen_1462_; lean_object* v_traceState_1463_; lean_object* v_cache_1464_; lean_object* v_messages_1465_; lean_object* v_snapshotTasks_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1490_; 
v___x_1457_ = lean_st_ref_take(v___y_1437_);
v_infoState_1458_ = lean_ctor_get(v___x_1457_, 7);
v_env_1459_ = lean_ctor_get(v___x_1457_, 0);
v_nextMacroScope_1460_ = lean_ctor_get(v___x_1457_, 1);
v_ngen_1461_ = lean_ctor_get(v___x_1457_, 2);
v_auxDeclNGen_1462_ = lean_ctor_get(v___x_1457_, 3);
v_traceState_1463_ = lean_ctor_get(v___x_1457_, 4);
v_cache_1464_ = lean_ctor_get(v___x_1457_, 5);
v_messages_1465_ = lean_ctor_get(v___x_1457_, 6);
v_snapshotTasks_1466_ = lean_ctor_get(v___x_1457_, 8);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1468_ = v___x_1457_;
v_isShared_1469_ = v_isSharedCheck_1490_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_snapshotTasks_1466_);
lean_inc(v_infoState_1458_);
lean_inc(v_messages_1465_);
lean_inc(v_cache_1464_);
lean_inc(v_traceState_1463_);
lean_inc(v_auxDeclNGen_1462_);
lean_inc(v_ngen_1461_);
lean_inc(v_nextMacroScope_1460_);
lean_inc(v_env_1459_);
lean_dec(v___x_1457_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1490_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
uint8_t v_enabled_1470_; lean_object* v_assignment_1471_; lean_object* v_lazyAssignment_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1488_; 
v_enabled_1470_ = lean_ctor_get_uint8(v_infoState_1458_, sizeof(void*)*3);
v_assignment_1471_ = lean_ctor_get(v_infoState_1458_, 0);
v_lazyAssignment_1472_ = lean_ctor_get(v_infoState_1458_, 1);
v_isSharedCheck_1488_ = !lean_is_exclusive(v_infoState_1458_);
if (v_isSharedCheck_1488_ == 0)
{
lean_object* v_unused_1489_; 
v_unused_1489_ = lean_ctor_get(v_infoState_1458_, 2);
lean_dec(v_unused_1489_);
v___x_1474_ = v_infoState_1458_;
v_isShared_1475_ = v_isSharedCheck_1488_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_lazyAssignment_1472_);
lean_inc(v_assignment_1471_);
lean_dec(v_infoState_1458_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1488_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1479_; 
v___x_1476_ = lean_box(0);
v___x_1477_ = l_Lean_PersistentArray_push___redArg(v_a_1446_, v_a_1453_);
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 2, v___x_1477_);
v___x_1479_ = v___x_1474_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_assignment_1471_);
lean_ctor_set(v_reuseFailAlloc_1487_, 1, v_lazyAssignment_1472_);
lean_ctor_set(v_reuseFailAlloc_1487_, 2, v___x_1477_);
lean_ctor_set_uint8(v_reuseFailAlloc_1487_, sizeof(void*)*3, v_enabled_1470_);
v___x_1479_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
lean_object* v___x_1481_; 
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 7, v___x_1479_);
v___x_1481_ = v___x_1468_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_env_1459_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v_nextMacroScope_1460_);
lean_ctor_set(v_reuseFailAlloc_1486_, 2, v_ngen_1461_);
lean_ctor_set(v_reuseFailAlloc_1486_, 3, v_auxDeclNGen_1462_);
lean_ctor_set(v_reuseFailAlloc_1486_, 4, v_traceState_1463_);
lean_ctor_set(v_reuseFailAlloc_1486_, 5, v_cache_1464_);
lean_ctor_set(v_reuseFailAlloc_1486_, 6, v_messages_1465_);
lean_ctor_set(v_reuseFailAlloc_1486_, 7, v___x_1479_);
lean_ctor_set(v_reuseFailAlloc_1486_, 8, v_snapshotTasks_1466_);
v___x_1481_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
lean_object* v___x_1482_; lean_object* v___x_1484_; 
v___x_1482_ = lean_st_ref_put(v___y_1437_, v___x_1481_);
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 0, v___x_1476_);
v___x_1484_ = v___x_1455_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1476_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
lean_dec_ref(v_a_1446_);
v_a_1492_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v___x_1452_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1452_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1492_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0___boxed(lean_object* v___y_1500_, lean_object* v_mkInfoTree_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v_a_1509_, lean_object* v_a_x3f_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0(v___y_1500_, v_mkInfoTree_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v_a_1509_, v_a_x3f_1510_);
lean_dec(v_a_x3f_1510_);
lean_dec_ref(v___y_1508_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v___y_1500_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(lean_object* v_x_1513_, lean_object* v_mkInfoTree_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v___x_1524_; lean_object* v_infoState_1525_; uint8_t v_enabled_1526_; 
v___x_1524_ = lean_st_ref_get(v___y_1522_);
v_infoState_1525_ = lean_ctor_get(v___x_1524_, 7);
lean_inc_ref(v_infoState_1525_);
lean_dec(v___x_1524_);
v_enabled_1526_ = lean_ctor_get_uint8(v_infoState_1525_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1525_);
if (v_enabled_1526_ == 0)
{
lean_object* v___x_1527_; 
lean_dec_ref(v_mkInfoTree_1514_);
lean_inc(v___y_1522_);
lean_inc_ref(v___y_1521_);
lean_inc(v___y_1520_);
lean_inc_ref(v___y_1519_);
lean_inc(v___y_1518_);
lean_inc_ref(v___y_1517_);
lean_inc(v___y_1516_);
lean_inc_ref(v___y_1515_);
v___x_1527_ = lean_apply_9(v_x_1513_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, lean_box(0));
return v___x_1527_;
}
else
{
lean_object* v___x_1528_; lean_object* v_a_1529_; lean_object* v_r_1530_; 
v___x_1528_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___y_1522_);
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_a_1529_);
lean_dec_ref(v___x_1528_);
lean_inc(v___y_1522_);
lean_inc_ref(v___y_1521_);
lean_inc(v___y_1520_);
lean_inc_ref(v___y_1519_);
lean_inc(v___y_1518_);
lean_inc_ref(v___y_1517_);
lean_inc(v___y_1516_);
lean_inc_ref(v___y_1515_);
v_r_1530_ = lean_apply_9(v_x_1513_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, lean_box(0));
if (lean_obj_tag(v_r_1530_) == 0)
{
lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1555_; 
v_a_1531_ = lean_ctor_get(v_r_1530_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v_r_1530_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1533_ = v_r_1530_;
v_isShared_1534_ = v_isSharedCheck_1555_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v_r_1530_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1555_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1536_; 
lean_inc(v_a_1531_);
if (v_isShared_1534_ == 0)
{
lean_ctor_set_tag(v___x_1533_, 1);
v___x_1536_ = v___x_1533_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_a_1531_);
v___x_1536_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
lean_object* v___x_1537_; 
v___x_1537_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0(v___y_1522_, v_mkInfoTree_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v_a_1529_, v___x_1536_);
lean_dec_ref(v___x_1536_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1544_; 
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1544_ == 0)
{
lean_object* v_unused_1545_; 
v_unused_1545_ = lean_ctor_get(v___x_1537_, 0);
lean_dec(v_unused_1545_);
v___x_1539_ = v___x_1537_;
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
else
{
lean_dec(v___x_1537_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1542_; 
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 0, v_a_1531_);
v___x_1542_ = v___x_1539_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_a_1531_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
else
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1553_; 
lean_dec(v_a_1531_);
v_a_1546_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1548_ = v___x_1537_;
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1537_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1551_; 
if (v_isShared_1549_ == 0)
{
v___x_1551_ = v___x_1548_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_a_1546_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
}
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v_a_1556_ = lean_ctor_get(v_r_1530_, 0);
lean_inc(v_a_1556_);
lean_dec_ref_known(v_r_1530_, 1);
v___x_1557_ = lean_box(0);
v___x_1558_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0(v___y_1522_, v_mkInfoTree_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v_a_1529_, v___x_1557_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1565_ == 0)
{
lean_object* v_unused_1566_; 
v_unused_1566_ = lean_ctor_get(v___x_1558_, 0);
lean_dec(v_unused_1566_);
v___x_1560_ = v___x_1558_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_dec(v___x_1558_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
lean_ctor_set_tag(v___x_1560_, 1);
lean_ctor_set(v___x_1560_, 0, v_a_1556_);
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1556_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
else
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1574_; 
lean_dec(v_a_1556_);
v_a_1567_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1569_ = v___x_1558_;
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___x_1558_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1572_; 
if (v_isShared_1570_ == 0)
{
v___x_1572_ = v___x_1569_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_a_1567_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___boxed(lean_object* v_x_1575_, lean_object* v_mkInfoTree_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v_x_1575_, v_mkInfoTree_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(lean_object* v_msg_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
lean_object* v_ref_1593_; lean_object* v___x_1594_; lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1603_; 
v_ref_1593_ = lean_ctor_get(v___y_1590_, 2);
v___x_1594_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__2(v_msg_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1597_ = v___x_1594_;
v_isShared_1598_ = v_isSharedCheck_1603_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1594_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1603_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1599_; lean_object* v___x_1601_; 
lean_inc(v_ref_1593_);
v___x_1599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1599_, 0, v_ref_1593_);
lean_ctor_set(v___x_1599_, 1, v_a_1595_);
if (v_isShared_1598_ == 0)
{
lean_ctor_set_tag(v___x_1597_, 1);
lean_ctor_set(v___x_1597_, 0, v___x_1599_);
v___x_1601_ = v___x_1597_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1599_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg___boxed(lean_object* v_msg_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_msg_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
return v_res_1610_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___redArg(lean_object* v_a_1611_, lean_object* v_x_1612_){
_start:
{
if (lean_obj_tag(v_x_1612_) == 0)
{
uint8_t v___x_1613_; 
v___x_1613_ = 0;
return v___x_1613_;
}
else
{
lean_object* v_key_1614_; lean_object* v_tail_1615_; uint8_t v___x_1616_; 
v_key_1614_ = lean_ctor_get(v_x_1612_, 0);
v_tail_1615_ = lean_ctor_get(v_x_1612_, 2);
v___x_1616_ = lean_expr_eqv(v_key_1614_, v_a_1611_);
if (v___x_1616_ == 0)
{
v_x_1612_ = v_tail_1615_;
goto _start;
}
else
{
return v___x_1616_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___redArg___boxed(lean_object* v_a_1618_, lean_object* v_x_1619_){
_start:
{
uint8_t v_res_1620_; lean_object* v_r_1621_; 
v_res_1620_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___redArg(v_a_1618_, v_x_1619_);
lean_dec(v_x_1619_);
lean_dec_ref(v_a_1618_);
v_r_1621_ = lean_box(v_res_1620_);
return v_r_1621_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19_spec__23___redArg(lean_object* v_x_1622_, lean_object* v_x_1623_){
_start:
{
if (lean_obj_tag(v_x_1623_) == 0)
{
return v_x_1622_;
}
else
{
lean_object* v_key_1624_; lean_object* v_value_1625_; lean_object* v_tail_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1649_; 
v_key_1624_ = lean_ctor_get(v_x_1623_, 0);
v_value_1625_ = lean_ctor_get(v_x_1623_, 1);
v_tail_1626_ = lean_ctor_get(v_x_1623_, 2);
v_isSharedCheck_1649_ = !lean_is_exclusive(v_x_1623_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1628_ = v_x_1623_;
v_isShared_1629_ = v_isSharedCheck_1649_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_tail_1626_);
lean_inc(v_value_1625_);
lean_inc(v_key_1624_);
lean_dec(v_x_1623_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1649_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1630_; uint64_t v___x_1631_; uint64_t v___x_1632_; uint64_t v___x_1633_; uint64_t v_fold_1634_; uint64_t v___x_1635_; uint64_t v___x_1636_; uint64_t v___x_1637_; size_t v___x_1638_; size_t v___x_1639_; size_t v___x_1640_; size_t v___x_1641_; size_t v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1645_; 
v___x_1630_ = lean_array_get_size(v_x_1622_);
v___x_1631_ = l_Lean_Expr_hash(v_key_1624_);
v___x_1632_ = 32ULL;
v___x_1633_ = lean_uint64_shift_right(v___x_1631_, v___x_1632_);
v_fold_1634_ = lean_uint64_xor(v___x_1631_, v___x_1633_);
v___x_1635_ = 16ULL;
v___x_1636_ = lean_uint64_shift_right(v_fold_1634_, v___x_1635_);
v___x_1637_ = lean_uint64_xor(v_fold_1634_, v___x_1636_);
v___x_1638_ = lean_uint64_to_usize(v___x_1637_);
v___x_1639_ = lean_usize_of_nat(v___x_1630_);
v___x_1640_ = ((size_t)1ULL);
v___x_1641_ = lean_usize_sub(v___x_1639_, v___x_1640_);
v___x_1642_ = lean_usize_land(v___x_1638_, v___x_1641_);
v___x_1643_ = lean_array_uget_borrowed(v_x_1622_, v___x_1642_);
lean_inc(v___x_1643_);
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 2, v___x_1643_);
v___x_1645_ = v___x_1628_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_key_1624_);
lean_ctor_set(v_reuseFailAlloc_1648_, 1, v_value_1625_);
lean_ctor_set(v_reuseFailAlloc_1648_, 2, v___x_1643_);
v___x_1645_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
lean_object* v___x_1646_; 
v___x_1646_ = lean_array_uset(v_x_1622_, v___x_1642_, v___x_1645_);
v_x_1622_ = v___x_1646_;
v_x_1623_ = v_tail_1626_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19___redArg(lean_object* v_i_1650_, lean_object* v_source_1651_, lean_object* v_target_1652_){
_start:
{
lean_object* v___x_1653_; uint8_t v___x_1654_; 
v___x_1653_ = lean_array_get_size(v_source_1651_);
v___x_1654_ = lean_nat_dec_lt(v_i_1650_, v___x_1653_);
if (v___x_1654_ == 0)
{
lean_dec_ref(v_source_1651_);
lean_dec(v_i_1650_);
return v_target_1652_;
}
else
{
lean_object* v_es_1655_; lean_object* v___x_1656_; lean_object* v_source_1657_; lean_object* v_target_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v_es_1655_ = lean_array_fget(v_source_1651_, v_i_1650_);
v___x_1656_ = lean_box(0);
v_source_1657_ = lean_array_fset(v_source_1651_, v_i_1650_, v___x_1656_);
v_target_1658_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19_spec__23___redArg(v_target_1652_, v_es_1655_);
v___x_1659_ = lean_unsigned_to_nat(1u);
v___x_1660_ = lean_nat_add(v_i_1650_, v___x_1659_);
lean_dec(v_i_1650_);
v_i_1650_ = v___x_1660_;
v_source_1651_ = v_source_1657_;
v_target_1652_ = v_target_1658_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17___redArg(lean_object* v_data_1662_){
_start:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v_nbuckets_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1663_ = lean_array_get_size(v_data_1662_);
v___x_1664_ = lean_unsigned_to_nat(2u);
v_nbuckets_1665_ = lean_nat_mul(v___x_1663_, v___x_1664_);
v___x_1666_ = lean_unsigned_to_nat(0u);
v___x_1667_ = lean_box(0);
v___x_1668_ = lean_mk_array(v_nbuckets_1665_, v___x_1667_);
v___x_1669_ = lean_array_propagate_mark(v_data_1662_, v___x_1668_);
v___x_1670_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19___redArg(v___x_1666_, v_data_1662_, v___x_1669_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11___redArg(lean_object* v_m_1671_, lean_object* v_a_1672_, lean_object* v_b_1673_){
_start:
{
lean_object* v_size_1674_; lean_object* v_buckets_1675_; lean_object* v___x_1676_; uint64_t v___x_1677_; uint64_t v___x_1678_; uint64_t v___x_1679_; uint64_t v_fold_1680_; uint64_t v___x_1681_; uint64_t v___x_1682_; uint64_t v___x_1683_; size_t v___x_1684_; size_t v___x_1685_; size_t v___x_1686_; size_t v___x_1687_; size_t v___x_1688_; lean_object* v_bkt_1689_; uint8_t v___x_1690_; 
v_size_1674_ = lean_ctor_get(v_m_1671_, 0);
v_buckets_1675_ = lean_ctor_get(v_m_1671_, 1);
v___x_1676_ = lean_array_get_size(v_buckets_1675_);
v___x_1677_ = l_Lean_Expr_hash(v_a_1672_);
v___x_1678_ = 32ULL;
v___x_1679_ = lean_uint64_shift_right(v___x_1677_, v___x_1678_);
v_fold_1680_ = lean_uint64_xor(v___x_1677_, v___x_1679_);
v___x_1681_ = 16ULL;
v___x_1682_ = lean_uint64_shift_right(v_fold_1680_, v___x_1681_);
v___x_1683_ = lean_uint64_xor(v_fold_1680_, v___x_1682_);
v___x_1684_ = lean_uint64_to_usize(v___x_1683_);
v___x_1685_ = lean_usize_of_nat(v___x_1676_);
v___x_1686_ = ((size_t)1ULL);
v___x_1687_ = lean_usize_sub(v___x_1685_, v___x_1686_);
v___x_1688_ = lean_usize_land(v___x_1684_, v___x_1687_);
v_bkt_1689_ = lean_array_uget_borrowed(v_buckets_1675_, v___x_1688_);
v___x_1690_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___redArg(v_a_1672_, v_bkt_1689_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1711_; 
lean_inc_ref(v_buckets_1675_);
lean_inc(v_size_1674_);
v_isSharedCheck_1711_ = !lean_is_exclusive(v_m_1671_);
if (v_isSharedCheck_1711_ == 0)
{
lean_object* v_unused_1712_; lean_object* v_unused_1713_; 
v_unused_1712_ = lean_ctor_get(v_m_1671_, 1);
lean_dec(v_unused_1712_);
v_unused_1713_ = lean_ctor_get(v_m_1671_, 0);
lean_dec(v_unused_1713_);
v___x_1692_ = v_m_1671_;
v_isShared_1693_ = v_isSharedCheck_1711_;
goto v_resetjp_1691_;
}
else
{
lean_dec(v_m_1671_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1711_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1694_; lean_object* v_size_x27_1695_; lean_object* v___x_1696_; lean_object* v_buckets_x27_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; uint8_t v___x_1703_; 
v___x_1694_ = lean_unsigned_to_nat(1u);
v_size_x27_1695_ = lean_nat_add(v_size_1674_, v___x_1694_);
lean_dec(v_size_1674_);
lean_inc(v_bkt_1689_);
v___x_1696_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1696_, 0, v_a_1672_);
lean_ctor_set(v___x_1696_, 1, v_b_1673_);
lean_ctor_set(v___x_1696_, 2, v_bkt_1689_);
v_buckets_x27_1697_ = lean_array_uset(v_buckets_1675_, v___x_1688_, v___x_1696_);
v___x_1698_ = lean_unsigned_to_nat(4u);
v___x_1699_ = lean_nat_mul(v_size_x27_1695_, v___x_1698_);
v___x_1700_ = lean_unsigned_to_nat(3u);
v___x_1701_ = lean_nat_div(v___x_1699_, v___x_1700_);
lean_dec(v___x_1699_);
v___x_1702_ = lean_array_get_size(v_buckets_x27_1697_);
v___x_1703_ = lean_nat_dec_le(v___x_1701_, v___x_1702_);
lean_dec(v___x_1701_);
if (v___x_1703_ == 0)
{
lean_object* v_val_1704_; lean_object* v___x_1706_; 
v_val_1704_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17___redArg(v_buckets_x27_1697_);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 1, v_val_1704_);
lean_ctor_set(v___x_1692_, 0, v_size_x27_1695_);
v___x_1706_ = v___x_1692_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_size_x27_1695_);
lean_ctor_set(v_reuseFailAlloc_1707_, 1, v_val_1704_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
else
{
lean_object* v___x_1709_; 
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 1, v_buckets_x27_1697_);
lean_ctor_set(v___x_1692_, 0, v_size_x27_1695_);
v___x_1709_ = v___x_1692_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_size_x27_1695_);
lean_ctor_set(v_reuseFailAlloc_1710_, 1, v_buckets_x27_1697_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
}
else
{
lean_dec(v_b_1673_);
lean_dec_ref(v_a_1672_);
return v_m_1671_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19___redArg(lean_object* v_mvarId_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v___x_1718_; lean_object* v_mctx_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1718_ = lean_st_ref_get(v___y_1716_);
v_mctx_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc_ref(v_mctx_1719_);
lean_dec(v___x_1718_);
v___x_1720_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_1719_, v_mvarId_1714_);
lean_dec_ref(v_mctx_1719_);
v___x_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1720_);
v___x_1722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1721_);
lean_ctor_set(v___x_1722_, 1, v___y_1715_);
v___x_1723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1722_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19___redArg___boxed(lean_object* v_mvarId_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19___redArg(v_mvarId_1724_, v___y_1725_, v___y_1726_);
lean_dec(v___y_1726_);
lean_dec(v_mvarId_1724_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20___redArg(lean_object* v_mvarId_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
lean_object* v___x_1733_; lean_object* v_mctx_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1733_ = lean_st_ref_get(v___y_1731_);
v_mctx_1734_ = lean_ctor_get(v___x_1733_, 0);
lean_inc_ref(v_mctx_1734_);
lean_dec(v___x_1733_);
v___x_1735_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_1734_, v_mvarId_1729_);
lean_dec_ref(v_mctx_1734_);
v___x_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1735_);
v___x_1737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1736_);
lean_ctor_set(v___x_1737_, 1, v___y_1730_);
v___x_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1737_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20___redArg___boxed(lean_object* v_mvarId_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
lean_object* v_res_1743_; 
v_res_1743_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20___redArg(v_mvarId_1739_, v___y_1740_, v___y_1741_);
lean_dec(v___y_1741_);
lean_dec(v_mvarId_1739_);
return v_res_1743_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10___redArg(lean_object* v_m_1744_, lean_object* v_a_1745_){
_start:
{
lean_object* v_buckets_1746_; lean_object* v___x_1747_; uint64_t v___x_1748_; uint64_t v___x_1749_; uint64_t v___x_1750_; uint64_t v_fold_1751_; uint64_t v___x_1752_; uint64_t v___x_1753_; uint64_t v___x_1754_; size_t v___x_1755_; size_t v___x_1756_; size_t v___x_1757_; size_t v___x_1758_; size_t v___x_1759_; lean_object* v___x_1760_; uint8_t v___x_1761_; 
v_buckets_1746_ = lean_ctor_get(v_m_1744_, 1);
v___x_1747_ = lean_array_get_size(v_buckets_1746_);
v___x_1748_ = l_Lean_Expr_hash(v_a_1745_);
v___x_1749_ = 32ULL;
v___x_1750_ = lean_uint64_shift_right(v___x_1748_, v___x_1749_);
v_fold_1751_ = lean_uint64_xor(v___x_1748_, v___x_1750_);
v___x_1752_ = 16ULL;
v___x_1753_ = lean_uint64_shift_right(v_fold_1751_, v___x_1752_);
v___x_1754_ = lean_uint64_xor(v_fold_1751_, v___x_1753_);
v___x_1755_ = lean_uint64_to_usize(v___x_1754_);
v___x_1756_ = lean_usize_of_nat(v___x_1747_);
v___x_1757_ = ((size_t)1ULL);
v___x_1758_ = lean_usize_sub(v___x_1756_, v___x_1757_);
v___x_1759_ = lean_usize_land(v___x_1755_, v___x_1758_);
v___x_1760_ = lean_array_uget_borrowed(v_buckets_1746_, v___x_1759_);
v___x_1761_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___redArg(v_a_1745_, v___x_1760_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10___redArg___boxed(lean_object* v_m_1762_, lean_object* v_a_1763_){
_start:
{
uint8_t v_res_1764_; lean_object* v_r_1765_; 
v_res_1764_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10___redArg(v_m_1762_, v_a_1763_);
lean_dec_ref(v_a_1763_);
lean_dec_ref(v_m_1762_);
v_r_1765_ = lean_box(v_res_1764_);
return v_r_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(lean_object* v_mvarId_1770_, lean_object* v_e_1771_, lean_object* v_a_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v_d_1783_; lean_object* v_b_1784_; lean_object* v___y_1785_; uint8_t v___x_1791_; 
v___x_1791_ = l_Lean_Expr_hasExprMVar(v_e_1771_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
lean_dec_ref(v_e_1771_);
v___x_1792_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12___closed__0));
v___x_1793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1792_);
lean_ctor_set(v___x_1793_, 1, v_a_1772_);
v___x_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1793_);
return v___x_1794_;
}
else
{
uint8_t v___x_1795_; 
v___x_1795_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10___redArg(v_a_1772_, v_e_1771_);
if (v___x_1795_ == 0)
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1796_ = lean_box(0);
lean_inc_ref(v_e_1771_);
v___x_1797_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11___redArg(v_a_1772_, v_e_1771_, v___x_1796_);
switch(lean_obj_tag(v_e_1771_))
{
case 11:
{
lean_object* v_struct_1798_; 
v_struct_1798_ = lean_ctor_get(v_e_1771_, 2);
lean_inc_ref(v_struct_1798_);
lean_dec_ref_known(v_e_1771_, 3);
v_e_1771_ = v_struct_1798_;
v_a_1772_ = v___x_1797_;
goto _start;
}
case 7:
{
lean_object* v_binderType_1800_; lean_object* v_body_1801_; 
v_binderType_1800_ = lean_ctor_get(v_e_1771_, 1);
lean_inc_ref(v_binderType_1800_);
v_body_1801_ = lean_ctor_get(v_e_1771_, 2);
lean_inc_ref(v_body_1801_);
lean_dec_ref_known(v_e_1771_, 3);
v_d_1783_ = v_binderType_1800_;
v_b_1784_ = v_body_1801_;
v___y_1785_ = v___x_1797_;
goto v___jp_1782_;
}
case 6:
{
lean_object* v_binderType_1802_; lean_object* v_body_1803_; 
v_binderType_1802_ = lean_ctor_get(v_e_1771_, 1);
lean_inc_ref(v_binderType_1802_);
v_body_1803_ = lean_ctor_get(v_e_1771_, 2);
lean_inc_ref(v_body_1803_);
lean_dec_ref_known(v_e_1771_, 3);
v_d_1783_ = v_binderType_1802_;
v_b_1784_ = v_body_1803_;
v___y_1785_ = v___x_1797_;
goto v___jp_1782_;
}
case 8:
{
lean_object* v_type_1804_; lean_object* v_value_1805_; lean_object* v_body_1806_; lean_object* v___x_1807_; 
v_type_1804_ = lean_ctor_get(v_e_1771_, 1);
lean_inc_ref(v_type_1804_);
v_value_1805_ = lean_ctor_get(v_e_1771_, 2);
lean_inc_ref(v_value_1805_);
v_body_1806_ = lean_ctor_get(v_e_1771_, 3);
lean_inc_ref(v_body_1806_);
lean_dec_ref_known(v_e_1771_, 4);
v___x_1807_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(v_mvarId_1770_, v_type_1804_, v___x_1797_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_a_1808_; lean_object* v_fst_1809_; 
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
lean_inc(v_a_1808_);
v_fst_1809_ = lean_ctor_get(v_a_1808_, 0);
if (lean_obj_tag(v_fst_1809_) == 0)
{
lean_dec(v_a_1808_);
lean_dec_ref(v_body_1806_);
lean_dec_ref(v_value_1805_);
return v___x_1807_;
}
else
{
lean_object* v_snd_1810_; lean_object* v___x_1811_; 
lean_dec_ref_known(v___x_1807_, 1);
v_snd_1810_ = lean_ctor_get(v_a_1808_, 1);
lean_inc(v_snd_1810_);
lean_dec(v_a_1808_);
v___x_1811_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(v_mvarId_1770_, v_value_1805_, v_snd_1810_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_a_1812_; lean_object* v_fst_1813_; 
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
lean_inc(v_a_1812_);
v_fst_1813_ = lean_ctor_get(v_a_1812_, 0);
if (lean_obj_tag(v_fst_1813_) == 0)
{
lean_dec(v_a_1812_);
lean_dec_ref(v_body_1806_);
return v___x_1811_;
}
else
{
lean_object* v_snd_1814_; 
lean_dec_ref_known(v___x_1811_, 1);
v_snd_1814_ = lean_ctor_get(v_a_1812_, 1);
lean_inc(v_snd_1814_);
lean_dec(v_a_1812_);
v_e_1771_ = v_body_1806_;
v_a_1772_ = v_snd_1814_;
goto _start;
}
}
else
{
lean_dec_ref(v_body_1806_);
return v___x_1811_;
}
}
}
else
{
lean_dec_ref(v_body_1806_);
lean_dec_ref(v_value_1805_);
return v___x_1807_;
}
}
case 10:
{
lean_object* v_expr_1816_; 
v_expr_1816_ = lean_ctor_get(v_e_1771_, 1);
lean_inc_ref(v_expr_1816_);
lean_dec_ref_known(v_e_1771_, 2);
v_e_1771_ = v_expr_1816_;
v_a_1772_ = v___x_1797_;
goto _start;
}
case 5:
{
lean_object* v_fn_1818_; lean_object* v_arg_1819_; lean_object* v___x_1820_; 
v_fn_1818_ = lean_ctor_get(v_e_1771_, 0);
lean_inc_ref(v_fn_1818_);
v_arg_1819_ = lean_ctor_get(v_e_1771_, 1);
lean_inc_ref(v_arg_1819_);
lean_dec_ref_known(v_e_1771_, 2);
v___x_1820_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(v_mvarId_1770_, v_fn_1818_, v___x_1797_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v_a_1821_; lean_object* v_fst_1822_; 
v_a_1821_ = lean_ctor_get(v___x_1820_, 0);
lean_inc(v_a_1821_);
v_fst_1822_ = lean_ctor_get(v_a_1821_, 0);
if (lean_obj_tag(v_fst_1822_) == 0)
{
lean_dec(v_a_1821_);
lean_dec_ref(v_arg_1819_);
return v___x_1820_;
}
else
{
lean_object* v_snd_1823_; 
lean_dec_ref_known(v___x_1820_, 1);
v_snd_1823_ = lean_ctor_get(v_a_1821_, 1);
lean_inc(v_snd_1823_);
lean_dec(v_a_1821_);
v_e_1771_ = v_arg_1819_;
v_a_1772_ = v_snd_1823_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_1819_);
return v___x_1820_;
}
}
case 2:
{
lean_object* v_mvarId_1825_; lean_object* v___x_1826_; 
v_mvarId_1825_ = lean_ctor_get(v_e_1771_, 0);
lean_inc(v_mvarId_1825_);
lean_dec_ref_known(v_e_1771_, 1);
v___x_1826_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12(v_mvarId_1770_, v_mvarId_1825_, v___x_1797_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
return v___x_1826_;
}
default: 
{
lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
lean_dec_ref(v_e_1771_);
v___x_1827_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12___closed__0));
v___x_1828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
lean_ctor_set(v___x_1828_, 1, v___x_1797_);
v___x_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
return v___x_1829_;
}
}
}
else
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
lean_dec_ref(v_e_1771_);
v___x_1830_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12___closed__0));
v___x_1831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1830_);
lean_ctor_set(v___x_1831_, 1, v_a_1772_);
v___x_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1831_);
return v___x_1832_;
}
}
v___jp_1782_:
{
lean_object* v___x_1786_; 
v___x_1786_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(v_mvarId_1770_, v_d_1783_, v___y_1785_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v_a_1787_; lean_object* v_fst_1788_; 
v_a_1787_ = lean_ctor_get(v___x_1786_, 0);
lean_inc(v_a_1787_);
v_fst_1788_ = lean_ctor_get(v_a_1787_, 0);
if (lean_obj_tag(v_fst_1788_) == 0)
{
lean_dec(v_a_1787_);
lean_dec_ref(v_b_1784_);
return v___x_1786_;
}
else
{
lean_object* v_snd_1789_; 
lean_dec_ref_known(v___x_1786_, 1);
v_snd_1789_ = lean_ctor_get(v_a_1787_, 1);
lean_inc(v_snd_1789_);
lean_dec(v_a_1787_);
v_e_1771_ = v_b_1784_;
v_a_1772_ = v_snd_1789_;
goto _start;
}
}
else
{
lean_dec_ref(v_b_1784_);
return v___x_1786_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12(lean_object* v_mvarId_1833_, lean_object* v_mvarId_x27_1834_, lean_object* v_a_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
uint8_t v___x_1845_; 
v___x_1845_ = l_Lean_instBEqMVarId_beq(v_mvarId_1833_, v_mvarId_x27_1834_);
if (v___x_1845_ == 0)
{
lean_object* v___x_1846_; 
v___x_1846_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19___redArg(v_mvarId_x27_1834_, v_a_1835_, v___y_1841_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1930_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1849_ = v___x_1846_;
v_isShared_1850_ = v_isSharedCheck_1930_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1846_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1930_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v_fst_1851_; 
v_fst_1851_ = lean_ctor_get(v_a_1847_, 0);
lean_inc(v_fst_1851_);
if (lean_obj_tag(v_fst_1851_) == 0)
{
lean_object* v_snd_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1870_; 
lean_dec(v_mvarId_x27_1834_);
v_snd_1852_ = lean_ctor_get(v_a_1847_, 1);
v_isSharedCheck_1870_ = !lean_is_exclusive(v_a_1847_);
if (v_isSharedCheck_1870_ == 0)
{
lean_object* v_unused_1871_; 
v_unused_1871_ = lean_ctor_get(v_a_1847_, 0);
lean_dec(v_unused_1871_);
v___x_1854_ = v_a_1847_;
v_isShared_1855_ = v_isSharedCheck_1870_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_snd_1852_);
lean_dec(v_a_1847_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1870_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1869_; 
v_a_1856_ = lean_ctor_get(v_fst_1851_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v_fst_1851_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1858_ = v_fst_1851_;
v_isShared_1859_ = v_isSharedCheck_1869_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v_fst_1851_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1869_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1861_; 
if (v_isShared_1859_ == 0)
{
v___x_1861_ = v___x_1858_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1856_);
v___x_1861_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
lean_object* v___x_1863_; 
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 0, v___x_1861_);
v___x_1863_ = v___x_1854_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v___x_1861_);
lean_ctor_set(v_reuseFailAlloc_1867_, 1, v_snd_1852_);
v___x_1863_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
lean_object* v___x_1865_; 
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 0, v___x_1863_);
v___x_1865_ = v___x_1849_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___x_1863_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
}
}
}
else
{
lean_object* v_a_1872_; 
lean_del_object(v___x_1849_);
v_a_1872_ = lean_ctor_get(v_fst_1851_, 0);
lean_inc(v_a_1872_);
lean_dec_ref_known(v_fst_1851_, 1);
if (lean_obj_tag(v_a_1872_) == 0)
{
lean_object* v_snd_1873_; lean_object* v___x_1874_; 
v_snd_1873_ = lean_ctor_get(v_a_1847_, 1);
lean_inc(v_snd_1873_);
lean_dec(v_a_1847_);
v___x_1874_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20___redArg(v_mvarId_x27_1834_, v_snd_1873_, v___y_1841_);
lean_dec(v_mvarId_x27_1834_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1918_; 
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1877_ = v___x_1874_;
v_isShared_1878_ = v_isSharedCheck_1918_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1874_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1918_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v_fst_1879_; 
v_fst_1879_ = lean_ctor_get(v_a_1875_, 0);
lean_inc(v_fst_1879_);
if (lean_obj_tag(v_fst_1879_) == 0)
{
lean_object* v_snd_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1898_; 
v_snd_1880_ = lean_ctor_get(v_a_1875_, 1);
v_isSharedCheck_1898_ = !lean_is_exclusive(v_a_1875_);
if (v_isSharedCheck_1898_ == 0)
{
lean_object* v_unused_1899_; 
v_unused_1899_ = lean_ctor_get(v_a_1875_, 0);
lean_dec(v_unused_1899_);
v___x_1882_ = v_a_1875_;
v_isShared_1883_ = v_isSharedCheck_1898_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_snd_1880_);
lean_dec(v_a_1875_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1898_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1897_; 
v_a_1884_ = lean_ctor_get(v_fst_1879_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v_fst_1879_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1886_ = v_fst_1879_;
v_isShared_1887_ = v_isSharedCheck_1897_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v_fst_1879_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1897_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1884_);
v___x_1889_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
lean_object* v___x_1891_; 
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 0, v___x_1889_);
v___x_1891_ = v___x_1882_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1889_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v_snd_1880_);
v___x_1891_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
lean_object* v___x_1893_; 
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 0, v___x_1891_);
v___x_1893_ = v___x_1877_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1891_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
}
}
else
{
lean_object* v_a_1900_; 
v_a_1900_ = lean_ctor_get(v_fst_1879_, 0);
lean_inc(v_a_1900_);
lean_dec_ref_known(v_fst_1879_, 1);
if (lean_obj_tag(v_a_1900_) == 0)
{
lean_object* v_snd_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1912_; 
v_snd_1901_ = lean_ctor_get(v_a_1875_, 1);
v_isSharedCheck_1912_ = !lean_is_exclusive(v_a_1875_);
if (v_isSharedCheck_1912_ == 0)
{
lean_object* v_unused_1913_; 
v_unused_1913_ = lean_ctor_get(v_a_1875_, 0);
lean_dec(v_unused_1913_);
v___x_1903_ = v_a_1875_;
v_isShared_1904_ = v_isSharedCheck_1912_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_snd_1901_);
lean_dec(v_a_1875_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1912_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1905_; lean_object* v___x_1907_; 
v___x_1905_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12___closed__0));
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 0, v___x_1905_);
v___x_1907_ = v___x_1903_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1905_);
lean_ctor_set(v_reuseFailAlloc_1911_, 1, v_snd_1901_);
v___x_1907_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
lean_object* v___x_1909_; 
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 0, v___x_1907_);
v___x_1909_ = v___x_1877_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1907_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
else
{
lean_object* v_val_1914_; lean_object* v_snd_1915_; lean_object* v_mvarIdPending_1916_; 
lean_del_object(v___x_1877_);
v_val_1914_ = lean_ctor_get(v_a_1900_, 0);
lean_inc(v_val_1914_);
lean_dec_ref_known(v_a_1900_, 1);
v_snd_1915_ = lean_ctor_get(v_a_1875_, 1);
lean_inc(v_snd_1915_);
lean_dec(v_a_1875_);
v_mvarIdPending_1916_ = lean_ctor_get(v_val_1914_, 1);
lean_inc(v_mvarIdPending_1916_);
lean_dec(v_val_1914_);
v_mvarId_x27_1834_ = v_mvarIdPending_1916_;
v_a_1835_ = v_snd_1915_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
v_a_1919_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1874_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1874_);
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
lean_object* v_snd_1927_; lean_object* v_val_1928_; lean_object* v___x_1929_; 
lean_dec(v_mvarId_x27_1834_);
v_snd_1927_ = lean_ctor_get(v_a_1847_, 1);
lean_inc(v_snd_1927_);
lean_dec(v_a_1847_);
v_val_1928_ = lean_ctor_get(v_a_1872_, 0);
lean_inc(v_val_1928_);
lean_dec_ref_known(v_a_1872_, 1);
v___x_1929_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(v_mvarId_1833_, v_val_1928_, v_snd_1927_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
return v___x_1929_;
}
}
}
}
else
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
lean_dec(v_mvarId_x27_1834_);
v_a_1931_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1846_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1846_);
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
else
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
lean_dec(v_mvarId_x27_1834_);
v___x_1939_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12___closed__1));
v___x_1940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1939_);
lean_ctor_set(v___x_1940_, 1, v_a_1835_);
v___x_1941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1940_);
return v___x_1941_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12___boxed(lean_object* v_mvarId_1942_, lean_object* v_mvarId_x27_1943_, lean_object* v_a_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12(v_mvarId_1942_, v_mvarId_x27_1943_, v_a_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v_mvarId_1942_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6___boxed(lean_object* v_mvarId_1955_, lean_object* v_e_1956_, lean_object* v_a_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(v_mvarId_1955_, v_e_1956_, v_a_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v_mvarId_1955_);
return v_res_1967_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1968_ = lean_box(0);
v___x_1969_ = lean_unsigned_to_nat(16u);
v___x_1970_ = lean_mk_array(v___x_1969_, v___x_1968_);
return v___x_1970_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1971_ = lean_obj_once(&l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__0, &l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__0_once, _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__0);
v___x_1972_ = lean_unsigned_to_nat(0u);
v___x_1973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1973_, 0, v___x_1972_);
lean_ctor_set(v___x_1973_, 1, v___x_1971_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(lean_object* v_mvarId_1974_, lean_object* v_e_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
uint8_t v___x_1985_; 
v___x_1985_ = l_Lean_Expr_hasExprMVar(v_e_1975_);
if (v___x_1985_ == 0)
{
uint8_t v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
lean_dec_ref(v_e_1975_);
v___x_1986_ = 1;
v___x_1987_ = lean_box(v___x_1986_);
v___x_1988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1987_);
return v___x_1988_;
}
else
{
uint8_t v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1989_ = 0;
v___x_1990_ = lean_obj_once(&l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1, &l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1_once, _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1);
v___x_1991_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(v_mvarId_1974_, v_e_1975_, v___x_1990_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2005_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_1994_ = v___x_1991_;
v_isShared_1995_ = v_isSharedCheck_2005_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1991_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2005_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v_fst_1996_; 
v_fst_1996_ = lean_ctor_get(v_a_1992_, 0);
lean_inc(v_fst_1996_);
lean_dec(v_a_1992_);
if (lean_obj_tag(v_fst_1996_) == 0)
{
lean_object* v___x_1997_; lean_object* v___x_1999_; 
lean_dec_ref_known(v_fst_1996_, 1);
v___x_1997_ = lean_box(v___x_1989_);
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 0, v___x_1997_);
v___x_1999_ = v___x_1994_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v___x_1997_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
else
{
lean_object* v___x_2001_; lean_object* v___x_2003_; 
lean_dec_ref_known(v_fst_1996_, 1);
v___x_2001_ = lean_box(v___x_1985_);
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 0, v___x_2001_);
v___x_2003_ = v___x_1994_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_2001_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
}
else
{
lean_object* v_a_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2013_; 
v_a_2006_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_2008_ = v___x_1991_;
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_a_2006_);
lean_dec(v___x_1991_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2011_; 
if (v_isShared_2009_ == 0)
{
v___x_2011_ = v___x_2008_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_a_2006_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___boxed(lean_object* v_mvarId_2014_, lean_object* v_e_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(v_mvarId_2014_, v_e_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
lean_dec(v___y_2021_);
lean_dec_ref(v___y_2020_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v_mvarId_2014_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11_spec__13___redArg(lean_object* v_x_2026_, lean_object* v_x_2027_, lean_object* v_x_2028_, lean_object* v_x_2029_){
_start:
{
lean_object* v_ks_2030_; lean_object* v_vs_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2055_; 
v_ks_2030_ = lean_ctor_get(v_x_2026_, 0);
v_vs_2031_ = lean_ctor_get(v_x_2026_, 1);
v_isSharedCheck_2055_ = !lean_is_exclusive(v_x_2026_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2033_ = v_x_2026_;
v_isShared_2034_ = v_isSharedCheck_2055_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_vs_2031_);
lean_inc(v_ks_2030_);
lean_dec(v_x_2026_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2055_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2035_; uint8_t v___x_2036_; 
v___x_2035_ = lean_array_get_size(v_ks_2030_);
v___x_2036_ = lean_nat_dec_lt(v_x_2027_, v___x_2035_);
if (v___x_2036_ == 0)
{
lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2040_; 
lean_dec(v_x_2027_);
v___x_2037_ = lean_array_push(v_ks_2030_, v_x_2028_);
v___x_2038_ = lean_array_push(v_vs_2031_, v_x_2029_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 1, v___x_2038_);
lean_ctor_set(v___x_2033_, 0, v___x_2037_);
v___x_2040_ = v___x_2033_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2037_);
lean_ctor_set(v_reuseFailAlloc_2041_, 1, v___x_2038_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
else
{
lean_object* v_k_x27_2042_; uint8_t v___x_2043_; 
v_k_x27_2042_ = lean_array_fget_borrowed(v_ks_2030_, v_x_2027_);
v___x_2043_ = l_Lean_instBEqMVarId_beq(v_x_2028_, v_k_x27_2042_);
if (v___x_2043_ == 0)
{
lean_object* v___x_2045_; 
if (v_isShared_2034_ == 0)
{
v___x_2045_ = v___x_2033_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_ks_2030_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v_vs_2031_);
v___x_2045_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2046_ = lean_unsigned_to_nat(1u);
v___x_2047_ = lean_nat_add(v_x_2027_, v___x_2046_);
lean_dec(v_x_2027_);
v_x_2026_ = v___x_2045_;
v_x_2027_ = v___x_2047_;
goto _start;
}
}
else
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2053_; 
v___x_2050_ = lean_array_fset(v_ks_2030_, v_x_2027_, v_x_2028_);
v___x_2051_ = lean_array_fset(v_vs_2031_, v_x_2027_, v_x_2029_);
lean_dec(v_x_2027_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 1, v___x_2051_);
lean_ctor_set(v___x_2033_, 0, v___x_2050_);
v___x_2053_ = v___x_2033_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v___x_2050_);
lean_ctor_set(v_reuseFailAlloc_2054_, 1, v___x_2051_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___redArg(lean_object* v_n_2056_, lean_object* v_k_2057_, lean_object* v_v_2058_){
_start:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2059_ = lean_unsigned_to_nat(0u);
v___x_2060_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11_spec__13___redArg(v_n_2056_, v___x_2059_, v_k_2057_, v_v_2058_);
return v___x_2060_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2061_; 
v___x_2061_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(lean_object* v_x_2062_, size_t v_x_2063_, size_t v_x_2064_, lean_object* v_x_2065_, lean_object* v_x_2066_){
_start:
{
if (lean_obj_tag(v_x_2062_) == 0)
{
lean_object* v_es_2067_; size_t v___x_2068_; size_t v___x_2069_; lean_object* v_j_2070_; lean_object* v___x_2071_; uint8_t v___x_2072_; 
v_es_2067_ = lean_ctor_get(v_x_2062_, 0);
v___x_2068_ = ((size_t)31ULL);
v___x_2069_ = lean_usize_land(v_x_2063_, v___x_2068_);
v_j_2070_ = lean_usize_to_nat(v___x_2069_);
v___x_2071_ = lean_array_get_size(v_es_2067_);
v___x_2072_ = lean_nat_dec_lt(v_j_2070_, v___x_2071_);
if (v___x_2072_ == 0)
{
lean_dec(v_j_2070_);
lean_dec(v_x_2066_);
lean_dec(v_x_2065_);
return v_x_2062_;
}
else
{
lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2111_; 
lean_inc_ref(v_es_2067_);
v_isSharedCheck_2111_ = !lean_is_exclusive(v_x_2062_);
if (v_isSharedCheck_2111_ == 0)
{
lean_object* v_unused_2112_; 
v_unused_2112_ = lean_ctor_get(v_x_2062_, 0);
lean_dec(v_unused_2112_);
v___x_2074_ = v_x_2062_;
v_isShared_2075_ = v_isSharedCheck_2111_;
goto v_resetjp_2073_;
}
else
{
lean_dec(v_x_2062_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2111_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v_v_2076_; lean_object* v___x_2077_; lean_object* v_xs_x27_2078_; lean_object* v___y_2080_; 
v_v_2076_ = lean_array_fget(v_es_2067_, v_j_2070_);
v___x_2077_ = lean_box(0);
v_xs_x27_2078_ = lean_array_fset(v_es_2067_, v_j_2070_, v___x_2077_);
switch(lean_obj_tag(v_v_2076_))
{
case 0:
{
lean_object* v_key_2085_; lean_object* v_val_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2096_; 
v_key_2085_ = lean_ctor_get(v_v_2076_, 0);
v_val_2086_ = lean_ctor_get(v_v_2076_, 1);
v_isSharedCheck_2096_ = !lean_is_exclusive(v_v_2076_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2088_ = v_v_2076_;
v_isShared_2089_ = v_isSharedCheck_2096_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_val_2086_);
lean_inc(v_key_2085_);
lean_dec(v_v_2076_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2096_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
uint8_t v___x_2090_; 
v___x_2090_ = l_Lean_instBEqMVarId_beq(v_x_2065_, v_key_2085_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2091_; lean_object* v___x_2092_; 
lean_del_object(v___x_2088_);
v___x_2091_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2085_, v_val_2086_, v_x_2065_, v_x_2066_);
v___x_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
v___y_2080_ = v___x_2092_;
goto v___jp_2079_;
}
else
{
lean_object* v___x_2094_; 
lean_dec(v_val_2086_);
lean_dec(v_key_2085_);
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 1, v_x_2066_);
lean_ctor_set(v___x_2088_, 0, v_x_2065_);
v___x_2094_ = v___x_2088_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_x_2065_);
lean_ctor_set(v_reuseFailAlloc_2095_, 1, v_x_2066_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
v___y_2080_ = v___x_2094_;
goto v___jp_2079_;
}
}
}
}
case 1:
{
lean_object* v_node_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2109_; 
v_node_2097_ = lean_ctor_get(v_v_2076_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v_v_2076_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2099_ = v_v_2076_;
v_isShared_2100_ = v_isSharedCheck_2109_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_node_2097_);
lean_dec(v_v_2076_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2109_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
size_t v___x_2101_; size_t v___x_2102_; size_t v___x_2103_; size_t v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2107_; 
v___x_2101_ = ((size_t)5ULL);
v___x_2102_ = lean_usize_shift_right(v_x_2063_, v___x_2101_);
v___x_2103_ = ((size_t)1ULL);
v___x_2104_ = lean_usize_add(v_x_2064_, v___x_2103_);
v___x_2105_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(v_node_2097_, v___x_2102_, v___x_2104_, v_x_2065_, v_x_2066_);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 0, v___x_2105_);
v___x_2107_ = v___x_2099_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2105_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
v___y_2080_ = v___x_2107_;
goto v___jp_2079_;
}
}
}
default: 
{
lean_object* v___x_2110_; 
v___x_2110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2110_, 0, v_x_2065_);
lean_ctor_set(v___x_2110_, 1, v_x_2066_);
v___y_2080_ = v___x_2110_;
goto v___jp_2079_;
}
}
v___jp_2079_:
{
lean_object* v___x_2081_; lean_object* v___x_2083_; 
v___x_2081_ = lean_array_fset(v_xs_x27_2078_, v_j_2070_, v___y_2080_);
lean_dec(v_j_2070_);
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 0, v___x_2081_);
v___x_2083_ = v___x_2074_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2081_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
}
else
{
lean_object* v_ks_2113_; lean_object* v_vs_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2132_; 
v_ks_2113_ = lean_ctor_get(v_x_2062_, 0);
v_vs_2114_ = lean_ctor_get(v_x_2062_, 1);
v_isSharedCheck_2132_ = !lean_is_exclusive(v_x_2062_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2116_ = v_x_2062_;
v_isShared_2117_ = v_isSharedCheck_2132_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_vs_2114_);
lean_inc(v_ks_2113_);
lean_dec(v_x_2062_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2132_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2119_; 
if (v_isShared_2117_ == 0)
{
v___x_2119_ = v___x_2116_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_ks_2113_);
lean_ctor_set(v_reuseFailAlloc_2131_, 1, v_vs_2114_);
v___x_2119_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
lean_object* v_newNode_2120_; size_t v___x_2121_; uint8_t v___x_2122_; 
v_newNode_2120_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___redArg(v___x_2119_, v_x_2065_, v_x_2066_);
v___x_2121_ = ((size_t)7ULL);
v___x_2122_ = lean_usize_dec_le(v___x_2121_, v_x_2064_);
if (v___x_2122_ == 0)
{
lean_object* v___x_2123_; lean_object* v___x_2124_; uint8_t v___x_2125_; 
v___x_2123_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2120_);
v___x_2124_ = lean_unsigned_to_nat(4u);
v___x_2125_ = lean_nat_dec_lt(v___x_2123_, v___x_2124_);
lean_dec(v___x_2123_);
if (v___x_2125_ == 0)
{
lean_object* v_ks_2126_; lean_object* v_vs_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v_ks_2126_ = lean_ctor_get(v_newNode_2120_, 0);
lean_inc_ref(v_ks_2126_);
v_vs_2127_ = lean_ctor_get(v_newNode_2120_, 1);
lean_inc_ref(v_vs_2127_);
lean_dec_ref(v_newNode_2120_);
v___x_2128_ = lean_unsigned_to_nat(0u);
v___x_2129_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg___closed__0);
v___x_2130_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12___redArg(v_x_2064_, v_ks_2126_, v_vs_2127_, v___x_2128_, v___x_2129_);
lean_dec_ref(v_vs_2127_);
lean_dec_ref(v_ks_2126_);
return v___x_2130_;
}
else
{
return v_newNode_2120_;
}
}
else
{
return v_newNode_2120_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12___redArg(size_t v_depth_2133_, lean_object* v_keys_2134_, lean_object* v_vals_2135_, lean_object* v_i_2136_, lean_object* v_entries_2137_){
_start:
{
lean_object* v___x_2138_; uint8_t v___x_2139_; 
v___x_2138_ = lean_array_get_size(v_keys_2134_);
v___x_2139_ = lean_nat_dec_lt(v_i_2136_, v___x_2138_);
if (v___x_2139_ == 0)
{
lean_dec(v_i_2136_);
return v_entries_2137_;
}
else
{
lean_object* v_k_2140_; lean_object* v_v_2141_; uint64_t v___x_2142_; size_t v_h_2143_; size_t v___x_2144_; lean_object* v___x_2145_; size_t v___x_2146_; size_t v___x_2147_; size_t v___x_2148_; size_t v_h_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v_k_2140_ = lean_array_fget_borrowed(v_keys_2134_, v_i_2136_);
v_v_2141_ = lean_array_fget_borrowed(v_vals_2135_, v_i_2136_);
v___x_2142_ = l_Lean_instHashableMVarId_hash(v_k_2140_);
v_h_2143_ = lean_uint64_to_usize(v___x_2142_);
v___x_2144_ = ((size_t)5ULL);
v___x_2145_ = lean_unsigned_to_nat(1u);
v___x_2146_ = ((size_t)1ULL);
v___x_2147_ = lean_usize_sub(v_depth_2133_, v___x_2146_);
v___x_2148_ = lean_usize_mul(v___x_2144_, v___x_2147_);
v_h_2149_ = lean_usize_shift_right(v_h_2143_, v___x_2148_);
v___x_2150_ = lean_nat_add(v_i_2136_, v___x_2145_);
lean_dec(v_i_2136_);
lean_inc(v_v_2141_);
lean_inc(v_k_2140_);
v___x_2151_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(v_entries_2137_, v_h_2149_, v_depth_2133_, v_k_2140_, v_v_2141_);
v_i_2136_ = v___x_2150_;
v_entries_2137_ = v___x_2151_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12___redArg___boxed(lean_object* v_depth_2153_, lean_object* v_keys_2154_, lean_object* v_vals_2155_, lean_object* v_i_2156_, lean_object* v_entries_2157_){
_start:
{
size_t v_depth_boxed_2158_; lean_object* v_res_2159_; 
v_depth_boxed_2158_ = lean_unbox_usize(v_depth_2153_);
lean_dec(v_depth_2153_);
v_res_2159_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12___redArg(v_depth_boxed_2158_, v_keys_2154_, v_vals_2155_, v_i_2156_, v_entries_2157_);
lean_dec_ref(v_vals_2155_);
lean_dec_ref(v_keys_2154_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg___boxed(lean_object* v_x_2160_, lean_object* v_x_2161_, lean_object* v_x_2162_, lean_object* v_x_2163_, lean_object* v_x_2164_){
_start:
{
size_t v_x_95254__boxed_2165_; size_t v_x_95255__boxed_2166_; lean_object* v_res_2167_; 
v_x_95254__boxed_2165_ = lean_unbox_usize(v_x_2161_);
lean_dec(v_x_2161_);
v_x_95255__boxed_2166_ = lean_unbox_usize(v_x_2162_);
lean_dec(v_x_2162_);
v_res_2167_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(v_x_2160_, v_x_95254__boxed_2165_, v_x_95255__boxed_2166_, v_x_2163_, v_x_2164_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1___redArg(lean_object* v_x_2168_, lean_object* v_x_2169_, lean_object* v_x_2170_){
_start:
{
uint64_t v___x_2171_; size_t v___x_2172_; size_t v___x_2173_; lean_object* v___x_2174_; 
v___x_2171_ = l_Lean_instHashableMVarId_hash(v_x_2169_);
v___x_2172_ = lean_uint64_to_usize(v___x_2171_);
v___x_2173_ = ((size_t)1ULL);
v___x_2174_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(v_x_2168_, v___x_2172_, v___x_2173_, v_x_2169_, v_x_2170_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___redArg(lean_object* v_mvarId_2175_, lean_object* v_val_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v___x_2179_; lean_object* v_mctx_2180_; lean_object* v_cache_2181_; lean_object* v_zetaDeltaFVarIds_2182_; lean_object* v_postponed_2183_; lean_object* v_diag_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2213_; 
v___x_2179_ = lean_st_ref_take(v___y_2177_);
v_mctx_2180_ = lean_ctor_get(v___x_2179_, 0);
v_cache_2181_ = lean_ctor_get(v___x_2179_, 1);
v_zetaDeltaFVarIds_2182_ = lean_ctor_get(v___x_2179_, 2);
v_postponed_2183_ = lean_ctor_get(v___x_2179_, 3);
v_diag_2184_ = lean_ctor_get(v___x_2179_, 4);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2186_ = v___x_2179_;
v_isShared_2187_ = v_isSharedCheck_2213_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_diag_2184_);
lean_inc(v_postponed_2183_);
lean_inc(v_zetaDeltaFVarIds_2182_);
lean_inc(v_cache_2181_);
lean_inc(v_mctx_2180_);
lean_dec(v___x_2179_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2213_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v_depth_2188_; lean_object* v_levelAssignDepth_2189_; lean_object* v_lmvarCounter_2190_; lean_object* v_mvarCounter_2191_; lean_object* v_lDecls_2192_; lean_object* v_decls_2193_; lean_object* v_userNames_2194_; lean_object* v_lAssignment_2195_; lean_object* v_eAssignment_2196_; lean_object* v_dAssignment_2197_; lean_object* v_instanceTypedMVars_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2212_; 
v_depth_2188_ = lean_ctor_get(v_mctx_2180_, 0);
v_levelAssignDepth_2189_ = lean_ctor_get(v_mctx_2180_, 1);
v_lmvarCounter_2190_ = lean_ctor_get(v_mctx_2180_, 2);
v_mvarCounter_2191_ = lean_ctor_get(v_mctx_2180_, 3);
v_lDecls_2192_ = lean_ctor_get(v_mctx_2180_, 4);
v_decls_2193_ = lean_ctor_get(v_mctx_2180_, 5);
v_userNames_2194_ = lean_ctor_get(v_mctx_2180_, 6);
v_lAssignment_2195_ = lean_ctor_get(v_mctx_2180_, 7);
v_eAssignment_2196_ = lean_ctor_get(v_mctx_2180_, 8);
v_dAssignment_2197_ = lean_ctor_get(v_mctx_2180_, 9);
v_instanceTypedMVars_2198_ = lean_ctor_get(v_mctx_2180_, 10);
v_isSharedCheck_2212_ = !lean_is_exclusive(v_mctx_2180_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2200_ = v_mctx_2180_;
v_isShared_2201_ = v_isSharedCheck_2212_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_instanceTypedMVars_2198_);
lean_inc(v_dAssignment_2197_);
lean_inc(v_eAssignment_2196_);
lean_inc(v_lAssignment_2195_);
lean_inc(v_userNames_2194_);
lean_inc(v_decls_2193_);
lean_inc(v_lDecls_2192_);
lean_inc(v_mvarCounter_2191_);
lean_inc(v_lmvarCounter_2190_);
lean_inc(v_levelAssignDepth_2189_);
lean_inc(v_depth_2188_);
lean_dec(v_mctx_2180_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2212_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2205_; 
v___x_2202_ = lean_box(0);
v___x_2203_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1___redArg(v_eAssignment_2196_, v_mvarId_2175_, v_val_2176_);
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 8, v___x_2203_);
v___x_2205_ = v___x_2200_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_depth_2188_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v_levelAssignDepth_2189_);
lean_ctor_set(v_reuseFailAlloc_2211_, 2, v_lmvarCounter_2190_);
lean_ctor_set(v_reuseFailAlloc_2211_, 3, v_mvarCounter_2191_);
lean_ctor_set(v_reuseFailAlloc_2211_, 4, v_lDecls_2192_);
lean_ctor_set(v_reuseFailAlloc_2211_, 5, v_decls_2193_);
lean_ctor_set(v_reuseFailAlloc_2211_, 6, v_userNames_2194_);
lean_ctor_set(v_reuseFailAlloc_2211_, 7, v_lAssignment_2195_);
lean_ctor_set(v_reuseFailAlloc_2211_, 8, v___x_2203_);
lean_ctor_set(v_reuseFailAlloc_2211_, 9, v_dAssignment_2197_);
lean_ctor_set(v_reuseFailAlloc_2211_, 10, v_instanceTypedMVars_2198_);
v___x_2205_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
lean_object* v___x_2207_; 
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 0, v___x_2205_);
v___x_2207_ = v___x_2186_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v___x_2205_);
lean_ctor_set(v_reuseFailAlloc_2210_, 1, v_cache_2181_);
lean_ctor_set(v_reuseFailAlloc_2210_, 2, v_zetaDeltaFVarIds_2182_);
lean_ctor_set(v_reuseFailAlloc_2210_, 3, v_postponed_2183_);
lean_ctor_set(v_reuseFailAlloc_2210_, 4, v_diag_2184_);
v___x_2207_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2208_ = lean_st_ref_put(v___y_2177_, v___x_2207_);
v___x_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2202_);
return v___x_2209_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___redArg___boxed(lean_object* v_mvarId_2214_, lean_object* v_val_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v_res_2218_; 
v_res_2218_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___redArg(v_mvarId_2214_, v_val_2215_, v___y_2216_);
lean_dec(v___y_2216_);
return v_res_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(lean_object* v_o_2219_, lean_object* v___y_2220_){
_start:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v_env_2224_; lean_object* v___x_2225_; lean_object* v_toEnvExtension_2226_; lean_object* v_asyncMode_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v_merged_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2238_; 
v___x_2222_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_2223_ = lean_st_ref_get(v___y_2220_);
v_env_2224_ = lean_ctor_get(v___x_2223_, 0);
lean_inc_ref(v_env_2224_);
lean_dec(v___x_2223_);
v___x_2225_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_2226_ = lean_ctor_get(v___x_2225_, 0);
v_asyncMode_2227_ = lean_ctor_get(v_toEnvExtension_2226_, 2);
v___x_2228_ = lean_box(0);
v___x_2229_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2222_, v___x_2225_, v_env_2224_, v_asyncMode_2227_, v___x_2228_);
v_merged_2230_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2238_ == 0)
{
lean_object* v_unused_2239_; 
v_unused_2239_ = lean_ctor_get(v___x_2229_, 1);
lean_dec(v_unused_2239_);
v___x_2232_ = v___x_2229_;
v_isShared_2233_ = v_isSharedCheck_2238_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_merged_2230_);
lean_dec(v___x_2229_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2238_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2235_; 
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 1, v_merged_2230_);
lean_ctor_set(v___x_2232_, 0, v_o_2219_);
v___x_2235_ = v___x_2232_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_o_2219_);
lean_ctor_set(v_reuseFailAlloc_2237_, 1, v_merged_2230_);
v___x_2235_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
lean_object* v___x_2236_; 
v___x_2236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2235_);
return v___x_2236_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg___boxed(lean_object* v_o_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(v_o_2240_, v___y_2241_);
lean_dec(v___y_2241_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v_toCold_2253_; lean_object* v_options_2254_; lean_object* v___x_2255_; 
v_toCold_2253_ = lean_ctor_get(v___y_2250_, 0);
v_options_2254_ = lean_ctor_get(v_toCold_2253_, 2);
lean_inc_ref(v_options_2254_);
v___x_2255_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(v_options_2254_, v___y_2251_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___boxed(lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
lean_object* v_res_2265_; 
v_res_2265_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
return v_res_2265_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__6(void){
_start:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2273_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5));
v___x_2274_ = l_Lean_stringToMessageData(v___x_2273_);
return v___x_2274_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__8(void){
_start:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2276_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__7));
v___x_2277_ = l_Lean_stringToMessageData(v___x_2276_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5(lean_object* v_usingArg_2281_, lean_object* v_snd_2282_, uint8_t v___x_2283_, lean_object* v___x_2284_, uint8_t v___x_2285_, uint8_t v_useReducible_2286_, uint8_t v___x_2287_, lean_object* v___x_2288_, lean_object* v___x_2289_, lean_object* v_simprocs_2290_, lean_object* v_discharge_x3f_2291_, lean_object* v_snd_2292_, lean_object* v___f_2293_, lean_object* v___x_2294_, lean_object* v___x_2295_, lean_object* v___x_2296_, lean_object* v___x_2297_, lean_object* v___f_2298_, lean_object* v_a_2299_, lean_object* v___x_2300_, lean_object* v___f_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v___y_2312_; lean_object* v___y_2313_; lean_object* v___y_2314_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2327_; lean_object* v___y_2328_; lean_object* v___y_2329_; lean_object* v___y_2330_; lean_object* v___y_2331_; lean_object* v___y_2332_; lean_object* v___y_2333_; lean_object* v___y_2334_; lean_object* v___y_2335_; lean_object* v___y_2336_; lean_object* v___y_2337_; lean_object* v___y_2338_; lean_object* v___y_2339_; lean_object* v___y_2340_; lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v___y_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v___y_2387_; 
if (lean_obj_tag(v_usingArg_2281_) == 1)
{
lean_object* v_val_2524_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___x_2576_; lean_object* v_infoState_2577_; uint8_t v_enabled_2578_; 
v_val_2524_ = lean_ctor_get(v_usingArg_2281_, 0);
lean_inc(v_val_2524_);
lean_dec_ref_known(v_usingArg_2281_, 1);
v___x_2576_ = lean_st_ref_get(v___y_2309_);
v_infoState_2577_ = lean_ctor_get(v___x_2576_, 7);
lean_inc_ref(v_infoState_2577_);
lean_dec(v___x_2576_);
v_enabled_2578_ = lean_ctor_get_uint8(v_infoState_2577_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2577_);
if (v_enabled_2578_ == 0)
{
lean_dec_ref(v___f_2301_);
v___y_2526_ = v___y_2302_;
v___y_2527_ = v___y_2303_;
v___y_2528_ = v___y_2304_;
v___y_2529_ = v___y_2305_;
v___y_2530_ = v___y_2306_;
v___y_2531_ = v___y_2307_;
v___y_2532_ = v___y_2308_;
v___y_2533_ = v___y_2309_;
goto v___jp_2525_;
}
else
{
lean_object* v___x_2579_; lean_object* v_a_2580_; lean_object* v___f_2581_; lean_object* v___x_2582_; 
v___x_2579_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___y_2309_);
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
lean_inc(v_a_2580_);
lean_dec_ref(v___x_2579_);
v___f_2581_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___boxed), 10, 1);
lean_closure_set(v___f_2581_, 0, v_a_2580_);
v___x_2582_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v___f_2581_, v___f_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_dec_ref_known(v___x_2582_, 1);
v___y_2526_ = v___y_2302_;
v___y_2527_ = v___y_2303_;
v___y_2528_ = v___y_2304_;
v___y_2529_ = v___y_2305_;
v___y_2530_ = v___y_2306_;
v___y_2531_ = v___y_2307_;
v___y_2532_ = v___y_2308_;
v___y_2533_ = v___y_2309_;
goto v___jp_2525_;
}
else
{
lean_object* v_a_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2590_; 
lean_dec(v_val_2524_);
lean_dec_ref(v_a_2299_);
lean_dec_ref(v___f_2298_);
lean_dec(v___x_2297_);
lean_dec_ref(v___x_2296_);
lean_dec_ref(v___x_2295_);
lean_dec_ref(v___x_2294_);
lean_dec_ref(v___f_2293_);
lean_dec_ref(v_snd_2292_);
lean_dec(v_discharge_x3f_2291_);
lean_dec_ref(v_simprocs_2290_);
lean_dec_ref(v___x_2289_);
lean_dec_ref(v___x_2284_);
lean_dec(v_snd_2282_);
v_a_2583_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2585_ = v___x_2582_;
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_a_2583_);
lean_dec(v___x_2582_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2588_; 
if (v_isShared_2586_ == 0)
{
v___x_2588_ = v___x_2585_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_a_2583_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
}
v___jp_2525_:
{
lean_object* v___x_2534_; lean_object* v_mctx_2535_; lean_object* v_mvarCounter_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2534_ = lean_st_ref_get(v___y_2531_);
v_mctx_2535_ = lean_ctor_get(v___x_2534_, 0);
lean_inc_ref(v_mctx_2535_);
lean_dec(v___x_2534_);
v_mvarCounter_2536_ = lean_ctor_get(v_mctx_2535_, 3);
lean_inc(v_mvarCounter_2536_);
lean_dec_ref(v_mctx_2535_);
v___x_2537_ = lean_box(0);
v___x_2538_ = l_Lean_Elab_Tactic_elabTerm(v_val_2524_, v___x_2537_, v___x_2283_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v_a_2539_; lean_object* v___x_2540_; 
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
lean_inc_n(v_a_2539_, 2);
lean_dec_ref_known(v___x_2538_, 1);
v___x_2540_ = l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(v_snd_2282_, v_a_2539_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_object* v_a_2541_; uint8_t v___x_2542_; 
v_a_2541_ = lean_ctor_get(v___x_2540_, 0);
lean_inc(v_a_2541_);
lean_dec_ref_known(v___x_2540_, 1);
v___x_2542_ = lean_unbox(v_a_2541_);
lean_dec(v_a_2541_);
if (v___x_2542_ == 0)
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2559_; 
lean_dec(v_mvarCounter_2536_);
lean_dec_ref(v_a_2299_);
lean_dec_ref(v___f_2298_);
lean_dec(v___x_2297_);
lean_dec_ref(v___x_2296_);
lean_dec_ref(v___x_2295_);
lean_dec_ref(v___x_2294_);
lean_dec_ref(v___f_2293_);
lean_dec_ref(v_snd_2292_);
lean_dec(v_discharge_x3f_2291_);
lean_dec_ref(v_simprocs_2290_);
lean_dec_ref(v___x_2289_);
lean_dec_ref(v___x_2284_);
v___x_2543_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__6);
v___x_2544_ = l_Lean_indentExpr(v_a_2539_);
v___x_2545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2543_);
lean_ctor_set(v___x_2545_, 1, v___x_2544_);
v___x_2546_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__8, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__8_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__8);
v___x_2547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2545_);
lean_ctor_set(v___x_2547_, 1, v___x_2546_);
v___x_2548_ = l_Lean_Expr_mvar___override(v_snd_2282_);
v___x_2549_ = l_Lean_MessageData_ofExpr(v___x_2548_);
v___x_2550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2547_);
lean_ctor_set(v___x_2550_, 1, v___x_2549_);
v___x_2551_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v___x_2550_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2554_ = v___x_2551_;
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2551_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2557_; 
if (v_isShared_2555_ == 0)
{
v___x_2557_ = v___x_2554_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_a_2552_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
else
{
v___y_2376_ = v___x_2537_;
v___y_2377_ = v_a_2539_;
v___y_2378_ = v_mvarCounter_2536_;
v___y_2379_ = v___x_2537_;
v___y_2380_ = v___y_2526_;
v___y_2381_ = v___y_2527_;
v___y_2382_ = v___y_2528_;
v___y_2383_ = v___y_2529_;
v___y_2384_ = v___y_2530_;
v___y_2385_ = v___y_2531_;
v___y_2386_ = v___y_2532_;
v___y_2387_ = v___y_2533_;
goto v___jp_2375_;
}
}
else
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2567_; 
lean_dec(v_a_2539_);
lean_dec(v_mvarCounter_2536_);
lean_dec_ref(v_a_2299_);
lean_dec_ref(v___f_2298_);
lean_dec(v___x_2297_);
lean_dec_ref(v___x_2296_);
lean_dec_ref(v___x_2295_);
lean_dec_ref(v___x_2294_);
lean_dec_ref(v___f_2293_);
lean_dec_ref(v_snd_2292_);
lean_dec(v_discharge_x3f_2291_);
lean_dec_ref(v_simprocs_2290_);
lean_dec_ref(v___x_2289_);
lean_dec_ref(v___x_2284_);
lean_dec(v_snd_2282_);
v_a_2560_ = lean_ctor_get(v___x_2540_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2540_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2562_ = v___x_2540_;
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2540_);
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
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2575_; 
lean_dec(v_mvarCounter_2536_);
lean_dec_ref(v_a_2299_);
lean_dec_ref(v___f_2298_);
lean_dec(v___x_2297_);
lean_dec_ref(v___x_2296_);
lean_dec_ref(v___x_2295_);
lean_dec_ref(v___x_2294_);
lean_dec_ref(v___f_2293_);
lean_dec_ref(v_snd_2292_);
lean_dec(v_discharge_x3f_2291_);
lean_dec_ref(v_simprocs_2290_);
lean_dec_ref(v___x_2289_);
lean_dec_ref(v___x_2284_);
lean_dec(v_snd_2282_);
v_a_2568_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2570_ = v___x_2538_;
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2538_);
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
}
else
{
lean_object* v_lctx_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; 
lean_dec_ref(v___f_2301_);
lean_dec_ref(v_a_2299_);
lean_dec_ref(v___f_2298_);
lean_dec(v___x_2297_);
lean_dec_ref(v___x_2296_);
lean_dec_ref(v___x_2295_);
lean_dec_ref(v___x_2294_);
lean_dec_ref(v___f_2293_);
lean_dec_ref(v___x_2284_);
lean_dec(v_usingArg_2281_);
v_lctx_2591_ = lean_ctor_get(v___y_2306_, 2);
v___x_2592_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__10));
v___x_2593_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2591_, v___x_2592_);
if (lean_obj_tag(v___x_2593_) == 1)
{
lean_object* v_val_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v_val_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_val_2594_);
lean_dec_ref_known(v___x_2593_, 1);
v___x_2595_ = l_Lean_LocalDecl_fvarId(v_val_2594_);
lean_dec(v_val_2594_);
v___x_2596_ = lean_mk_empty_array_with_capacity(v___x_2288_);
v___x_2597_ = lean_array_push(v___x_2596_, v___x_2595_);
lean_inc_ref(v_snd_2292_);
v___x_2598_ = l_Lean_Meta_simpGoal(v_snd_2282_, v___x_2289_, v_simprocs_2290_, v_discharge_x3f_2291_, v___x_2285_, v___x_2597_, v_snd_2292_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2627_; 
v_a_2599_ = lean_ctor_get(v___x_2598_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2601_ = v___x_2598_;
v_isShared_2602_ = v_isSharedCheck_2627_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_a_2599_);
lean_dec(v___x_2598_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2627_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v_fst_2603_; 
v_fst_2603_ = lean_ctor_get(v_a_2599_, 0);
if (lean_obj_tag(v_fst_2603_) == 1)
{
lean_object* v_val_2604_; lean_object* v_snd_2605_; lean_object* v_snd_2606_; lean_object* v___x_2607_; 
lean_del_object(v___x_2601_);
lean_dec_ref(v_snd_2292_);
v_val_2604_ = lean_ctor_get(v_fst_2603_, 0);
lean_inc(v_val_2604_);
v_snd_2605_ = lean_ctor_get(v_a_2599_, 1);
lean_inc(v_snd_2605_);
lean_dec(v_a_2599_);
v_snd_2606_ = lean_ctor_get(v_val_2604_, 1);
lean_inc(v_snd_2606_);
lean_dec(v_val_2604_);
v___x_2607_ = l_Lean_MVarId_assumption(v_snd_2606_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2614_ == 0)
{
lean_object* v_unused_2615_; 
v_unused_2615_ = lean_ctor_get(v___x_2607_, 0);
lean_dec(v_unused_2615_);
v___x_2609_ = v___x_2607_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_dec(v___x_2607_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2612_; 
if (v_isShared_2610_ == 0)
{
lean_ctor_set(v___x_2609_, 0, v_snd_2605_);
v___x_2612_ = v___x_2609_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_snd_2605_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
else
{
lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2623_; 
lean_dec(v_snd_2605_);
v_a_2616_ = lean_ctor_get(v___x_2607_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2618_ = v___x_2607_;
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2607_);
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
lean_object* v___x_2625_; 
lean_dec(v_a_2599_);
if (v_isShared_2602_ == 0)
{
lean_ctor_set(v___x_2601_, 0, v_snd_2292_);
v___x_2625_ = v___x_2601_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_snd_2292_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
}
else
{
lean_object* v_a_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2635_; 
lean_dec_ref(v_snd_2292_);
v_a_2628_ = lean_ctor_get(v___x_2598_, 0);
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2630_ = v___x_2598_;
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_dec(v___x_2598_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2633_; 
if (v_isShared_2631_ == 0)
{
v___x_2633_ = v___x_2630_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_a_2628_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
}
else
{
lean_object* v___x_2636_; 
lean_dec(v___x_2593_);
lean_dec(v_discharge_x3f_2291_);
lean_dec_ref(v_simprocs_2290_);
lean_dec_ref(v___x_2289_);
v___x_2636_ = l_Lean_MVarId_assumption(v_snd_2282_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2643_; 
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2643_ == 0)
{
lean_object* v_unused_2644_; 
v_unused_2644_ = lean_ctor_get(v___x_2636_, 0);
lean_dec(v_unused_2644_);
v___x_2638_ = v___x_2636_;
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
else
{
lean_dec(v___x_2636_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v___x_2641_; 
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 0, v_snd_2292_);
v___x_2641_ = v___x_2638_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_snd_2292_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
else
{
lean_object* v_a_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2652_; 
lean_dec_ref(v_snd_2292_);
v_a_2645_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2647_ = v___x_2636_;
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_a_2645_);
lean_dec(v___x_2636_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2650_; 
if (v_isShared_2648_ == 0)
{
v___x_2650_ = v___x_2647_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_a_2645_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
}
}
v___jp_2311_:
{
lean_object* v___x_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2322_; 
v___x_2315_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___redArg(v_snd_2282_, v___y_2313_, v___y_2314_);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2322_ == 0)
{
lean_object* v_unused_2323_; 
v_unused_2323_ = lean_ctor_get(v___x_2315_, 0);
lean_dec(v_unused_2323_);
v___x_2317_ = v___x_2315_;
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
else
{
lean_dec(v___x_2315_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 0, v___y_2312_);
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v___y_2312_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
v___jp_2324_:
{
lean_object* v___x_2341_; 
v___x_2341_ = l_Lean_Core_mkFreshUserName(v___y_2329_, v___y_2336_, v___y_2330_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v_a_2342_; lean_object* v___x_2343_; 
v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
lean_inc_n(v_a_2342_, 2);
lean_dec_ref_known(v___x_2341_, 1);
v___x_2343_ = l_Lean_MVarId_rename(v___y_2335_, v___y_2340_, v_a_2342_, v___y_2332_, v___y_2328_, v___y_2336_, v___y_2330_);
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_object* v_a_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___f_2349_; lean_object* v___x_2350_; 
v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
lean_inc_n(v_a_2344_, 2);
lean_dec_ref_known(v___x_2343_, 1);
v___x_2345_ = lean_box(v___x_2283_);
v___x_2346_ = lean_box(v___x_2285_);
v___x_2347_ = lean_box(v_useReducible_2286_);
v___x_2348_ = lean_box(v___x_2287_);
v___f_2349_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___boxed), 19, 10);
lean_closure_set(v___f_2349_, 0, v_a_2344_);
lean_closure_set(v___f_2349_, 1, v_a_2342_);
lean_closure_set(v___f_2349_, 2, v___x_2345_);
lean_closure_set(v___f_2349_, 3, v___y_2326_);
lean_closure_set(v___f_2349_, 4, v___y_2327_);
lean_closure_set(v___f_2349_, 5, v___x_2284_);
lean_closure_set(v___f_2349_, 6, v___x_2346_);
lean_closure_set(v___f_2349_, 7, v___y_2325_);
lean_closure_set(v___f_2349_, 8, v___x_2347_);
lean_closure_set(v___f_2349_, 9, v___x_2348_);
v___x_2350_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg(v_a_2344_, v___f_2349_, v___y_2334_, v___y_2331_, v___y_2337_, v___y_2333_, v___y_2332_, v___y_2328_, v___y_2336_, v___y_2330_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_dec_ref_known(v___x_2350_, 1);
v___y_2312_ = v___y_2338_;
v___y_2313_ = v___y_2339_;
v___y_2314_ = v___y_2328_;
goto v___jp_2311_;
}
else
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
lean_dec_ref(v___y_2339_);
lean_dec_ref(v___y_2338_);
lean_dec(v_snd_2282_);
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2353_ = v___x_2350_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2350_);
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
else
{
lean_object* v_a_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2366_; 
lean_dec(v_a_2342_);
lean_dec_ref(v___y_2339_);
lean_dec_ref(v___y_2338_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
lean_dec(v___y_2325_);
lean_dec_ref(v___x_2284_);
lean_dec(v_snd_2282_);
v_a_2359_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2361_ = v___x_2343_;
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_a_2359_);
lean_dec(v___x_2343_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2364_; 
if (v_isShared_2362_ == 0)
{
v___x_2364_ = v___x_2361_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_a_2359_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
}
else
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2374_; 
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec_ref(v___y_2338_);
lean_dec(v___y_2335_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
lean_dec(v___y_2325_);
lean_dec_ref(v___x_2284_);
lean_dec(v_snd_2282_);
v_a_2367_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2369_ = v___x_2341_;
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2341_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2372_; 
if (v_isShared_2370_ == 0)
{
v___x_2372_ = v___x_2369_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_a_2367_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
}
v___jp_2375_:
{
lean_object* v___x_2388_; 
lean_inc(v_snd_2282_);
v___x_2388_ = l_Lean_MVarId_getType(v_snd_2282_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v_a_2389_; lean_object* v___x_2390_; 
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
lean_inc(v_a_2389_);
lean_dec_ref_known(v___x_2388_, 1);
lean_inc(v_snd_2282_);
v___x_2390_ = l_Lean_MVarId_getTag(v_snd_2282_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; lean_object* v___x_2392_; 
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_a_2391_);
lean_dec_ref_known(v___x_2390_, 1);
v___x_2392_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2389_, v_a_2391_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v_a_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
lean_inc(v_a_2393_);
lean_dec_ref_known(v___x_2392_, 1);
v___x_2394_ = l_Lean_Expr_mvarId_x21(v_a_2393_);
v___x_2395_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1));
lean_inc_ref(v___y_2377_);
v___x_2396_ = l_Lean_MVarId_note(v___x_2394_, v___x_2395_, v___y_2377_, v___y_2379_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v_a_2397_; lean_object* v_fst_2398_; lean_object* v_snd_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
lean_inc(v_a_2397_);
lean_dec_ref_known(v___x_2396_, 1);
v_fst_2398_ = lean_ctor_get(v_a_2397_, 0);
lean_inc_n(v_fst_2398_, 2);
v_snd_2399_ = lean_ctor_get(v_a_2397_, 1);
lean_inc(v_snd_2399_);
lean_dec(v_a_2397_);
v___x_2400_ = lean_mk_empty_array_with_capacity(v___x_2288_);
v___x_2401_ = lean_array_push(v___x_2400_, v_fst_2398_);
v___x_2402_ = l_Lean_Meta_simpGoal(v_snd_2399_, v___x_2289_, v_simprocs_2290_, v_discharge_x3f_2291_, v___x_2285_, v___x_2401_, v_snd_2292_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v_a_2403_; lean_object* v_fst_2404_; 
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
lean_inc(v_a_2403_);
lean_dec_ref_known(v___x_2402_, 1);
v_fst_2404_ = lean_ctor_get(v_a_2403_, 0);
if (lean_obj_tag(v_fst_2404_) == 0)
{
lean_object* v_snd_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2475_; 
lean_dec(v_fst_2398_);
lean_dec(v___y_2378_);
lean_dec(v___y_2376_);
lean_dec_ref(v___x_2284_);
v_snd_2405_ = lean_ctor_get(v_a_2403_, 1);
v_isSharedCheck_2475_ = !lean_is_exclusive(v_a_2403_);
if (v_isSharedCheck_2475_ == 0)
{
lean_object* v_unused_2476_; 
v_unused_2476_ = lean_ctor_get(v_a_2403_, 0);
lean_dec(v_unused_2476_);
v___x_2407_ = v_a_2403_;
v_isShared_2408_ = v_isSharedCheck_2475_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_snd_2405_);
lean_dec(v_a_2403_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2475_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v___x_2409_; lean_object* v_a_2410_; uint8_t v___x_2411_; 
v___x_2409_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
lean_inc(v_a_2410_);
lean_dec_ref(v___x_2409_);
v___x_2411_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_a_2410_);
lean_dec(v_a_2410_);
if (v___x_2411_ == 0)
{
lean_del_object(v___x_2407_);
lean_dec_ref(v___y_2377_);
lean_dec_ref(v_a_2299_);
lean_dec_ref(v___f_2298_);
lean_dec(v___x_2297_);
lean_dec_ref(v___x_2296_);
lean_dec_ref(v___x_2295_);
lean_dec_ref(v___x_2294_);
lean_dec_ref(v___f_2293_);
v___y_2312_ = v_snd_2405_;
v___y_2313_ = v_a_2393_;
v___y_2314_ = v___y_2385_;
goto v___jp_2311_;
}
else
{
if (lean_obj_tag(v___y_2377_) == 1)
{
lean_object* v_fvarId_2412_; lean_object* v_lctx_2413_; lean_object* v___x_2414_; 
v_fvarId_2412_ = lean_ctor_get(v___y_2377_, 0);
lean_inc(v_fvarId_2412_);
lean_dec_ref_known(v___y_2377_, 1);
v_lctx_2413_ = lean_ctor_get(v___y_2384_, 2);
lean_inc_ref(v_lctx_2413_);
v___x_2414_ = l_Lean_LocalContext_getRoundtrippingUserName_x3f(v_lctx_2413_, v_fvarId_2412_);
if (lean_obj_tag(v___x_2414_) == 1)
{
lean_object* v_val_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2474_; 
v_val_2415_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2417_ = v___x_2414_;
v_isShared_2418_ = v_isSharedCheck_2474_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_val_2415_);
lean_dec(v___x_2414_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2474_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2419_ = l_Lean_mkIdent(v_val_2415_);
lean_inc_ref(v___f_2293_);
lean_inc(v___y_2387_);
lean_inc_ref(v___y_2386_);
lean_inc(v___y_2385_);
lean_inc_ref(v___y_2384_);
lean_inc(v___y_2383_);
lean_inc_ref(v___y_2382_);
lean_inc(v___y_2381_);
lean_inc_ref(v___y_2380_);
v___x_2420_ = lean_apply_9(v___f_2293_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, lean_box(0));
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_object* v_a_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; 
v_a_2421_ = lean_ctor_get(v___x_2420_, 0);
lean_inc_n(v_a_2421_, 2);
lean_dec_ref_known(v___x_2420_, 1);
v___x_2422_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2));
lean_inc_ref(v___x_2296_);
lean_inc_ref(v___x_2295_);
lean_inc_ref(v___x_2294_);
v___x_2423_ = l_Lean_Name_mkStr4(v___x_2294_, v___x_2295_, v___x_2296_, v___x_2422_);
v___x_2424_ = l_Lean_Syntax_node1(v_a_2421_, v___x_2297_, v___x_2419_);
v___x_2425_ = l_Lean_Syntax_node1(v_a_2421_, v___x_2423_, v___x_2424_);
lean_inc(v___y_2387_);
lean_inc_ref(v___y_2386_);
lean_inc(v___y_2385_);
lean_inc_ref(v___y_2384_);
lean_inc(v___y_2383_);
lean_inc_ref(v___y_2382_);
lean_inc(v___y_2381_);
lean_inc_ref(v___y_2380_);
v___x_2426_ = lean_apply_9(v___f_2293_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, lean_box(0));
if (lean_obj_tag(v___x_2426_) == 0)
{
lean_object* v_a_2427_; lean_object* v_ref_2428_; lean_object* v___x_2429_; lean_object* v___x_2431_; 
v_a_2427_ = lean_ctor_get(v___x_2426_, 0);
lean_inc_n(v_a_2427_, 2);
lean_dec_ref_known(v___x_2426_, 1);
v_ref_2428_ = lean_ctor_get(v___y_2386_, 2);
v___x_2429_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__3));
if (v_isShared_2408_ == 0)
{
lean_ctor_set_tag(v___x_2407_, 2);
lean_ctor_set(v___x_2407_, 1, v___x_2429_);
lean_ctor_set(v___x_2407_, 0, v_a_2427_);
v___x_2431_ = v___x_2407_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_a_2427_);
lean_ctor_set(v_reuseFailAlloc_2457_, 1, v___x_2429_);
v___x_2431_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2436_; 
v___x_2432_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__4));
v___x_2433_ = l_Lean_Name_mkStr4(v___x_2294_, v___x_2295_, v___x_2296_, v___x_2432_);
v___x_2434_ = l_Lean_Syntax_node2(v_a_2427_, v___x_2433_, v___x_2431_, v___x_2425_);
if (v_isShared_2418_ == 0)
{
lean_ctor_set(v___x_2417_, 0, v___x_2434_);
v___x_2436_ = v___x_2417_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v___x_2434_);
v___x_2436_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
lean_object* v___x_2437_; 
lean_inc(v___y_2387_);
lean_inc_ref(v___y_2386_);
lean_inc(v___y_2385_);
lean_inc_ref(v___y_2384_);
lean_inc(v___y_2383_);
lean_inc_ref(v___y_2382_);
lean_inc(v___y_2381_);
lean_inc_ref(v___y_2380_);
v___x_2437_ = lean_apply_10(v___f_2298_, v___x_2436_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, lean_box(0));
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_a_2438_; lean_object* v___x_2439_; 
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_a_2438_);
lean_dec_ref_known(v___x_2437_, 1);
lean_inc(v_ref_2428_);
v___x_2439_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa(v_a_2299_, v_ref_2428_, v_a_2438_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
if (lean_obj_tag(v___x_2439_) == 0)
{
lean_dec_ref_known(v___x_2439_, 1);
v___y_2312_ = v_snd_2405_;
v___y_2313_ = v_a_2393_;
v___y_2314_ = v___y_2385_;
goto v___jp_2311_;
}
else
{
lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2447_; 
lean_dec(v_snd_2405_);
lean_dec(v_a_2393_);
lean_dec(v_snd_2282_);
v_a_2440_ = lean_ctor_get(v___x_2439_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2439_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2442_ = v___x_2439_;
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v___x_2439_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2445_; 
if (v_isShared_2443_ == 0)
{
v___x_2445_ = v___x_2442_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_a_2440_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
}
else
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2455_; 
lean_dec(v_snd_2405_);
lean_dec(v_a_2393_);
lean_dec_ref(v_a_2299_);
lean_dec(v_snd_2282_);
v_a_2448_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2450_ = v___x_2437_;
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___x_2437_);
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
}
}
else
{
lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2465_; 
lean_dec(v___x_2425_);
lean_del_object(v___x_2417_);
lean_del_object(v___x_2407_);
lean_dec(v_snd_2405_);
lean_dec(v_a_2393_);
lean_dec_ref(v_a_2299_);
lean_dec_ref(v___f_2298_);
lean_dec_ref(v___x_2296_);
lean_dec_ref(v___x_2295_);
lean_dec_ref(v___x_2294_);
lean_dec(v_snd_2282_);
v_a_2458_ = lean_ctor_get(v___x_2426_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2426_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2460_ = v___x_2426_;
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v___x_2426_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2463_; 
if (v_isShared_2461_ == 0)
{
v___x_2463_ = v___x_2460_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_a_2458_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
}
else
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2473_; 
lean_dec(v___x_2419_);
lean_del_object(v___x_2417_);
lean_del_object(v___x_2407_);
lean_dec(v_snd_2405_);
lean_dec(v_a_2393_);
lean_dec_ref(v_a_2299_);
lean_dec_ref(v___f_2298_);
lean_dec(v___x_2297_);
lean_dec_ref(v___x_2296_);
lean_dec_ref(v___x_2295_);
lean_dec_ref(v___x_2294_);
lean_dec_ref(v___f_2293_);
lean_dec(v_snd_2282_);
v_a_2466_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2468_ = v___x_2420_;
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___x_2420_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2471_; 
if (v_isShared_2469_ == 0)
{
v___x_2471_ = v___x_2468_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2466_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
}
else
{
lean_dec(v___x_2414_);
lean_del_object(v___x_2407_);
lean_dec_ref(v_a_2299_);
lean_dec_ref(v___f_2298_);
lean_dec(v___x_2297_);
lean_dec_ref(v___x_2296_);
lean_dec_ref(v___x_2295_);
lean_dec_ref(v___x_2294_);
lean_dec_ref(v___f_2293_);
v___y_2312_ = v_snd_2405_;
v___y_2313_ = v_a_2393_;
v___y_2314_ = v___y_2385_;
goto v___jp_2311_;
}
}
else
{
lean_del_object(v___x_2407_);
lean_dec_ref(v___y_2377_);
lean_dec_ref(v_a_2299_);
lean_dec_ref(v___f_2298_);
lean_dec(v___x_2297_);
lean_dec_ref(v___x_2296_);
lean_dec_ref(v___x_2295_);
lean_dec_ref(v___x_2294_);
lean_dec_ref(v___f_2293_);
v___y_2312_ = v_snd_2405_;
v___y_2313_ = v_a_2393_;
v___y_2314_ = v___y_2385_;
goto v___jp_2311_;
}
}
}
}
else
{
lean_object* v_val_2477_; lean_object* v_snd_2478_; lean_object* v_fst_2479_; lean_object* v_snd_2480_; lean_object* v___x_2481_; uint8_t v___x_2482_; 
lean_dec_ref(v_a_2299_);
lean_dec_ref(v___f_2298_);
lean_dec(v___x_2297_);
lean_dec_ref(v___x_2296_);
lean_dec_ref(v___x_2295_);
lean_dec_ref(v___x_2294_);
lean_dec_ref(v___f_2293_);
v_val_2477_ = lean_ctor_get(v_fst_2404_, 0);
lean_inc(v_val_2477_);
v_snd_2478_ = lean_ctor_get(v_a_2403_, 1);
lean_inc(v_snd_2478_);
lean_dec(v_a_2403_);
v_fst_2479_ = lean_ctor_get(v_val_2477_, 0);
lean_inc(v_fst_2479_);
v_snd_2480_ = lean_ctor_get(v_val_2477_, 1);
lean_inc(v_snd_2480_);
lean_dec(v_val_2477_);
v___x_2481_ = lean_array_get_size(v_fst_2479_);
v___x_2482_ = lean_nat_dec_lt(v___x_2300_, v___x_2481_);
if (v___x_2482_ == 0)
{
lean_dec(v_fst_2479_);
v___y_2325_ = v___y_2376_;
v___y_2326_ = v___y_2377_;
v___y_2327_ = v___y_2378_;
v___y_2328_ = v___y_2385_;
v___y_2329_ = v___x_2395_;
v___y_2330_ = v___y_2387_;
v___y_2331_ = v___y_2381_;
v___y_2332_ = v___y_2384_;
v___y_2333_ = v___y_2383_;
v___y_2334_ = v___y_2380_;
v___y_2335_ = v_snd_2480_;
v___y_2336_ = v___y_2386_;
v___y_2337_ = v___y_2382_;
v___y_2338_ = v_snd_2478_;
v___y_2339_ = v_a_2393_;
v___y_2340_ = v_fst_2398_;
goto v___jp_2324_;
}
else
{
lean_object* v___x_2483_; 
lean_dec(v_fst_2398_);
v___x_2483_ = lean_array_fget(v_fst_2479_, v___x_2300_);
lean_dec(v_fst_2479_);
v___y_2325_ = v___y_2376_;
v___y_2326_ = v___y_2377_;
v___y_2327_ = v___y_2378_;
v___y_2328_ = v___y_2385_;
v___y_2329_ = v___x_2395_;
v___y_2330_ = v___y_2387_;
v___y_2331_ = v___y_2381_;
v___y_2332_ = v___y_2384_;
v___y_2333_ = v___y_2383_;
v___y_2334_ = v___y_2380_;
v___y_2335_ = v_snd_2480_;
v___y_2336_ = v___y_2386_;
v___y_2337_ = v___y_2382_;
v___y_2338_ = v_snd_2478_;
v___y_2339_ = v_a_2393_;
v___y_2340_ = v___x_2483_;
goto v___jp_2324_;
}
}
}
else
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2491_; 
lean_dec(v_fst_2398_);
lean_dec(v_a_2393_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v_a_2299_);
lean_dec_ref(v___f_2298_);
lean_dec(v___x_2297_);
lean_dec_ref(v___x_2296_);
lean_dec_ref(v___x_2295_);
lean_dec_ref(v___x_2294_);
lean_dec_ref(v___f_2293_);
lean_dec_ref(v___x_2284_);
lean_dec(v_snd_2282_);
v_a_2484_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2486_ = v___x_2402_;
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2402_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2489_; 
if (v_isShared_2487_ == 0)
{
v___x_2489_ = v___x_2486_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_a_2484_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
}
}
else
{
lean_object* v_a_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2499_; 
lean_dec(v_a_2393_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v_a_2299_);
lean_dec_ref(v___f_2298_);
lean_dec(v___x_2297_);
lean_dec_ref(v___x_2296_);
lean_dec_ref(v___x_2295_);
lean_dec_ref(v___x_2294_);
lean_dec_ref(v___f_2293_);
lean_dec_ref(v_snd_2292_);
lean_dec(v_discharge_x3f_2291_);
lean_dec_ref(v_simprocs_2290_);
lean_dec_ref(v___x_2289_);
lean_dec_ref(v___x_2284_);
lean_dec(v_snd_2282_);
v_a_2492_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2494_ = v___x_2396_;
v_isShared_2495_ = v_isSharedCheck_2499_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_a_2492_);
lean_dec(v___x_2396_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2499_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v___x_2497_; 
if (v_isShared_2495_ == 0)
{
v___x_2497_ = v___x_2494_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v_a_2492_);
v___x_2497_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
return v___x_2497_;
}
}
}
}
else
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2507_; 
lean_dec(v___y_2379_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v_a_2299_);
lean_dec_ref(v___f_2298_);
lean_dec(v___x_2297_);
lean_dec_ref(v___x_2296_);
lean_dec_ref(v___x_2295_);
lean_dec_ref(v___x_2294_);
lean_dec_ref(v___f_2293_);
lean_dec_ref(v_snd_2292_);
lean_dec(v_discharge_x3f_2291_);
lean_dec_ref(v_simprocs_2290_);
lean_dec_ref(v___x_2289_);
lean_dec_ref(v___x_2284_);
lean_dec(v_snd_2282_);
v_a_2500_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2502_ = v___x_2392_;
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2392_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2505_; 
if (v_isShared_2503_ == 0)
{
v___x_2505_ = v___x_2502_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_a_2500_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
}
else
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2515_; 
lean_dec(v_a_2389_);
lean_dec(v___y_2379_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v_a_2299_);
lean_dec_ref(v___f_2298_);
lean_dec(v___x_2297_);
lean_dec_ref(v___x_2296_);
lean_dec_ref(v___x_2295_);
lean_dec_ref(v___x_2294_);
lean_dec_ref(v___f_2293_);
lean_dec_ref(v_snd_2292_);
lean_dec(v_discharge_x3f_2291_);
lean_dec_ref(v_simprocs_2290_);
lean_dec_ref(v___x_2289_);
lean_dec_ref(v___x_2284_);
lean_dec(v_snd_2282_);
v_a_2508_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2510_ = v___x_2390_;
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2390_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2513_; 
if (v_isShared_2511_ == 0)
{
v___x_2513_ = v___x_2510_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_a_2508_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
}
else
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2523_; 
lean_dec(v___y_2379_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v_a_2299_);
lean_dec_ref(v___f_2298_);
lean_dec(v___x_2297_);
lean_dec_ref(v___x_2296_);
lean_dec_ref(v___x_2295_);
lean_dec_ref(v___x_2294_);
lean_dec_ref(v___f_2293_);
lean_dec_ref(v_snd_2292_);
lean_dec(v_discharge_x3f_2291_);
lean_dec_ref(v_simprocs_2290_);
lean_dec_ref(v___x_2289_);
lean_dec_ref(v___x_2284_);
lean_dec(v_snd_2282_);
v_a_2516_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2518_ = v___x_2388_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2388_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2519_ == 0)
{
v___x_2521_ = v___x_2518_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_a_2516_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___boxed(lean_object** _args){
lean_object* v_usingArg_2653_ = _args[0];
lean_object* v_snd_2654_ = _args[1];
lean_object* v___x_2655_ = _args[2];
lean_object* v___x_2656_ = _args[3];
lean_object* v___x_2657_ = _args[4];
lean_object* v_useReducible_2658_ = _args[5];
lean_object* v___x_2659_ = _args[6];
lean_object* v___x_2660_ = _args[7];
lean_object* v___x_2661_ = _args[8];
lean_object* v_simprocs_2662_ = _args[9];
lean_object* v_discharge_x3f_2663_ = _args[10];
lean_object* v_snd_2664_ = _args[11];
lean_object* v___f_2665_ = _args[12];
lean_object* v___x_2666_ = _args[13];
lean_object* v___x_2667_ = _args[14];
lean_object* v___x_2668_ = _args[15];
lean_object* v___x_2669_ = _args[16];
lean_object* v___f_2670_ = _args[17];
lean_object* v_a_2671_ = _args[18];
lean_object* v___x_2672_ = _args[19];
lean_object* v___f_2673_ = _args[20];
lean_object* v___y_2674_ = _args[21];
lean_object* v___y_2675_ = _args[22];
lean_object* v___y_2676_ = _args[23];
lean_object* v___y_2677_ = _args[24];
lean_object* v___y_2678_ = _args[25];
lean_object* v___y_2679_ = _args[26];
lean_object* v___y_2680_ = _args[27];
lean_object* v___y_2681_ = _args[28];
lean_object* v___y_2682_ = _args[29];
_start:
{
uint8_t v___x_95563__boxed_2683_; uint8_t v___x_95565__boxed_2684_; uint8_t v_useReducible_boxed_2685_; uint8_t v___x_95566__boxed_2686_; lean_object* v_res_2687_; 
v___x_95563__boxed_2683_ = lean_unbox(v___x_2655_);
v___x_95565__boxed_2684_ = lean_unbox(v___x_2657_);
v_useReducible_boxed_2685_ = lean_unbox(v_useReducible_2658_);
v___x_95566__boxed_2686_ = lean_unbox(v___x_2659_);
v_res_2687_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5(v_usingArg_2653_, v_snd_2654_, v___x_95563__boxed_2683_, v___x_2656_, v___x_95565__boxed_2684_, v_useReducible_boxed_2685_, v___x_95566__boxed_2686_, v___x_2660_, v___x_2661_, v_simprocs_2662_, v_discharge_x3f_2663_, v_snd_2664_, v___f_2665_, v___x_2666_, v___x_2667_, v___x_2668_, v___x_2669_, v___f_2670_, v_a_2671_, v___x_2672_, v___f_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2676_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec(v___x_2672_);
lean_dec(v___x_2660_);
return v_res_2687_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0(void){
_start:
{
lean_object* v___x_2688_; 
v___x_2688_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2688_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1(void){
_start:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; 
v___x_2689_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0);
v___x_2690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2689_);
return v___x_2690_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2(void){
_start:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; 
v___x_2691_ = lean_unsigned_to_nat(32u);
v___x_2692_ = lean_mk_empty_array_with_capacity(v___x_2691_);
v___x_2693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2692_);
return v___x_2693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6(lean_object* v___x_2694_, lean_object* v_tk_2695_, lean_object* v___x_2696_, lean_object* v___x_2697_, lean_object* v___x_2698_, lean_object* v_simprocs_2699_, uint8_t v___x_2700_, lean_object* v_usingArg_2701_, lean_object* v___x_2702_, uint8_t v___x_2703_, uint8_t v_useReducible_2704_, uint8_t v___x_2705_, lean_object* v___x_2706_, lean_object* v___f_2707_, lean_object* v___x_2708_, lean_object* v___x_2709_, lean_object* v___x_2710_, lean_object* v___f_2711_, lean_object* v_a_2712_, lean_object* v_usingTk_x3f_2713_, lean_object* v_discharge_x3f_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v___y_2725_; 
if (lean_obj_tag(v_usingTk_x3f_2713_) == 0)
{
lean_object* v___x_2839_; 
v___x_2839_ = lean_box(0);
v___y_2725_ = v___x_2839_;
goto v___jp_2724_;
}
else
{
lean_object* v_val_2840_; 
v_val_2840_ = lean_ctor_get(v_usingTk_x3f_2713_, 0);
lean_inc(v_val_2840_);
lean_dec_ref_known(v_usingTk_x3f_2713_, 1);
v___y_2725_ = v_val_2840_;
goto v___jp_2724_;
}
v___jp_2724_:
{
lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
v___x_2726_ = lean_mk_empty_array_with_capacity(v___x_2694_);
v___x_2727_ = lean_array_push(v___x_2726_, v_tk_2695_);
v___x_2728_ = lean_array_push(v___x_2727_, v___y_2725_);
v___x_2729_ = lean_box(2);
lean_inc(v___x_2696_);
v___x_2730_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2730_, 0, v___x_2729_);
lean_ctor_set(v___x_2730_, 1, v___x_2696_);
lean_ctor_set(v___x_2730_, 2, v___x_2728_);
v___x_2731_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_2730_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_object* v_a_2732_; lean_object* v___f_2733_; lean_object* v___x_2734_; 
v_a_2732_ = lean_ctor_get(v___x_2731_, 0);
lean_inc(v_a_2732_);
lean_dec_ref_known(v___x_2731_, 1);
v___f_2733_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___boxed), 11, 1);
lean_closure_set(v___f_2733_, 0, v_a_2732_);
v___x_2734_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2716_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v_a_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; size_t v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
lean_inc(v_a_2735_);
lean_dec_ref_known(v___x_2734_, 1);
v___x_2736_ = lean_mk_empty_array_with_capacity(v___x_2697_);
v___x_2737_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1);
lean_inc_n(v___x_2697_, 3);
v___x_2738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2737_);
lean_ctor_set(v___x_2738_, 1, v___x_2697_);
v___x_2739_ = lean_unsigned_to_nat(32u);
v___x_2740_ = lean_mk_empty_array_with_capacity(v___x_2739_);
v___x_2741_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2);
v___x_2742_ = ((size_t)5ULL);
v___x_2743_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2743_, 0, v___x_2741_);
lean_ctor_set(v___x_2743_, 1, v___x_2740_);
lean_ctor_set(v___x_2743_, 2, v___x_2697_);
lean_ctor_set(v___x_2743_, 3, v___x_2697_);
lean_ctor_set_usize(v___x_2743_, 4, v___x_2742_);
v___x_2744_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2737_);
lean_ctor_set(v___x_2744_, 1, v___x_2737_);
lean_ctor_set(v___x_2744_, 2, v___x_2737_);
lean_ctor_set(v___x_2744_, 3, v___x_2743_);
v___x_2745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2738_);
lean_ctor_set(v___x_2745_, 1, v___x_2744_);
lean_inc_ref(v___x_2745_);
lean_inc(v_discharge_x3f_2714_);
lean_inc_ref(v_simprocs_2699_);
lean_inc_ref(v___x_2698_);
v___x_2746_ = l_Lean_Meta_simpGoal(v_a_2735_, v___x_2698_, v_simprocs_2699_, v_discharge_x3f_2714_, v___x_2700_, v___x_2736_, v___x_2745_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_a_2747_; lean_object* v_fst_2748_; 
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
lean_inc(v_a_2747_);
lean_dec_ref_known(v___x_2746_, 1);
v_fst_2748_ = lean_ctor_get(v_a_2747_, 0);
if (lean_obj_tag(v_fst_2748_) == 1)
{
lean_object* v_val_2749_; lean_object* v_snd_2750_; lean_object* v_snd_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2774_; 
lean_dec_ref_known(v___x_2745_, 2);
v_val_2749_ = lean_ctor_get(v_fst_2748_, 0);
lean_inc(v_val_2749_);
v_snd_2750_ = lean_ctor_get(v_a_2747_, 1);
lean_inc(v_snd_2750_);
lean_dec(v_a_2747_);
v_snd_2751_ = lean_ctor_get(v_val_2749_, 1);
v_isSharedCheck_2774_ = !lean_is_exclusive(v_val_2749_);
if (v_isSharedCheck_2774_ == 0)
{
lean_object* v_unused_2775_; 
v_unused_2775_ = lean_ctor_get(v_val_2749_, 0);
lean_dec(v_unused_2775_);
v___x_2753_ = v_val_2749_;
v_isShared_2754_ = v_isSharedCheck_2774_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_snd_2751_);
lean_dec(v_val_2749_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2774_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___y_2759_; lean_object* v___x_2760_; lean_object* v___x_2762_; 
v___x_2755_ = lean_box(v___x_2700_);
v___x_2756_ = lean_box(v___x_2703_);
v___x_2757_ = lean_box(v_useReducible_2704_);
v___x_2758_ = lean_box(v___x_2705_);
lean_inc_n(v_snd_2751_, 2);
v___y_2759_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___boxed), 30, 21);
lean_closure_set(v___y_2759_, 0, v_usingArg_2701_);
lean_closure_set(v___y_2759_, 1, v_snd_2751_);
lean_closure_set(v___y_2759_, 2, v___x_2755_);
lean_closure_set(v___y_2759_, 3, v___x_2702_);
lean_closure_set(v___y_2759_, 4, v___x_2756_);
lean_closure_set(v___y_2759_, 5, v___x_2757_);
lean_closure_set(v___y_2759_, 6, v___x_2758_);
lean_closure_set(v___y_2759_, 7, v___x_2706_);
lean_closure_set(v___y_2759_, 8, v___x_2698_);
lean_closure_set(v___y_2759_, 9, v_simprocs_2699_);
lean_closure_set(v___y_2759_, 10, v_discharge_x3f_2714_);
lean_closure_set(v___y_2759_, 11, v_snd_2750_);
lean_closure_set(v___y_2759_, 12, v___f_2707_);
lean_closure_set(v___y_2759_, 13, v___x_2708_);
lean_closure_set(v___y_2759_, 14, v___x_2709_);
lean_closure_set(v___y_2759_, 15, v___x_2710_);
lean_closure_set(v___y_2759_, 16, v___x_2696_);
lean_closure_set(v___y_2759_, 17, v___f_2711_);
lean_closure_set(v___y_2759_, 18, v_a_2712_);
lean_closure_set(v___y_2759_, 19, v___x_2697_);
lean_closure_set(v___y_2759_, 20, v___f_2733_);
v___x_2760_ = lean_box(0);
if (v_isShared_2754_ == 0)
{
lean_ctor_set_tag(v___x_2753_, 1);
lean_ctor_set(v___x_2753_, 1, v___x_2760_);
lean_ctor_set(v___x_2753_, 0, v_snd_2751_);
v___x_2762_ = v___x_2753_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_snd_2751_);
lean_ctor_set(v_reuseFailAlloc_2773_, 1, v___x_2760_);
v___x_2762_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
lean_object* v___x_2763_; 
v___x_2763_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2762_, v___y_2716_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_object* v___x_2764_; 
lean_dec_ref_known(v___x_2763_, 1);
v___x_2764_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg(v_snd_2751_, v___y_2759_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
return v___x_2764_;
}
else
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2772_; 
lean_dec_ref(v___y_2759_);
lean_dec(v_snd_2751_);
v_a_2765_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2767_ = v___x_2763_;
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2763_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2770_; 
if (v_isShared_2768_ == 0)
{
v___x_2770_ = v___x_2767_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_a_2765_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
return v___x_2770_;
}
}
}
}
}
}
else
{
lean_object* v___x_2776_; lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2814_; 
lean_dec(v_a_2747_);
lean_dec_ref(v___f_2733_);
lean_dec(v_discharge_x3f_2714_);
lean_dec_ref(v___x_2710_);
lean_dec_ref(v___x_2709_);
lean_dec_ref(v___x_2708_);
lean_dec_ref(v___f_2707_);
lean_dec(v___x_2706_);
lean_dec_ref(v___x_2702_);
lean_dec(v_usingArg_2701_);
lean_dec_ref(v_simprocs_2699_);
lean_dec_ref(v___x_2698_);
lean_dec(v___x_2697_);
lean_dec(v___x_2696_);
v___x_2776_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2779_ = v___x_2776_;
v_isShared_2780_ = v_isSharedCheck_2814_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2776_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2814_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
uint8_t v___x_2781_; 
v___x_2781_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_a_2777_);
lean_dec(v_a_2777_);
if (v___x_2781_ == 0)
{
lean_object* v___x_2783_; 
lean_dec_ref(v_a_2712_);
lean_dec_ref(v___f_2711_);
if (v_isShared_2780_ == 0)
{
lean_ctor_set(v___x_2779_, 0, v___x_2745_);
v___x_2783_ = v___x_2779_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v___x_2745_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
else
{
lean_object* v_ref_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
lean_del_object(v___x_2779_);
v_ref_2785_ = lean_ctor_get(v___y_2721_, 2);
v___x_2786_ = lean_box(0);
lean_inc(v___y_2722_);
lean_inc_ref(v___y_2721_);
lean_inc(v___y_2720_);
lean_inc_ref(v___y_2719_);
lean_inc(v___y_2718_);
lean_inc_ref(v___y_2717_);
lean_inc(v___y_2716_);
lean_inc_ref(v___y_2715_);
v___x_2787_ = lean_apply_10(v___f_2711_, v___x_2786_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, lean_box(0));
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_object* v_a_2788_; lean_object* v___x_2789_; 
v_a_2788_ = lean_ctor_get(v___x_2787_, 0);
lean_inc(v_a_2788_);
lean_dec_ref_known(v___x_2787_, 1);
lean_inc(v_ref_2785_);
v___x_2789_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa(v_a_2712_, v_ref_2785_, v_a_2788_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2796_; 
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2796_ == 0)
{
lean_object* v_unused_2797_; 
v_unused_2797_ = lean_ctor_get(v___x_2789_, 0);
lean_dec(v_unused_2797_);
v___x_2791_ = v___x_2789_;
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
else
{
lean_dec(v___x_2789_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2794_; 
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 0, v___x_2745_);
v___x_2794_ = v___x_2791_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v___x_2745_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
}
else
{
lean_object* v_a_2798_; lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2805_; 
lean_dec_ref_known(v___x_2745_, 2);
v_a_2798_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2800_ = v___x_2789_;
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
else
{
lean_inc(v_a_2798_);
lean_dec(v___x_2789_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
lean_object* v___x_2803_; 
if (v_isShared_2801_ == 0)
{
v___x_2803_ = v___x_2800_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v_a_2798_);
v___x_2803_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
return v___x_2803_;
}
}
}
}
else
{
lean_object* v_a_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2813_; 
lean_dec_ref_known(v___x_2745_, 2);
lean_dec_ref(v_a_2712_);
v_a_2806_ = lean_ctor_get(v___x_2787_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2808_ = v___x_2787_;
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_a_2806_);
lean_dec(v___x_2787_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2811_; 
if (v_isShared_2809_ == 0)
{
v___x_2811_ = v___x_2808_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_a_2806_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2822_; 
lean_dec_ref_known(v___x_2745_, 2);
lean_dec_ref(v___f_2733_);
lean_dec(v_discharge_x3f_2714_);
lean_dec_ref(v_a_2712_);
lean_dec_ref(v___f_2711_);
lean_dec_ref(v___x_2710_);
lean_dec_ref(v___x_2709_);
lean_dec_ref(v___x_2708_);
lean_dec_ref(v___f_2707_);
lean_dec(v___x_2706_);
lean_dec_ref(v___x_2702_);
lean_dec(v_usingArg_2701_);
lean_dec_ref(v_simprocs_2699_);
lean_dec_ref(v___x_2698_);
lean_dec(v___x_2697_);
lean_dec(v___x_2696_);
v_a_2815_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2817_ = v___x_2746_;
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2746_);
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
else
{
lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2830_; 
lean_dec_ref(v___f_2733_);
lean_dec(v_discharge_x3f_2714_);
lean_dec_ref(v_a_2712_);
lean_dec_ref(v___f_2711_);
lean_dec_ref(v___x_2710_);
lean_dec_ref(v___x_2709_);
lean_dec_ref(v___x_2708_);
lean_dec_ref(v___f_2707_);
lean_dec(v___x_2706_);
lean_dec_ref(v___x_2702_);
lean_dec(v_usingArg_2701_);
lean_dec_ref(v_simprocs_2699_);
lean_dec_ref(v___x_2698_);
lean_dec(v___x_2697_);
lean_dec(v___x_2696_);
v_a_2823_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2825_ = v___x_2734_;
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v___x_2734_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2828_; 
if (v_isShared_2826_ == 0)
{
v___x_2828_ = v___x_2825_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_a_2823_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
}
}
else
{
lean_object* v_a_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2838_; 
lean_dec(v_discharge_x3f_2714_);
lean_dec_ref(v_a_2712_);
lean_dec_ref(v___f_2711_);
lean_dec_ref(v___x_2710_);
lean_dec_ref(v___x_2709_);
lean_dec_ref(v___x_2708_);
lean_dec_ref(v___f_2707_);
lean_dec(v___x_2706_);
lean_dec_ref(v___x_2702_);
lean_dec(v_usingArg_2701_);
lean_dec_ref(v_simprocs_2699_);
lean_dec_ref(v___x_2698_);
lean_dec(v___x_2697_);
lean_dec(v___x_2696_);
v_a_2831_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2833_ = v___x_2731_;
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_a_2831_);
lean_dec(v___x_2731_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2836_; 
if (v_isShared_2834_ == 0)
{
v___x_2836_ = v___x_2833_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_a_2831_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
return v___x_2836_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___boxed(lean_object** _args){
lean_object* v___x_2841_ = _args[0];
lean_object* v_tk_2842_ = _args[1];
lean_object* v___x_2843_ = _args[2];
lean_object* v___x_2844_ = _args[3];
lean_object* v___x_2845_ = _args[4];
lean_object* v_simprocs_2846_ = _args[5];
lean_object* v___x_2847_ = _args[6];
lean_object* v_usingArg_2848_ = _args[7];
lean_object* v___x_2849_ = _args[8];
lean_object* v___x_2850_ = _args[9];
lean_object* v_useReducible_2851_ = _args[10];
lean_object* v___x_2852_ = _args[11];
lean_object* v___x_2853_ = _args[12];
lean_object* v___f_2854_ = _args[13];
lean_object* v___x_2855_ = _args[14];
lean_object* v___x_2856_ = _args[15];
lean_object* v___x_2857_ = _args[16];
lean_object* v___f_2858_ = _args[17];
lean_object* v_a_2859_ = _args[18];
lean_object* v_usingTk_x3f_2860_ = _args[19];
lean_object* v_discharge_x3f_2861_ = _args[20];
lean_object* v___y_2862_ = _args[21];
lean_object* v___y_2863_ = _args[22];
lean_object* v___y_2864_ = _args[23];
lean_object* v___y_2865_ = _args[24];
lean_object* v___y_2866_ = _args[25];
lean_object* v___y_2867_ = _args[26];
lean_object* v___y_2868_ = _args[27];
lean_object* v___y_2869_ = _args[28];
lean_object* v___y_2870_ = _args[29];
_start:
{
uint8_t v___x_96356__boxed_2871_; uint8_t v___x_96358__boxed_2872_; uint8_t v_useReducible_boxed_2873_; uint8_t v___x_96359__boxed_2874_; lean_object* v_res_2875_; 
v___x_96356__boxed_2871_ = lean_unbox(v___x_2847_);
v___x_96358__boxed_2872_ = lean_unbox(v___x_2850_);
v_useReducible_boxed_2873_ = lean_unbox(v_useReducible_2851_);
v___x_96359__boxed_2874_ = lean_unbox(v___x_2852_);
v_res_2875_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6(v___x_2841_, v_tk_2842_, v___x_2843_, v___x_2844_, v___x_2845_, v_simprocs_2846_, v___x_96356__boxed_2871_, v_usingArg_2848_, v___x_2849_, v___x_96358__boxed_2872_, v_useReducible_boxed_2873_, v___x_96359__boxed_2874_, v___x_2853_, v___f_2854_, v___x_2855_, v___x_2856_, v___x_2857_, v___f_2858_, v_a_2859_, v_usingTk_x3f_2860_, v_discharge_x3f_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec_ref(v___y_2862_);
lean_dec(v___x_2841_);
return v_res_2875_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__4(void){
_start:
{
lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2880_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__3));
v___x_2881_ = lean_unsigned_to_nat(38u);
v___x_2882_ = lean_unsigned_to_nat(159u);
v___x_2883_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__2));
v___x_2884_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__1));
v___x_2885_ = l_mkPanicMessageWithDecl(v___x_2884_, v___x_2883_, v___x_2882_, v___x_2881_, v___x_2880_);
return v___x_2885_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12(void){
_start:
{
lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2893_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__3));
v___x_2894_ = lean_unsigned_to_nat(15u);
v___x_2895_ = lean_unsigned_to_nat(160u);
v___x_2896_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__2));
v___x_2897_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__1));
v___x_2898_ = l_mkPanicMessageWithDecl(v___x_2897_, v___x_2896_, v___x_2895_, v___x_2894_, v___x_2893_);
return v___x_2898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7(lean_object* v_tk_2900_, lean_object* v___x_2901_, lean_object* v___x_2902_, lean_object* v___x_2903_, lean_object* v___x_2904_, uint8_t v___x_2905_, lean_object* v___x_2906_, lean_object* v___x_2907_, uint8_t v_useReducible_2908_, lean_object* v___f_2909_, lean_object* v___x_2910_, lean_object* v___x_2911_, lean_object* v___x_2912_, lean_object* v___x_2913_, lean_object* v___x_2914_, lean_object* v___x_2915_, lean_object* v_usingArg_2916_, lean_object* v___x_2917_, uint8_t v___x_2918_, lean_object* v___f_2919_, lean_object* v_usingTk_x3f_2920_, lean_object* v_squeeze_2921_, lean_object* v_unfold_2922_, lean_object* v_args_2923_, lean_object* v_only_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_){
_start:
{
lean_object* v___y_2936_; lean_object* v___y_2940_; lean_object* v_stx_2941_; lean_object* v___y_2942_; lean_object* v_ref_2943_; lean_object* v___y_2944_; lean_object* v___y_2963_; lean_object* v_stx_2964_; lean_object* v___y_2965_; lean_object* v___y_2966_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v___y_2972_; lean_object* v___y_2973_; lean_object* v___y_2974_; lean_object* v___y_2975_; lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v___x_2989_; 
v___x_2989_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_2927_, v___y_2929_, v___y_2931_, v___y_2933_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v_a_2990_; lean_object* v_toCold_2991_; lean_object* v_ref_2992_; uint8_t v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; uint8_t v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3405_; uint8_t v___y_3406_; lean_object* v___y_3407_; lean_object* v_args_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; uint8_t v___y_3446_; lean_object* v___y_3447_; lean_object* v_only_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3476_; uint8_t v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3536_; lean_object* v___y_3537_; uint8_t v___y_3538_; lean_object* v___y_3549_; uint8_t v___y_3550_; lean_object* v___y_3551_; uint8_t v___y_3552_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v___y_3556_; uint8_t v___y_3557_; lean_object* v___y_3558_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3613_; lean_object* v___y_3614_; lean_object* v___y_3627_; 
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
lean_inc(v_a_2990_);
lean_dec_ref_known(v___x_2989_, 1);
v_toCold_2991_ = lean_ctor_get(v___y_2932_, 0);
v_ref_2992_ = lean_ctor_get(v___y_2932_, 2);
v___x_2993_ = 0;
v___x_2994_ = l_Lean_SourceInfo_fromRef(v_ref_2992_, v___x_2993_);
v___x_2995_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__3));
lean_inc_ref(v___x_2903_);
lean_inc_ref(v___x_2902_);
lean_inc_ref(v___x_2901_);
v___x_2996_ = l_Lean_Name_mkStr4(v___x_2901_, v___x_2902_, v___x_2903_, v___x_2995_);
lean_inc(v___x_2994_);
v___x_2997_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2994_);
lean_ctor_set(v___x_2997_, 1, v___x_2995_);
v___x_2998_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_2999_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6);
if (lean_obj_tag(v___y_2925_) == 0)
{
lean_object* v___x_3636_; 
v___x_3636_ = lean_mk_empty_array_with_capacity(v___x_2904_);
v___y_3627_ = v___x_3636_;
goto v___jp_3626_;
}
else
{
lean_object* v_val_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; 
v_val_3637_ = lean_ctor_get(v___y_2925_, 0);
lean_inc(v_val_3637_);
lean_dec_ref_known(v___y_2925_, 1);
v___x_3638_ = lean_mk_empty_array_with_capacity(v___x_2904_);
v___x_3639_ = lean_array_push(v___x_3638_, v_val_3637_);
v___y_3627_ = v___x_3639_;
goto v___jp_3626_;
}
v___jp_3000_:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3012_ = l_Array_append___redArg(v___x_2999_, v___y_3011_);
lean_dec_ref(v___y_3011_);
lean_inc_n(v___y_3002_, 2);
v___x_3013_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3013_, 0, v___y_3002_);
lean_ctor_set(v___x_3013_, 1, v___x_2998_);
lean_ctor_set(v___x_3013_, 2, v___x_3012_);
v___x_3014_ = l_Lean_Syntax_node5(v___y_3002_, v___x_2906_, v___y_3007_, v___y_3005_, v___y_3009_, v___y_3006_, v___x_3013_);
v___x_3015_ = l_Lean_Syntax_node2(v___y_3002_, v___y_3001_, v___y_3008_, v___x_3014_);
v___y_2963_ = v___y_3003_;
v_stx_2964_ = v___x_3015_;
v___y_2965_ = v___y_3004_;
v___y_2966_ = v___y_3010_;
goto v___jp_2962_;
}
v___jp_3016_:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3028_ = l_Array_append___redArg(v___x_2999_, v___y_3027_);
lean_dec_ref(v___y_3027_);
lean_inc(v___y_3018_);
v___x_3029_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3029_, 0, v___y_3018_);
lean_ctor_set(v___x_3029_, 1, v___x_2998_);
lean_ctor_set(v___x_3029_, 2, v___x_3028_);
if (lean_obj_tag(v___y_3020_) == 1)
{
lean_object* v_val_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
lean_dec(v___x_2904_);
v_val_3030_ = lean_ctor_get(v___y_3020_, 0);
lean_inc(v_val_3030_);
lean_dec_ref_known(v___y_3020_, 1);
v___x_3031_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__5));
lean_inc(v___y_3018_);
v___x_3032_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3032_, 0, v___y_3018_);
lean_ctor_set(v___x_3032_, 1, v___x_3031_);
v___x_3033_ = l_Array_mkArray2___redArg(v___x_3032_, v_val_3030_);
v___y_3001_ = v___y_3017_;
v___y_3002_ = v___y_3018_;
v___y_3003_ = v___y_3019_;
v___y_3004_ = v___y_3021_;
v___y_3005_ = v___y_3022_;
v___y_3006_ = v___x_3029_;
v___y_3007_ = v___y_3023_;
v___y_3008_ = v___y_3024_;
v___y_3009_ = v___y_3025_;
v___y_3010_ = v___y_3026_;
v___y_3011_ = v___x_3033_;
goto v___jp_3000_;
}
else
{
lean_object* v___x_3034_; 
lean_dec(v___y_3020_);
v___x_3034_ = lean_mk_empty_array_with_capacity(v___x_2904_);
lean_dec(v___x_2904_);
v___y_3001_ = v___y_3017_;
v___y_3002_ = v___y_3018_;
v___y_3003_ = v___y_3019_;
v___y_3004_ = v___y_3021_;
v___y_3005_ = v___y_3022_;
v___y_3006_ = v___x_3029_;
v___y_3007_ = v___y_3023_;
v___y_3008_ = v___y_3024_;
v___y_3009_ = v___y_3025_;
v___y_3010_ = v___y_3026_;
v___y_3011_ = v___x_3034_;
goto v___jp_3000_;
}
}
v___jp_3035_:
{
lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3047_ = l_Array_append___redArg(v___x_2999_, v___y_3046_);
lean_dec_ref(v___y_3046_);
lean_inc(v___y_3037_);
v___x_3048_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3048_, 0, v___y_3037_);
lean_ctor_set(v___x_3048_, 1, v___x_2998_);
lean_ctor_set(v___x_3048_, 2, v___x_3047_);
if (lean_obj_tag(v___y_3039_) == 1)
{
lean_object* v_val_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
v_val_3049_ = lean_ctor_get(v___y_3039_, 0);
lean_inc(v_val_3049_);
lean_dec_ref_known(v___y_3039_, 1);
v___x_3050_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_3051_ = l_Lean_Name_mkStr4(v___x_2901_, v___x_2902_, v___x_2903_, v___x_3050_);
v___x_3052_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_3037_, 4);
v___x_3053_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3053_, 0, v___y_3037_);
lean_ctor_set(v___x_3053_, 1, v___x_3052_);
v___x_3054_ = l_Array_append___redArg(v___x_2999_, v_val_3049_);
lean_dec(v_val_3049_);
v___x_3055_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3055_, 0, v___y_3037_);
lean_ctor_set(v___x_3055_, 1, v___x_2998_);
lean_ctor_set(v___x_3055_, 2, v___x_3054_);
v___x_3056_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_3057_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3057_, 0, v___y_3037_);
lean_ctor_set(v___x_3057_, 1, v___x_3056_);
v___x_3058_ = l_Lean_Syntax_node3(v___y_3037_, v___x_3051_, v___x_3053_, v___x_3055_, v___x_3057_);
v___x_3059_ = l_Array_mkArray1___redArg(v___x_3058_);
v___y_3017_ = v___y_3036_;
v___y_3018_ = v___y_3037_;
v___y_3019_ = v___y_3038_;
v___y_3020_ = v___y_3041_;
v___y_3021_ = v___y_3040_;
v___y_3022_ = v___y_3042_;
v___y_3023_ = v___y_3043_;
v___y_3024_ = v___y_3044_;
v___y_3025_ = v___x_3048_;
v___y_3026_ = v___y_3045_;
v___y_3027_ = v___x_3059_;
goto v___jp_3016_;
}
else
{
lean_object* v___x_3060_; 
lean_dec(v___y_3039_);
lean_dec_ref(v___x_2903_);
lean_dec_ref(v___x_2902_);
lean_dec_ref(v___x_2901_);
v___x_3060_ = lean_mk_empty_array_with_capacity(v___x_2904_);
v___y_3017_ = v___y_3036_;
v___y_3018_ = v___y_3037_;
v___y_3019_ = v___y_3038_;
v___y_3020_ = v___y_3041_;
v___y_3021_ = v___y_3040_;
v___y_3022_ = v___y_3042_;
v___y_3023_ = v___y_3043_;
v___y_3024_ = v___y_3044_;
v___y_3025_ = v___x_3048_;
v___y_3026_ = v___y_3045_;
v___y_3027_ = v___x_3060_;
goto v___jp_3016_;
}
}
v___jp_3061_:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3073_ = l_Array_append___redArg(v___x_2999_, v___y_3072_);
lean_dec_ref(v___y_3072_);
lean_inc(v___y_3063_);
v___x_3074_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3074_, 0, v___y_3063_);
lean_ctor_set(v___x_3074_, 1, v___x_2998_);
lean_ctor_set(v___x_3074_, 2, v___x_3073_);
if (lean_obj_tag(v___y_3070_) == 1)
{
lean_object* v_val_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v_val_3075_ = lean_ctor_get(v___y_3070_, 0);
lean_inc(v_val_3075_);
lean_dec_ref_known(v___y_3070_, 1);
v___x_3076_ = l_Lean_SourceInfo_fromRef(v_val_3075_, v___x_2905_);
lean_dec(v_val_3075_);
v___x_3077_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_3078_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3076_);
lean_ctor_set(v___x_3078_, 1, v___x_3077_);
v___x_3079_ = l_Array_mkArray1___redArg(v___x_3078_);
v___y_3036_ = v___y_3062_;
v___y_3037_ = v___y_3063_;
v___y_3038_ = v___y_3064_;
v___y_3039_ = v___y_3065_;
v___y_3040_ = v___y_3067_;
v___y_3041_ = v___y_3066_;
v___y_3042_ = v___x_3074_;
v___y_3043_ = v___y_3068_;
v___y_3044_ = v___y_3069_;
v___y_3045_ = v___y_3071_;
v___y_3046_ = v___x_3079_;
goto v___jp_3035_;
}
else
{
lean_object* v___x_3080_; 
lean_dec(v___y_3070_);
v___x_3080_ = lean_mk_empty_array_with_capacity(v___x_2904_);
v___y_3036_ = v___y_3062_;
v___y_3037_ = v___y_3063_;
v___y_3038_ = v___y_3064_;
v___y_3039_ = v___y_3065_;
v___y_3040_ = v___y_3067_;
v___y_3041_ = v___y_3066_;
v___y_3042_ = v___x_3074_;
v___y_3043_ = v___y_3068_;
v___y_3044_ = v___y_3069_;
v___y_3045_ = v___y_3071_;
v___y_3046_ = v___x_3080_;
goto v___jp_3035_;
}
}
v___jp_3081_:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; 
v___x_3096_ = l_Array_append___redArg(v___x_2999_, v___y_3095_);
lean_dec_ref(v___y_3095_);
lean_inc_n(v___y_3088_, 3);
v___x_3097_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3097_, 0, v___y_3088_);
lean_ctor_set(v___x_3097_, 1, v___x_2998_);
lean_ctor_set(v___x_3097_, 2, v___x_3096_);
v___x_3098_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__6));
v___x_3099_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3099_, 0, v___y_3088_);
lean_ctor_set(v___x_3099_, 1, v___x_3098_);
v___x_3100_ = l_Lean_Syntax_node6(v___y_3088_, v___y_3089_, v___y_3091_, v___y_3082_, v___y_3085_, v___x_3097_, v___x_3099_, v___y_3093_);
v___x_3101_ = l_Lean_Syntax_node4(v___y_3088_, v___y_3092_, v___y_3084_, v___y_3083_, v___y_3086_, v___x_3100_);
v___y_2963_ = v___y_3087_;
v_stx_2964_ = v___x_3101_;
v___y_2965_ = v___y_3090_;
v___y_2966_ = v___y_3094_;
goto v___jp_2962_;
}
v___jp_3102_:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3117_ = l_Array_append___redArg(v___x_2999_, v___y_3116_);
lean_dec_ref(v___y_3116_);
lean_inc(v___y_3108_);
v___x_3118_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3118_, 0, v___y_3108_);
lean_ctor_set(v___x_3118_, 1, v___x_2998_);
lean_ctor_set(v___x_3118_, 2, v___x_3117_);
if (lean_obj_tag(v___y_3104_) == 1)
{
lean_object* v_val_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; 
lean_dec(v___x_2904_);
v_val_3119_ = lean_ctor_get(v___y_3104_, 0);
lean_inc(v_val_3119_);
lean_dec_ref_known(v___y_3104_, 1);
v___x_3120_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_3121_ = l_Lean_Name_mkStr4(v___x_2901_, v___x_2902_, v___x_2903_, v___x_3120_);
v___x_3122_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_3108_, 4);
v___x_3123_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3123_, 0, v___y_3108_);
lean_ctor_set(v___x_3123_, 1, v___x_3122_);
v___x_3124_ = l_Array_append___redArg(v___x_2999_, v_val_3119_);
lean_dec(v_val_3119_);
v___x_3125_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3125_, 0, v___y_3108_);
lean_ctor_set(v___x_3125_, 1, v___x_2998_);
lean_ctor_set(v___x_3125_, 2, v___x_3124_);
v___x_3126_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_3127_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3127_, 0, v___y_3108_);
lean_ctor_set(v___x_3127_, 1, v___x_3126_);
v___x_3128_ = l_Lean_Syntax_node3(v___y_3108_, v___x_3121_, v___x_3123_, v___x_3125_, v___x_3127_);
v___x_3129_ = l_Array_mkArray1___redArg(v___x_3128_);
v___y_3082_ = v___y_3103_;
v___y_3083_ = v___y_3105_;
v___y_3084_ = v___y_3106_;
v___y_3085_ = v___x_3118_;
v___y_3086_ = v___y_3107_;
v___y_3087_ = v___y_3109_;
v___y_3088_ = v___y_3108_;
v___y_3089_ = v___y_3110_;
v___y_3090_ = v___y_3111_;
v___y_3091_ = v___y_3112_;
v___y_3092_ = v___y_3113_;
v___y_3093_ = v___y_3114_;
v___y_3094_ = v___y_3115_;
v___y_3095_ = v___x_3129_;
goto v___jp_3081_;
}
else
{
lean_object* v___x_3130_; 
lean_dec(v___y_3104_);
lean_dec_ref(v___x_2903_);
lean_dec_ref(v___x_2902_);
lean_dec_ref(v___x_2901_);
v___x_3130_ = lean_mk_empty_array_with_capacity(v___x_2904_);
lean_dec(v___x_2904_);
v___y_3082_ = v___y_3103_;
v___y_3083_ = v___y_3105_;
v___y_3084_ = v___y_3106_;
v___y_3085_ = v___x_3118_;
v___y_3086_ = v___y_3107_;
v___y_3087_ = v___y_3109_;
v___y_3088_ = v___y_3108_;
v___y_3089_ = v___y_3110_;
v___y_3090_ = v___y_3111_;
v___y_3091_ = v___y_3112_;
v___y_3092_ = v___y_3113_;
v___y_3093_ = v___y_3114_;
v___y_3094_ = v___y_3115_;
v___y_3095_ = v___x_3130_;
goto v___jp_3081_;
}
}
v___jp_3131_:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3146_ = l_Array_append___redArg(v___x_2999_, v___y_3145_);
lean_dec_ref(v___y_3145_);
lean_inc(v___y_3137_);
v___x_3147_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3147_, 0, v___y_3137_);
lean_ctor_set(v___x_3147_, 1, v___x_2998_);
lean_ctor_set(v___x_3147_, 2, v___x_3146_);
if (lean_obj_tag(v___y_3135_) == 1)
{
lean_object* v_val_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; 
v_val_3148_ = lean_ctor_get(v___y_3135_, 0);
lean_inc(v_val_3148_);
lean_dec_ref_known(v___y_3135_, 1);
v___x_3149_ = l_Lean_SourceInfo_fromRef(v_val_3148_, v___x_2905_);
lean_dec(v_val_3148_);
v___x_3150_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_3151_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3151_, 0, v___x_3149_);
lean_ctor_set(v___x_3151_, 1, v___x_3150_);
v___x_3152_ = l_Array_mkArray1___redArg(v___x_3151_);
v___y_3103_ = v___x_3147_;
v___y_3104_ = v___y_3132_;
v___y_3105_ = v___y_3133_;
v___y_3106_ = v___y_3134_;
v___y_3107_ = v___y_3136_;
v___y_3108_ = v___y_3137_;
v___y_3109_ = v___y_3138_;
v___y_3110_ = v___y_3139_;
v___y_3111_ = v___y_3140_;
v___y_3112_ = v___y_3141_;
v___y_3113_ = v___y_3142_;
v___y_3114_ = v___y_3143_;
v___y_3115_ = v___y_3144_;
v___y_3116_ = v___x_3152_;
goto v___jp_3102_;
}
else
{
lean_object* v___x_3153_; 
lean_dec(v___y_3135_);
v___x_3153_ = lean_mk_empty_array_with_capacity(v___x_2904_);
v___y_3103_ = v___x_3147_;
v___y_3104_ = v___y_3132_;
v___y_3105_ = v___y_3133_;
v___y_3106_ = v___y_3134_;
v___y_3107_ = v___y_3136_;
v___y_3108_ = v___y_3137_;
v___y_3109_ = v___y_3138_;
v___y_3110_ = v___y_3139_;
v___y_3111_ = v___y_3140_;
v___y_3112_ = v___y_3141_;
v___y_3113_ = v___y_3142_;
v___y_3114_ = v___y_3143_;
v___y_3115_ = v___y_3144_;
v___y_3116_ = v___x_3153_;
goto v___jp_3102_;
}
}
v___jp_3154_:
{
lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3166_ = l_Array_append___redArg(v___x_2999_, v___y_3165_);
lean_dec_ref(v___y_3165_);
lean_inc_n(v___y_3163_, 2);
v___x_3167_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3167_, 0, v___y_3163_);
lean_ctor_set(v___x_3167_, 1, v___x_2998_);
lean_ctor_set(v___x_3167_, 2, v___x_3166_);
v___x_3168_ = l_Lean_Syntax_node5(v___y_3163_, v___x_2906_, v___y_3161_, v___y_3157_, v___y_3155_, v___y_3160_, v___x_3167_);
lean_inc(v___y_3159_);
v___x_3169_ = l_Lean_Syntax_node4(v___y_3163_, v___x_2907_, v___y_3162_, v___y_3159_, v___y_3159_, v___x_3168_);
v___y_2963_ = v___y_3156_;
v_stx_2964_ = v___x_3169_;
v___y_2965_ = v___y_3158_;
v___y_2966_ = v___y_3164_;
goto v___jp_2962_;
}
v___jp_3170_:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3182_ = l_Array_append___redArg(v___x_2999_, v___y_3181_);
lean_dec_ref(v___y_3181_);
lean_inc(v___y_3179_);
v___x_3183_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3183_, 0, v___y_3179_);
lean_ctor_set(v___x_3183_, 1, v___x_2998_);
lean_ctor_set(v___x_3183_, 2, v___x_3182_);
if (lean_obj_tag(v___y_3174_) == 1)
{
lean_object* v_val_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
lean_dec(v___x_2904_);
v_val_3184_ = lean_ctor_get(v___y_3174_, 0);
lean_inc(v_val_3184_);
lean_dec_ref_known(v___y_3174_, 1);
v___x_3185_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__5));
lean_inc(v___y_3179_);
v___x_3186_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3186_, 0, v___y_3179_);
lean_ctor_set(v___x_3186_, 1, v___x_3185_);
v___x_3187_ = l_Array_mkArray2___redArg(v___x_3186_, v_val_3184_);
v___y_3155_ = v___y_3171_;
v___y_3156_ = v___y_3173_;
v___y_3157_ = v___y_3172_;
v___y_3158_ = v___y_3175_;
v___y_3159_ = v___y_3176_;
v___y_3160_ = v___x_3183_;
v___y_3161_ = v___y_3177_;
v___y_3162_ = v___y_3178_;
v___y_3163_ = v___y_3179_;
v___y_3164_ = v___y_3180_;
v___y_3165_ = v___x_3187_;
goto v___jp_3154_;
}
else
{
lean_object* v___x_3188_; 
lean_dec(v___y_3174_);
v___x_3188_ = lean_mk_empty_array_with_capacity(v___x_2904_);
lean_dec(v___x_2904_);
v___y_3155_ = v___y_3171_;
v___y_3156_ = v___y_3173_;
v___y_3157_ = v___y_3172_;
v___y_3158_ = v___y_3175_;
v___y_3159_ = v___y_3176_;
v___y_3160_ = v___x_3183_;
v___y_3161_ = v___y_3177_;
v___y_3162_ = v___y_3178_;
v___y_3163_ = v___y_3179_;
v___y_3164_ = v___y_3180_;
v___y_3165_ = v___x_3188_;
goto v___jp_3154_;
}
}
v___jp_3189_:
{
lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___x_3201_ = l_Array_append___redArg(v___x_2999_, v___y_3200_);
lean_dec_ref(v___y_3200_);
lean_inc(v___y_3198_);
v___x_3202_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3202_, 0, v___y_3198_);
lean_ctor_set(v___x_3202_, 1, v___x_2998_);
lean_ctor_set(v___x_3202_, 2, v___x_3201_);
if (lean_obj_tag(v___y_3192_) == 1)
{
lean_object* v_val_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
v_val_3203_ = lean_ctor_get(v___y_3192_, 0);
lean_inc(v_val_3203_);
lean_dec_ref_known(v___y_3192_, 1);
v___x_3204_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_3205_ = l_Lean_Name_mkStr4(v___x_2901_, v___x_2902_, v___x_2903_, v___x_3204_);
v___x_3206_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_3198_, 4);
v___x_3207_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3207_, 0, v___y_3198_);
lean_ctor_set(v___x_3207_, 1, v___x_3206_);
v___x_3208_ = l_Array_append___redArg(v___x_2999_, v_val_3203_);
lean_dec(v_val_3203_);
v___x_3209_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3209_, 0, v___y_3198_);
lean_ctor_set(v___x_3209_, 1, v___x_2998_);
lean_ctor_set(v___x_3209_, 2, v___x_3208_);
v___x_3210_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_3211_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3211_, 0, v___y_3198_);
lean_ctor_set(v___x_3211_, 1, v___x_3210_);
v___x_3212_ = l_Lean_Syntax_node3(v___y_3198_, v___x_3205_, v___x_3207_, v___x_3209_, v___x_3211_);
v___x_3213_ = l_Array_mkArray1___redArg(v___x_3212_);
v___y_3171_ = v___x_3202_;
v___y_3172_ = v___y_3191_;
v___y_3173_ = v___y_3190_;
v___y_3174_ = v___y_3194_;
v___y_3175_ = v___y_3193_;
v___y_3176_ = v___y_3195_;
v___y_3177_ = v___y_3196_;
v___y_3178_ = v___y_3197_;
v___y_3179_ = v___y_3198_;
v___y_3180_ = v___y_3199_;
v___y_3181_ = v___x_3213_;
goto v___jp_3170_;
}
else
{
lean_object* v___x_3214_; 
lean_dec(v___y_3192_);
lean_dec_ref(v___x_2903_);
lean_dec_ref(v___x_2902_);
lean_dec_ref(v___x_2901_);
v___x_3214_ = lean_mk_empty_array_with_capacity(v___x_2904_);
v___y_3171_ = v___x_3202_;
v___y_3172_ = v___y_3191_;
v___y_3173_ = v___y_3190_;
v___y_3174_ = v___y_3194_;
v___y_3175_ = v___y_3193_;
v___y_3176_ = v___y_3195_;
v___y_3177_ = v___y_3196_;
v___y_3178_ = v___y_3197_;
v___y_3179_ = v___y_3198_;
v___y_3180_ = v___y_3199_;
v___y_3181_ = v___x_3214_;
goto v___jp_3170_;
}
}
v___jp_3215_:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3227_ = l_Array_append___redArg(v___x_2999_, v___y_3226_);
lean_dec_ref(v___y_3226_);
lean_inc(v___y_3224_);
v___x_3228_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3228_, 0, v___y_3224_);
lean_ctor_set(v___x_3228_, 1, v___x_2998_);
lean_ctor_set(v___x_3228_, 2, v___x_3227_);
if (lean_obj_tag(v___y_3222_) == 1)
{
lean_object* v_val_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; 
v_val_3229_ = lean_ctor_get(v___y_3222_, 0);
lean_inc(v_val_3229_);
lean_dec_ref_known(v___y_3222_, 1);
v___x_3230_ = l_Lean_SourceInfo_fromRef(v_val_3229_, v___x_2905_);
lean_dec(v_val_3229_);
v___x_3231_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_3232_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3230_);
lean_ctor_set(v___x_3232_, 1, v___x_3231_);
v___x_3233_ = l_Array_mkArray1___redArg(v___x_3232_);
v___y_3190_ = v___y_3216_;
v___y_3191_ = v___x_3228_;
v___y_3192_ = v___y_3217_;
v___y_3193_ = v___y_3219_;
v___y_3194_ = v___y_3218_;
v___y_3195_ = v___y_3220_;
v___y_3196_ = v___y_3221_;
v___y_3197_ = v___y_3223_;
v___y_3198_ = v___y_3224_;
v___y_3199_ = v___y_3225_;
v___y_3200_ = v___x_3233_;
goto v___jp_3189_;
}
else
{
lean_object* v___x_3234_; 
lean_dec(v___y_3222_);
v___x_3234_ = lean_mk_empty_array_with_capacity(v___x_2904_);
v___y_3190_ = v___y_3216_;
v___y_3191_ = v___x_3228_;
v___y_3192_ = v___y_3217_;
v___y_3193_ = v___y_3219_;
v___y_3194_ = v___y_3218_;
v___y_3195_ = v___y_3220_;
v___y_3196_ = v___y_3221_;
v___y_3197_ = v___y_3223_;
v___y_3198_ = v___y_3224_;
v___y_3199_ = v___y_3225_;
v___y_3200_ = v___x_3234_;
goto v___jp_3189_;
}
}
v___jp_3235_:
{
lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; 
v___x_3249_ = l_Array_append___redArg(v___x_2999_, v___y_3248_);
lean_dec_ref(v___y_3248_);
lean_inc_n(v___y_3236_, 3);
v___x_3250_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3250_, 0, v___y_3236_);
lean_ctor_set(v___x_3250_, 1, v___x_2998_);
lean_ctor_set(v___x_3250_, 2, v___x_3249_);
v___x_3251_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__6));
v___x_3252_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3252_, 0, v___y_3236_);
lean_ctor_set(v___x_3252_, 1, v___x_3251_);
v___x_3253_ = l_Lean_Syntax_node6(v___y_3236_, v___y_3238_, v___y_3244_, v___y_3245_, v___y_3242_, v___x_3250_, v___x_3252_, v___y_3246_);
lean_inc(v___y_3237_);
v___x_3254_ = l_Lean_Syntax_node4(v___y_3236_, v___y_3239_, v___y_3240_, v___y_3237_, v___y_3237_, v___x_3253_);
v___y_2963_ = v___y_3241_;
v_stx_2964_ = v___x_3254_;
v___y_2965_ = v___y_3243_;
v___y_2966_ = v___y_3247_;
goto v___jp_2962_;
}
v___jp_3255_:
{
lean_object* v___x_3269_; lean_object* v___x_3270_; 
v___x_3269_ = l_Array_append___redArg(v___x_2999_, v___y_3268_);
lean_dec_ref(v___y_3268_);
lean_inc(v___y_3256_);
v___x_3270_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3270_, 0, v___y_3256_);
lean_ctor_set(v___x_3270_, 1, v___x_2998_);
lean_ctor_set(v___x_3270_, 2, v___x_3269_);
if (lean_obj_tag(v___y_3257_) == 1)
{
lean_object* v_val_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; 
lean_dec(v___x_2904_);
v_val_3271_ = lean_ctor_get(v___y_3257_, 0);
lean_inc(v_val_3271_);
lean_dec_ref_known(v___y_3257_, 1);
v___x_3272_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_3273_ = l_Lean_Name_mkStr4(v___x_2901_, v___x_2902_, v___x_2903_, v___x_3272_);
v___x_3274_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_3256_, 4);
v___x_3275_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3275_, 0, v___y_3256_);
lean_ctor_set(v___x_3275_, 1, v___x_3274_);
v___x_3276_ = l_Array_append___redArg(v___x_2999_, v_val_3271_);
lean_dec(v_val_3271_);
v___x_3277_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3277_, 0, v___y_3256_);
lean_ctor_set(v___x_3277_, 1, v___x_2998_);
lean_ctor_set(v___x_3277_, 2, v___x_3276_);
v___x_3278_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_3279_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3279_, 0, v___y_3256_);
lean_ctor_set(v___x_3279_, 1, v___x_3278_);
v___x_3280_ = l_Lean_Syntax_node3(v___y_3256_, v___x_3273_, v___x_3275_, v___x_3277_, v___x_3279_);
v___x_3281_ = l_Array_mkArray1___redArg(v___x_3280_);
v___y_3236_ = v___y_3256_;
v___y_3237_ = v___y_3258_;
v___y_3238_ = v___y_3259_;
v___y_3239_ = v___y_3260_;
v___y_3240_ = v___y_3261_;
v___y_3241_ = v___y_3262_;
v___y_3242_ = v___x_3270_;
v___y_3243_ = v___y_3263_;
v___y_3244_ = v___y_3264_;
v___y_3245_ = v___y_3265_;
v___y_3246_ = v___y_3266_;
v___y_3247_ = v___y_3267_;
v___y_3248_ = v___x_3281_;
goto v___jp_3235_;
}
else
{
lean_object* v___x_3282_; 
lean_dec(v___y_3257_);
lean_dec_ref(v___x_2903_);
lean_dec_ref(v___x_2902_);
lean_dec_ref(v___x_2901_);
v___x_3282_ = lean_mk_empty_array_with_capacity(v___x_2904_);
lean_dec(v___x_2904_);
v___y_3236_ = v___y_3256_;
v___y_3237_ = v___y_3258_;
v___y_3238_ = v___y_3259_;
v___y_3239_ = v___y_3260_;
v___y_3240_ = v___y_3261_;
v___y_3241_ = v___y_3262_;
v___y_3242_ = v___x_3270_;
v___y_3243_ = v___y_3263_;
v___y_3244_ = v___y_3264_;
v___y_3245_ = v___y_3265_;
v___y_3246_ = v___y_3266_;
v___y_3247_ = v___y_3267_;
v___y_3248_ = v___x_3282_;
goto v___jp_3235_;
}
}
v___jp_3283_:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3297_ = l_Array_append___redArg(v___x_2999_, v___y_3296_);
lean_dec_ref(v___y_3296_);
lean_inc(v___y_3284_);
v___x_3298_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3298_, 0, v___y_3284_);
lean_ctor_set(v___x_3298_, 1, v___x_2998_);
lean_ctor_set(v___x_3298_, 2, v___x_3297_);
if (lean_obj_tag(v___y_3288_) == 1)
{
lean_object* v_val_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
v_val_3299_ = lean_ctor_get(v___y_3288_, 0);
lean_inc(v_val_3299_);
lean_dec_ref_known(v___y_3288_, 1);
v___x_3300_ = l_Lean_SourceInfo_fromRef(v_val_3299_, v___x_2905_);
lean_dec(v_val_3299_);
v___x_3301_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_3302_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3300_);
lean_ctor_set(v___x_3302_, 1, v___x_3301_);
v___x_3303_ = l_Array_mkArray1___redArg(v___x_3302_);
v___y_3256_ = v___y_3284_;
v___y_3257_ = v___y_3285_;
v___y_3258_ = v___y_3286_;
v___y_3259_ = v___y_3287_;
v___y_3260_ = v___y_3289_;
v___y_3261_ = v___y_3290_;
v___y_3262_ = v___y_3291_;
v___y_3263_ = v___y_3292_;
v___y_3264_ = v___y_3293_;
v___y_3265_ = v___x_3298_;
v___y_3266_ = v___y_3294_;
v___y_3267_ = v___y_3295_;
v___y_3268_ = v___x_3303_;
goto v___jp_3255_;
}
else
{
lean_object* v___x_3304_; 
lean_dec(v___y_3288_);
v___x_3304_ = lean_mk_empty_array_with_capacity(v___x_2904_);
v___y_3256_ = v___y_3284_;
v___y_3257_ = v___y_3285_;
v___y_3258_ = v___y_3286_;
v___y_3259_ = v___y_3287_;
v___y_3260_ = v___y_3289_;
v___y_3261_ = v___y_3290_;
v___y_3262_ = v___y_3291_;
v___y_3263_ = v___y_3292_;
v___y_3264_ = v___y_3293_;
v___y_3265_ = v___x_3298_;
v___y_3266_ = v___y_3294_;
v___y_3267_ = v___y_3295_;
v___y_3268_ = v___x_3304_;
goto v___jp_3255_;
}
}
v___jp_3305_:
{
if (v___y_3313_ == 0)
{
if (v_useReducible_2908_ == 0)
{
lean_dec(v___x_2907_);
lean_dec(v___x_2906_);
if (lean_obj_tag(v___y_3310_) == 0)
{
lean_dec(v___y_3320_);
lean_dec(v___y_3317_);
lean_dec(v___y_3312_);
lean_dec(v___y_3307_);
lean_dec_ref(v___x_2910_);
lean_dec_ref(v___f_2909_);
lean_dec(v___x_2904_);
lean_dec_ref(v___x_2903_);
lean_dec_ref(v___x_2902_);
lean_dec_ref(v___x_2901_);
v___y_2969_ = v___y_3314_;
v___y_2970_ = v___y_3306_;
v___y_2971_ = v___y_3311_;
v___y_2972_ = v___y_3318_;
v___y_2973_ = v___y_3316_;
v___y_2974_ = v___y_3309_;
v___y_2975_ = v___y_3308_;
v___y_2976_ = v___y_3315_;
v___y_2977_ = v___y_3319_;
goto v___jp_2968_;
}
else
{
lean_object* v_val_3321_; lean_object* v___x_3322_; 
v_val_3321_ = lean_ctor_get(v___y_3310_, 0);
lean_inc(v_val_3321_);
lean_dec_ref_known(v___y_3310_, 1);
lean_inc(v___y_3319_);
lean_inc_ref(v___y_3315_);
v___x_3322_ = lean_apply_9(v___f_2909_, v___y_3306_, v___y_3311_, v___y_3318_, v___y_3316_, v___y_3309_, v___y_3308_, v___y_3315_, v___y_3319_, lean_box(0));
if (lean_obj_tag(v___x_3322_) == 0)
{
lean_object* v_a_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; 
v_a_3323_ = lean_ctor_get(v___x_3322_, 0);
lean_inc_n(v_a_3323_, 3);
lean_dec_ref_known(v___x_3322_, 1);
v___x_3324_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__7));
lean_inc_ref_n(v___x_2903_, 2);
lean_inc_ref_n(v___x_2902_, 2);
lean_inc_ref_n(v___x_2901_, 2);
v___x_3325_ = l_Lean_Name_mkStr4(v___x_2901_, v___x_2902_, v___x_2903_, v___x_3324_);
v___x_3326_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3326_, 0, v_a_3323_);
lean_ctor_set(v___x_3326_, 1, v___x_2910_);
v___x_3327_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3327_, 0, v_a_3323_);
lean_ctor_set(v___x_3327_, 1, v___x_2998_);
lean_ctor_set(v___x_3327_, 2, v___x_2999_);
v___x_3328_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__8));
v___x_3329_ = l_Lean_Name_mkStr4(v___x_2901_, v___x_2902_, v___x_2903_, v___x_3328_);
if (lean_obj_tag(v___y_3320_) == 0)
{
lean_object* v___x_3330_; 
v___x_3330_ = lean_mk_empty_array_with_capacity(v___x_2904_);
v___y_3284_ = v_a_3323_;
v___y_3285_ = v___y_3307_;
v___y_3286_ = v___x_3327_;
v___y_3287_ = v___x_3329_;
v___y_3288_ = v___y_3312_;
v___y_3289_ = v___x_3325_;
v___y_3290_ = v___x_3326_;
v___y_3291_ = v___y_3314_;
v___y_3292_ = v___y_3315_;
v___y_3293_ = v___y_3317_;
v___y_3294_ = v_val_3321_;
v___y_3295_ = v___y_3319_;
v___y_3296_ = v___x_3330_;
goto v___jp_3283_;
}
else
{
lean_object* v_val_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
v_val_3331_ = lean_ctor_get(v___y_3320_, 0);
lean_inc(v_val_3331_);
lean_dec_ref_known(v___y_3320_, 1);
v___x_3332_ = lean_mk_empty_array_with_capacity(v___x_2904_);
v___x_3333_ = lean_array_push(v___x_3332_, v_val_3331_);
v___y_3284_ = v_a_3323_;
v___y_3285_ = v___y_3307_;
v___y_3286_ = v___x_3327_;
v___y_3287_ = v___x_3329_;
v___y_3288_ = v___y_3312_;
v___y_3289_ = v___x_3325_;
v___y_3290_ = v___x_3326_;
v___y_3291_ = v___y_3314_;
v___y_3292_ = v___y_3315_;
v___y_3293_ = v___y_3317_;
v___y_3294_ = v_val_3321_;
v___y_3295_ = v___y_3319_;
v___y_3296_ = v___x_3333_;
goto v___jp_3283_;
}
}
else
{
lean_object* v_a_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3341_; 
lean_dec(v_val_3321_);
lean_dec(v___y_3320_);
lean_dec(v___y_3319_);
lean_dec(v___y_3317_);
lean_dec_ref(v___y_3315_);
lean_dec_ref(v___y_3314_);
lean_dec(v___y_3312_);
lean_dec(v___y_3307_);
lean_dec_ref(v___x_2910_);
lean_dec(v___x_2904_);
lean_dec_ref(v___x_2903_);
lean_dec_ref(v___x_2902_);
lean_dec_ref(v___x_2901_);
lean_dec(v_tk_2900_);
v_a_3334_ = lean_ctor_get(v___x_3322_, 0);
v_isSharedCheck_3341_ = !lean_is_exclusive(v___x_3322_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3336_ = v___x_3322_;
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_a_3334_);
lean_dec(v___x_3322_);
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
lean_object* v___x_3342_; 
lean_inc(v___y_3319_);
lean_inc_ref(v___y_3315_);
v___x_3342_ = lean_apply_9(v___f_2909_, v___y_3306_, v___y_3311_, v___y_3318_, v___y_3316_, v___y_3309_, v___y_3308_, v___y_3315_, v___y_3319_, lean_box(0));
if (lean_obj_tag(v___x_3342_) == 0)
{
lean_object* v_a_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; 
v_a_3343_ = lean_ctor_get(v___x_3342_, 0);
lean_inc_n(v_a_3343_, 3);
lean_dec_ref_known(v___x_3342_, 1);
v___x_3344_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3344_, 0, v_a_3343_);
lean_ctor_set(v___x_3344_, 1, v___x_2910_);
v___x_3345_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3345_, 0, v_a_3343_);
lean_ctor_set(v___x_3345_, 1, v___x_2998_);
lean_ctor_set(v___x_3345_, 2, v___x_2999_);
if (lean_obj_tag(v___y_3320_) == 0)
{
lean_object* v___x_3346_; 
v___x_3346_ = lean_mk_empty_array_with_capacity(v___x_2904_);
v___y_3216_ = v___y_3314_;
v___y_3217_ = v___y_3307_;
v___y_3218_ = v___y_3310_;
v___y_3219_ = v___y_3315_;
v___y_3220_ = v___x_3345_;
v___y_3221_ = v___y_3317_;
v___y_3222_ = v___y_3312_;
v___y_3223_ = v___x_3344_;
v___y_3224_ = v_a_3343_;
v___y_3225_ = v___y_3319_;
v___y_3226_ = v___x_3346_;
goto v___jp_3215_;
}
else
{
lean_object* v_val_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; 
v_val_3347_ = lean_ctor_get(v___y_3320_, 0);
lean_inc(v_val_3347_);
lean_dec_ref_known(v___y_3320_, 1);
v___x_3348_ = lean_mk_empty_array_with_capacity(v___x_2904_);
v___x_3349_ = lean_array_push(v___x_3348_, v_val_3347_);
v___y_3216_ = v___y_3314_;
v___y_3217_ = v___y_3307_;
v___y_3218_ = v___y_3310_;
v___y_3219_ = v___y_3315_;
v___y_3220_ = v___x_3345_;
v___y_3221_ = v___y_3317_;
v___y_3222_ = v___y_3312_;
v___y_3223_ = v___x_3344_;
v___y_3224_ = v_a_3343_;
v___y_3225_ = v___y_3319_;
v___y_3226_ = v___x_3349_;
goto v___jp_3215_;
}
}
else
{
lean_object* v_a_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3357_; 
lean_dec(v___y_3320_);
lean_dec(v___y_3319_);
lean_dec(v___y_3317_);
lean_dec_ref(v___y_3315_);
lean_dec_ref(v___y_3314_);
lean_dec(v___y_3312_);
lean_dec(v___y_3310_);
lean_dec(v___y_3307_);
lean_dec_ref(v___x_2910_);
lean_dec(v___x_2907_);
lean_dec(v___x_2906_);
lean_dec(v___x_2904_);
lean_dec_ref(v___x_2903_);
lean_dec_ref(v___x_2902_);
lean_dec_ref(v___x_2901_);
lean_dec(v_tk_2900_);
v_a_3350_ = lean_ctor_get(v___x_3342_, 0);
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3352_ = v___x_3342_;
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_a_3350_);
lean_dec(v___x_3342_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v___x_3355_; 
if (v_isShared_3353_ == 0)
{
v___x_3355_ = v___x_3352_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_a_3350_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
}
}
}
else
{
lean_dec(v___x_2907_);
if (v_useReducible_2908_ == 0)
{
lean_dec(v___x_2906_);
if (lean_obj_tag(v___y_3310_) == 0)
{
lean_dec(v___y_3320_);
lean_dec(v___y_3317_);
lean_dec(v___y_3312_);
lean_dec(v___y_3307_);
lean_dec_ref(v___x_2910_);
lean_dec_ref(v___f_2909_);
lean_dec(v___x_2904_);
lean_dec_ref(v___x_2903_);
lean_dec_ref(v___x_2902_);
lean_dec_ref(v___x_2901_);
v___y_2969_ = v___y_3314_;
v___y_2970_ = v___y_3306_;
v___y_2971_ = v___y_3311_;
v___y_2972_ = v___y_3318_;
v___y_2973_ = v___y_3316_;
v___y_2974_ = v___y_3309_;
v___y_2975_ = v___y_3308_;
v___y_2976_ = v___y_3315_;
v___y_2977_ = v___y_3319_;
goto v___jp_2968_;
}
else
{
lean_object* v_val_3358_; lean_object* v___x_3359_; 
v_val_3358_ = lean_ctor_get(v___y_3310_, 0);
lean_inc(v_val_3358_);
lean_dec_ref_known(v___y_3310_, 1);
lean_inc(v___y_3319_);
lean_inc_ref(v___y_3315_);
v___x_3359_ = lean_apply_9(v___f_2909_, v___y_3306_, v___y_3311_, v___y_3318_, v___y_3316_, v___y_3309_, v___y_3308_, v___y_3315_, v___y_3319_, lean_box(0));
if (lean_obj_tag(v___x_3359_) == 0)
{
lean_object* v_a_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; 
v_a_3360_ = lean_ctor_get(v___x_3359_, 0);
lean_inc_n(v_a_3360_, 5);
lean_dec_ref_known(v___x_3359_, 1);
v___x_3361_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__7));
lean_inc_ref_n(v___x_2903_, 2);
lean_inc_ref_n(v___x_2902_, 2);
lean_inc_ref_n(v___x_2901_, 2);
v___x_3362_ = l_Lean_Name_mkStr4(v___x_2901_, v___x_2902_, v___x_2903_, v___x_3361_);
v___x_3363_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3363_, 0, v_a_3360_);
lean_ctor_set(v___x_3363_, 1, v___x_2910_);
v___x_3364_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3364_, 0, v_a_3360_);
lean_ctor_set(v___x_3364_, 1, v___x_2998_);
lean_ctor_set(v___x_3364_, 2, v___x_2999_);
v___x_3365_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__9));
v___x_3366_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3366_, 0, v_a_3360_);
lean_ctor_set(v___x_3366_, 1, v___x_3365_);
v___x_3367_ = l_Lean_Syntax_node1(v_a_3360_, v___x_2998_, v___x_3366_);
v___x_3368_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__8));
v___x_3369_ = l_Lean_Name_mkStr4(v___x_2901_, v___x_2902_, v___x_2903_, v___x_3368_);
if (lean_obj_tag(v___y_3320_) == 0)
{
lean_object* v___x_3370_; 
v___x_3370_ = lean_mk_empty_array_with_capacity(v___x_2904_);
v___y_3132_ = v___y_3307_;
v___y_3133_ = v___x_3364_;
v___y_3134_ = v___x_3363_;
v___y_3135_ = v___y_3312_;
v___y_3136_ = v___x_3367_;
v___y_3137_ = v_a_3360_;
v___y_3138_ = v___y_3314_;
v___y_3139_ = v___x_3369_;
v___y_3140_ = v___y_3315_;
v___y_3141_ = v___y_3317_;
v___y_3142_ = v___x_3362_;
v___y_3143_ = v_val_3358_;
v___y_3144_ = v___y_3319_;
v___y_3145_ = v___x_3370_;
goto v___jp_3131_;
}
else
{
lean_object* v_val_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; 
v_val_3371_ = lean_ctor_get(v___y_3320_, 0);
lean_inc(v_val_3371_);
lean_dec_ref_known(v___y_3320_, 1);
v___x_3372_ = lean_mk_empty_array_with_capacity(v___x_2904_);
v___x_3373_ = lean_array_push(v___x_3372_, v_val_3371_);
v___y_3132_ = v___y_3307_;
v___y_3133_ = v___x_3364_;
v___y_3134_ = v___x_3363_;
v___y_3135_ = v___y_3312_;
v___y_3136_ = v___x_3367_;
v___y_3137_ = v_a_3360_;
v___y_3138_ = v___y_3314_;
v___y_3139_ = v___x_3369_;
v___y_3140_ = v___y_3315_;
v___y_3141_ = v___y_3317_;
v___y_3142_ = v___x_3362_;
v___y_3143_ = v_val_3358_;
v___y_3144_ = v___y_3319_;
v___y_3145_ = v___x_3373_;
goto v___jp_3131_;
}
}
else
{
lean_object* v_a_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3381_; 
lean_dec(v_val_3358_);
lean_dec(v___y_3320_);
lean_dec(v___y_3319_);
lean_dec(v___y_3317_);
lean_dec_ref(v___y_3315_);
lean_dec_ref(v___y_3314_);
lean_dec(v___y_3312_);
lean_dec(v___y_3307_);
lean_dec_ref(v___x_2910_);
lean_dec(v___x_2904_);
lean_dec_ref(v___x_2903_);
lean_dec_ref(v___x_2902_);
lean_dec_ref(v___x_2901_);
lean_dec(v_tk_2900_);
v_a_3374_ = lean_ctor_get(v___x_3359_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3376_ = v___x_3359_;
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_a_3374_);
lean_dec(v___x_3359_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v___x_3379_; 
if (v_isShared_3377_ == 0)
{
v___x_3379_ = v___x_3376_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_a_3374_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
}
}
}
else
{
lean_object* v___x_3382_; 
lean_dec_ref(v___x_2910_);
lean_inc(v___y_3319_);
lean_inc_ref(v___y_3315_);
v___x_3382_ = lean_apply_9(v___f_2909_, v___y_3306_, v___y_3311_, v___y_3318_, v___y_3316_, v___y_3309_, v___y_3308_, v___y_3315_, v___y_3319_, lean_box(0));
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_object* v_a_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; 
v_a_3383_ = lean_ctor_get(v___x_3382_, 0);
lean_inc_n(v_a_3383_, 2);
lean_dec_ref_known(v___x_3382_, 1);
v___x_3384_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__10));
lean_inc_ref(v___x_2903_);
lean_inc_ref(v___x_2902_);
lean_inc_ref(v___x_2901_);
v___x_3385_ = l_Lean_Name_mkStr4(v___x_2901_, v___x_2902_, v___x_2903_, v___x_3384_);
v___x_3386_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__11));
v___x_3387_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3387_, 0, v_a_3383_);
lean_ctor_set(v___x_3387_, 1, v___x_3386_);
if (lean_obj_tag(v___y_3320_) == 0)
{
lean_object* v___x_3388_; 
v___x_3388_ = lean_mk_empty_array_with_capacity(v___x_2904_);
v___y_3062_ = v___x_3385_;
v___y_3063_ = v_a_3383_;
v___y_3064_ = v___y_3314_;
v___y_3065_ = v___y_3307_;
v___y_3066_ = v___y_3310_;
v___y_3067_ = v___y_3315_;
v___y_3068_ = v___y_3317_;
v___y_3069_ = v___x_3387_;
v___y_3070_ = v___y_3312_;
v___y_3071_ = v___y_3319_;
v___y_3072_ = v___x_3388_;
goto v___jp_3061_;
}
else
{
lean_object* v_val_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; 
v_val_3389_ = lean_ctor_get(v___y_3320_, 0);
lean_inc(v_val_3389_);
lean_dec_ref_known(v___y_3320_, 1);
v___x_3390_ = lean_mk_empty_array_with_capacity(v___x_2904_);
v___x_3391_ = lean_array_push(v___x_3390_, v_val_3389_);
v___y_3062_ = v___x_3385_;
v___y_3063_ = v_a_3383_;
v___y_3064_ = v___y_3314_;
v___y_3065_ = v___y_3307_;
v___y_3066_ = v___y_3310_;
v___y_3067_ = v___y_3315_;
v___y_3068_ = v___y_3317_;
v___y_3069_ = v___x_3387_;
v___y_3070_ = v___y_3312_;
v___y_3071_ = v___y_3319_;
v___y_3072_ = v___x_3391_;
goto v___jp_3061_;
}
}
else
{
lean_object* v_a_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3399_; 
lean_dec(v___y_3320_);
lean_dec(v___y_3319_);
lean_dec(v___y_3317_);
lean_dec_ref(v___y_3315_);
lean_dec_ref(v___y_3314_);
lean_dec(v___y_3312_);
lean_dec(v___y_3310_);
lean_dec(v___y_3307_);
lean_dec(v___x_2906_);
lean_dec(v___x_2904_);
lean_dec_ref(v___x_2903_);
lean_dec_ref(v___x_2902_);
lean_dec_ref(v___x_2901_);
lean_dec(v_tk_2900_);
v_a_3392_ = lean_ctor_get(v___x_3382_, 0);
v_isSharedCheck_3399_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3399_ == 0)
{
v___x_3394_ = v___x_3382_;
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
else
{
lean_inc(v_a_3392_);
lean_dec(v___x_3382_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
lean_object* v___x_3397_; 
if (v_isShared_3395_ == 0)
{
v___x_3397_ = v___x_3394_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v_a_3392_);
v___x_3397_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
return v___x_3397_;
}
}
}
}
}
}
v___jp_3400_:
{
lean_object* v___x_3417_; lean_object* v___x_3418_; uint8_t v___x_3419_; 
v___x_3417_ = lean_unsigned_to_nat(5u);
v___x_3418_ = l_Lean_Syntax_getArg(v___y_3407_, v___x_3417_);
lean_dec(v___y_3407_);
v___x_3419_ = l_Lean_Syntax_matchesNull(v___x_3418_, v___x_2904_);
if (v___x_3419_ == 0)
{
lean_object* v___x_3420_; lean_object* v___x_3421_; 
lean_dec(v_args_3408_);
lean_dec(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec(v___y_3403_);
lean_dec(v___y_3402_);
lean_dec_ref(v___x_2910_);
lean_dec_ref(v___f_2909_);
lean_dec(v___x_2907_);
lean_dec(v___x_2906_);
lean_dec(v___x_2904_);
lean_dec_ref(v___x_2903_);
lean_dec_ref(v___x_2902_);
lean_dec_ref(v___x_2901_);
v___x_3420_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3421_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3420_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_);
lean_dec(v___y_3414_);
lean_dec_ref(v___y_3413_);
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
if (lean_obj_tag(v___x_3421_) == 0)
{
lean_object* v_a_3422_; 
v_a_3422_ = lean_ctor_get(v___x_3421_, 0);
lean_inc(v_a_3422_);
lean_dec_ref_known(v___x_3421_, 1);
v___y_2963_ = v___y_3401_;
v_stx_2964_ = v_a_3422_;
v___y_2965_ = v___y_3415_;
v___y_2966_ = v___y_3416_;
goto v___jp_2962_;
}
else
{
lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3430_; 
lean_dec(v___y_3416_);
lean_dec_ref(v___y_3415_);
lean_dec_ref(v___y_3401_);
lean_dec(v_tk_2900_);
v_a_3423_ = lean_ctor_get(v___x_3421_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v___x_3421_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3425_ = v___x_3421_;
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v___x_3421_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3428_; 
if (v_isShared_3426_ == 0)
{
v___x_3428_ = v___x_3425_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_a_3423_);
v___x_3428_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
return v___x_3428_;
}
}
}
}
else
{
lean_object* v___x_3431_; 
v___x_3431_ = l_Lean_Syntax_getOptional_x3f(v___y_3402_);
lean_dec(v___y_3402_);
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_object* v___x_3432_; 
v___x_3432_ = lean_box(0);
v___y_3306_ = v___y_3409_;
v___y_3307_ = v_args_3408_;
v___y_3308_ = v___y_3414_;
v___y_3309_ = v___y_3413_;
v___y_3310_ = v___y_3403_;
v___y_3311_ = v___y_3410_;
v___y_3312_ = v___y_3405_;
v___y_3313_ = v___y_3406_;
v___y_3314_ = v___y_3401_;
v___y_3315_ = v___y_3415_;
v___y_3316_ = v___y_3412_;
v___y_3317_ = v___y_3404_;
v___y_3318_ = v___y_3411_;
v___y_3319_ = v___y_3416_;
v___y_3320_ = v___x_3432_;
goto v___jp_3305_;
}
else
{
lean_object* v_val_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3440_; 
v_val_3433_ = lean_ctor_get(v___x_3431_, 0);
v_isSharedCheck_3440_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3435_ = v___x_3431_;
v_isShared_3436_ = v_isSharedCheck_3440_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_val_3433_);
lean_dec(v___x_3431_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3440_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3438_; 
if (v_isShared_3436_ == 0)
{
v___x_3438_ = v___x_3435_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v_val_3433_);
v___x_3438_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
v___y_3306_ = v___y_3409_;
v___y_3307_ = v_args_3408_;
v___y_3308_ = v___y_3414_;
v___y_3309_ = v___y_3413_;
v___y_3310_ = v___y_3403_;
v___y_3311_ = v___y_3410_;
v___y_3312_ = v___y_3405_;
v___y_3313_ = v___y_3406_;
v___y_3314_ = v___y_3401_;
v___y_3315_ = v___y_3415_;
v___y_3316_ = v___y_3412_;
v___y_3317_ = v___y_3404_;
v___y_3318_ = v___y_3411_;
v___y_3319_ = v___y_3416_;
v___y_3320_ = v___x_3438_;
goto v___jp_3305_;
}
}
}
}
}
v___jp_3441_:
{
lean_object* v___x_3457_; uint8_t v___x_3458_; 
v___x_3457_ = l_Lean_Syntax_getArg(v___y_3447_, v___x_2911_);
v___x_3458_ = l_Lean_Syntax_isNone(v___x_3457_);
if (v___x_3458_ == 0)
{
uint8_t v___x_3459_; 
lean_inc(v___x_3457_);
v___x_3459_ = l_Lean_Syntax_matchesNull(v___x_3457_, v___x_2912_);
if (v___x_3459_ == 0)
{
lean_object* v___x_3460_; lean_object* v___x_3461_; 
lean_dec(v___x_3457_);
lean_dec(v_only_3448_);
lean_dec(v___y_3447_);
lean_dec(v___y_3445_);
lean_dec(v___y_3444_);
lean_dec(v___y_3443_);
lean_dec(v___x_2913_);
lean_dec_ref(v___x_2910_);
lean_dec_ref(v___f_2909_);
lean_dec(v___x_2907_);
lean_dec(v___x_2906_);
lean_dec(v___x_2904_);
lean_dec_ref(v___x_2903_);
lean_dec_ref(v___x_2902_);
lean_dec_ref(v___x_2901_);
v___x_3460_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3461_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3460_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec(v___y_3452_);
lean_dec_ref(v___y_3451_);
lean_dec(v___y_3450_);
lean_dec_ref(v___y_3449_);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_object* v_a_3462_; 
v_a_3462_ = lean_ctor_get(v___x_3461_, 0);
lean_inc(v_a_3462_);
lean_dec_ref_known(v___x_3461_, 1);
v___y_2963_ = v___y_3442_;
v_stx_2964_ = v_a_3462_;
v___y_2965_ = v___y_3455_;
v___y_2966_ = v___y_3456_;
goto v___jp_2962_;
}
else
{
lean_object* v_a_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3470_; 
lean_dec(v___y_3456_);
lean_dec_ref(v___y_3455_);
lean_dec_ref(v___y_3442_);
lean_dec(v_tk_2900_);
v_a_3463_ = lean_ctor_get(v___x_3461_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3461_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3465_ = v___x_3461_;
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___x_3461_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3468_; 
if (v_isShared_3466_ == 0)
{
v___x_3468_ = v___x_3465_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_a_3463_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
return v___x_3468_;
}
}
}
}
else
{
lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; 
v___x_3471_ = l_Lean_Syntax_getArg(v___x_3457_, v___x_2913_);
lean_dec(v___x_2913_);
lean_dec(v___x_3457_);
v___x_3472_ = l_Lean_Syntax_getArgs(v___x_3471_);
lean_dec(v___x_3471_);
v___x_3473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3473_, 0, v___x_3472_);
v___y_3401_ = v___y_3442_;
v___y_3402_ = v___y_3443_;
v___y_3403_ = v___y_3444_;
v___y_3404_ = v___y_3445_;
v___y_3405_ = v_only_3448_;
v___y_3406_ = v___y_3446_;
v___y_3407_ = v___y_3447_;
v_args_3408_ = v___x_3473_;
v___y_3409_ = v___y_3449_;
v___y_3410_ = v___y_3450_;
v___y_3411_ = v___y_3451_;
v___y_3412_ = v___y_3452_;
v___y_3413_ = v___y_3453_;
v___y_3414_ = v___y_3454_;
v___y_3415_ = v___y_3455_;
v___y_3416_ = v___y_3456_;
goto v___jp_3400_;
}
}
else
{
lean_object* v___x_3474_; 
lean_dec(v___x_3457_);
lean_dec(v___x_2913_);
v___x_3474_ = lean_box(0);
v___y_3401_ = v___y_3442_;
v___y_3402_ = v___y_3443_;
v___y_3403_ = v___y_3444_;
v___y_3404_ = v___y_3445_;
v___y_3405_ = v_only_3448_;
v___y_3406_ = v___y_3446_;
v___y_3407_ = v___y_3447_;
v_args_3408_ = v___x_3474_;
v___y_3409_ = v___y_3449_;
v___y_3410_ = v___y_3450_;
v___y_3411_ = v___y_3451_;
v___y_3412_ = v___y_3452_;
v___y_3413_ = v___y_3453_;
v___y_3414_ = v___y_3454_;
v___y_3415_ = v___y_3455_;
v___y_3416_ = v___y_3456_;
goto v___jp_3400_;
}
}
v___jp_3475_:
{
lean_object* v_usedTheorems_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; 
v_usedTheorems_3480_ = lean_ctor_get(v___y_3476_, 0);
v___x_3481_ = l_Lean_Syntax_unsetTrailing(v___y_3478_);
v___x_3482_ = l_Lean_Elab_Tactic_mkSimpOnly(v___x_3481_, v_usedTheorems_3480_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
if (lean_obj_tag(v___x_3482_) == 0)
{
lean_object* v_a_3483_; uint8_t v___x_3484_; 
v_a_3483_ = lean_ctor_get(v___x_3482_, 0);
lean_inc_n(v_a_3483_, 2);
lean_dec_ref_known(v___x_3482_, 1);
v___x_3484_ = l_Lean_Syntax_isOfKind(v_a_3483_, v___x_2996_);
lean_dec(v___x_2996_);
if (v___x_3484_ == 0)
{
lean_object* v___x_3485_; lean_object* v___x_3486_; 
lean_inc(v_ref_2992_);
lean_dec(v_a_3483_);
lean_dec(v___y_3479_);
lean_dec(v___x_2915_);
lean_dec(v___x_2913_);
lean_dec_ref(v___x_2910_);
lean_dec_ref(v___f_2909_);
lean_dec(v___x_2907_);
lean_dec(v___x_2906_);
lean_dec(v___x_2904_);
lean_dec_ref(v___x_2903_);
lean_dec_ref(v___x_2902_);
lean_dec_ref(v___x_2901_);
v___x_3485_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3486_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3485_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v_a_3487_; 
v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
lean_inc(v_a_3487_);
lean_dec_ref_known(v___x_3486_, 1);
v___y_2940_ = v___y_3476_;
v_stx_2941_ = v_a_3487_;
v___y_2942_ = v___y_2932_;
v_ref_2943_ = v_ref_2992_;
v___y_2944_ = v___y_2933_;
goto v___jp_2939_;
}
else
{
lean_object* v_a_3488_; lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3495_; 
lean_dec_ref(v___y_3476_);
lean_dec(v_ref_2992_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec(v_tk_2900_);
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
lean_object* v___x_3496_; uint8_t v___x_3497_; 
v___x_3496_ = l_Lean_Syntax_getArg(v_a_3483_, v___x_2913_);
lean_inc(v___x_3496_);
v___x_3497_ = l_Lean_Syntax_isOfKind(v___x_3496_, v___x_2914_);
if (v___x_3497_ == 0)
{
lean_object* v___x_3498_; lean_object* v___x_3499_; 
lean_inc(v_ref_2992_);
lean_dec(v___x_3496_);
lean_dec(v_a_3483_);
lean_dec(v___y_3479_);
lean_dec(v___x_2915_);
lean_dec(v___x_2913_);
lean_dec_ref(v___x_2910_);
lean_dec_ref(v___f_2909_);
lean_dec(v___x_2907_);
lean_dec(v___x_2906_);
lean_dec(v___x_2904_);
lean_dec_ref(v___x_2903_);
lean_dec_ref(v___x_2902_);
lean_dec_ref(v___x_2901_);
v___x_3498_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3499_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3498_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
if (lean_obj_tag(v___x_3499_) == 0)
{
lean_object* v_a_3500_; 
v_a_3500_ = lean_ctor_get(v___x_3499_, 0);
lean_inc(v_a_3500_);
lean_dec_ref_known(v___x_3499_, 1);
v___y_2940_ = v___y_3476_;
v_stx_2941_ = v_a_3500_;
v___y_2942_ = v___y_2932_;
v_ref_2943_ = v_ref_2992_;
v___y_2944_ = v___y_2933_;
goto v___jp_2939_;
}
else
{
lean_object* v_a_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3508_; 
lean_dec_ref(v___y_3476_);
lean_dec(v_ref_2992_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec(v_tk_2900_);
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
lean_object* v___x_3509_; lean_object* v___x_3510_; uint8_t v___x_3511_; 
v___x_3509_ = l_Lean_Syntax_getArg(v_a_3483_, v___x_2915_);
lean_dec(v___x_2915_);
v___x_3510_ = l_Lean_Syntax_getArg(v_a_3483_, v___x_2912_);
v___x_3511_ = l_Lean_Syntax_isNone(v___x_3510_);
if (v___x_3511_ == 0)
{
uint8_t v___x_3512_; 
lean_inc(v___x_3510_);
v___x_3512_ = l_Lean_Syntax_matchesNull(v___x_3510_, v___x_2913_);
if (v___x_3512_ == 0)
{
lean_object* v___x_3513_; lean_object* v___x_3514_; 
lean_inc(v_ref_2992_);
lean_dec(v___x_3510_);
lean_dec(v___x_3509_);
lean_dec(v___x_3496_);
lean_dec(v_a_3483_);
lean_dec(v___y_3479_);
lean_dec(v___x_2913_);
lean_dec_ref(v___x_2910_);
lean_dec_ref(v___f_2909_);
lean_dec(v___x_2907_);
lean_dec(v___x_2906_);
lean_dec(v___x_2904_);
lean_dec_ref(v___x_2903_);
lean_dec_ref(v___x_2902_);
lean_dec_ref(v___x_2901_);
v___x_3513_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3514_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3513_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_object* v_a_3515_; 
v_a_3515_ = lean_ctor_get(v___x_3514_, 0);
lean_inc(v_a_3515_);
lean_dec_ref_known(v___x_3514_, 1);
v___y_2940_ = v___y_3476_;
v_stx_2941_ = v_a_3515_;
v___y_2942_ = v___y_2932_;
v_ref_2943_ = v_ref_2992_;
v___y_2944_ = v___y_2933_;
goto v___jp_2939_;
}
else
{
lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3523_; 
lean_dec_ref(v___y_3476_);
lean_dec(v_ref_2992_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec(v_tk_2900_);
v_a_3516_ = lean_ctor_get(v___x_3514_, 0);
v_isSharedCheck_3523_ = !lean_is_exclusive(v___x_3514_);
if (v_isSharedCheck_3523_ == 0)
{
v___x_3518_ = v___x_3514_;
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_3514_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v___x_3521_; 
if (v_isShared_3519_ == 0)
{
v___x_3521_ = v___x_3518_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_a_3516_);
v___x_3521_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
return v___x_3521_;
}
}
}
}
else
{
lean_object* v___x_3524_; lean_object* v___x_3525_; 
v___x_3524_ = l_Lean_Syntax_getArg(v___x_3510_, v___x_2904_);
lean_dec(v___x_3510_);
v___x_3525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3525_, 0, v___x_3524_);
v___y_3442_ = v___y_3476_;
v___y_3443_ = v___x_3509_;
v___y_3444_ = v___y_3479_;
v___y_3445_ = v___x_3496_;
v___y_3446_ = v___y_3477_;
v___y_3447_ = v_a_3483_;
v_only_3448_ = v___x_3525_;
v___y_3449_ = v___y_2926_;
v___y_3450_ = v___y_2927_;
v___y_3451_ = v___y_2928_;
v___y_3452_ = v___y_2929_;
v___y_3453_ = v___y_2930_;
v___y_3454_ = v___y_2931_;
v___y_3455_ = v___y_2932_;
v___y_3456_ = v___y_2933_;
goto v___jp_3441_;
}
}
else
{
lean_object* v___x_3526_; 
lean_dec(v___x_3510_);
v___x_3526_ = lean_box(0);
v___y_3442_ = v___y_3476_;
v___y_3443_ = v___x_3509_;
v___y_3444_ = v___y_3479_;
v___y_3445_ = v___x_3496_;
v___y_3446_ = v___y_3477_;
v___y_3447_ = v_a_3483_;
v_only_3448_ = v___x_3526_;
v___y_3449_ = v___y_2926_;
v___y_3450_ = v___y_2927_;
v___y_3451_ = v___y_2928_;
v___y_3452_ = v___y_2929_;
v___y_3453_ = v___y_2930_;
v___y_3454_ = v___y_2931_;
v___y_3455_ = v___y_2932_;
v___y_3456_ = v___y_2933_;
goto v___jp_3441_;
}
}
}
}
else
{
lean_object* v_a_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3534_; 
lean_dec(v___y_3479_);
lean_dec_ref(v___y_3476_);
lean_dec(v___x_2996_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
lean_dec(v___x_2915_);
lean_dec(v___x_2913_);
lean_dec_ref(v___x_2910_);
lean_dec_ref(v___f_2909_);
lean_dec(v___x_2907_);
lean_dec(v___x_2906_);
lean_dec(v___x_2904_);
lean_dec_ref(v___x_2903_);
lean_dec_ref(v___x_2902_);
lean_dec_ref(v___x_2901_);
lean_dec(v_tk_2900_);
v_a_3527_ = lean_ctor_get(v___x_3482_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v___x_3482_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3529_ = v___x_3482_;
v_isShared_3530_ = v_isSharedCheck_3534_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_a_3527_);
lean_dec(v___x_3482_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3534_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
lean_object* v___x_3532_; 
if (v_isShared_3530_ == 0)
{
v___x_3532_ = v___x_3529_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_a_3527_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
return v___x_3532_;
}
}
}
}
v___jp_3535_:
{
if (lean_obj_tag(v_usingArg_2916_) == 0)
{
v___y_3476_ = v___y_3536_;
v___y_3477_ = v___y_3538_;
v___y_3478_ = v___y_3537_;
v___y_3479_ = v_usingArg_2916_;
goto v___jp_3475_;
}
else
{
lean_object* v_val_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3547_; 
v_val_3539_ = lean_ctor_get(v_usingArg_2916_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v_usingArg_2916_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3541_ = v_usingArg_2916_;
v_isShared_3542_ = v_isSharedCheck_3547_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_val_3539_);
lean_dec(v_usingArg_2916_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3547_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3543_; lean_object* v___x_3545_; 
v___x_3543_ = l_Lean_Syntax_unsetTrailing(v_val_3539_);
if (v_isShared_3542_ == 0)
{
lean_ctor_set(v___x_3541_, 0, v___x_3543_);
v___x_3545_ = v___x_3541_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v___x_3543_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
v___y_3476_ = v___y_3536_;
v___y_3477_ = v___y_3538_;
v___y_3478_ = v___y_3537_;
v___y_3479_ = v___x_3545_;
goto v___jp_3475_;
}
}
}
}
v___jp_3548_:
{
if (v___y_3552_ == 0)
{
lean_dec(v___y_3551_);
lean_dec(v___x_2996_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
lean_dec(v_usingArg_2916_);
lean_dec(v___x_2915_);
lean_dec(v___x_2913_);
lean_dec_ref(v___x_2910_);
lean_dec_ref(v___f_2909_);
lean_dec(v___x_2907_);
lean_dec(v___x_2906_);
lean_dec(v___x_2904_);
lean_dec_ref(v___x_2903_);
lean_dec_ref(v___x_2902_);
lean_dec_ref(v___x_2901_);
lean_dec(v_tk_2900_);
v___y_2936_ = v___y_3549_;
goto v___jp_2935_;
}
else
{
v___y_3536_ = v___y_3549_;
v___y_3537_ = v___y_3551_;
v___y_3538_ = v___y_3550_;
goto v___jp_3535_;
}
}
v___jp_3553_:
{
lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___f_3564_; lean_object* v___x_3565_; 
v___x_3559_ = l_Lean_Meta_Simp_Context_setFailIfUnchanged(v___y_3558_, v___x_2993_);
v___x_3560_ = lean_box(v___x_2905_);
v___x_3561_ = lean_box(v___x_2993_);
v___x_3562_ = lean_box(v_useReducible_2908_);
v___x_3563_ = lean_box(v___x_2918_);
lean_inc_ref(v___x_2903_);
lean_inc_ref(v___x_2902_);
lean_inc_ref(v___x_2901_);
lean_inc_ref(v___f_2909_);
lean_inc(v___x_2913_);
lean_inc_ref(v___x_2910_);
lean_inc(v_usingArg_2916_);
lean_inc(v___x_2904_);
lean_inc(v_tk_2900_);
lean_inc(v___x_2915_);
v___f_3564_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___boxed), 30, 20);
lean_closure_set(v___f_3564_, 0, v___x_2915_);
lean_closure_set(v___f_3564_, 1, v_tk_2900_);
lean_closure_set(v___f_3564_, 2, v___x_2998_);
lean_closure_set(v___f_3564_, 3, v___x_2904_);
lean_closure_set(v___f_3564_, 4, v___x_3559_);
lean_closure_set(v___f_3564_, 5, v___y_3554_);
lean_closure_set(v___f_3564_, 6, v___x_3560_);
lean_closure_set(v___f_3564_, 7, v_usingArg_2916_);
lean_closure_set(v___f_3564_, 8, v___x_2910_);
lean_closure_set(v___f_3564_, 9, v___x_3561_);
lean_closure_set(v___f_3564_, 10, v___x_3562_);
lean_closure_set(v___f_3564_, 11, v___x_3563_);
lean_closure_set(v___f_3564_, 12, v___x_2913_);
lean_closure_set(v___f_3564_, 13, v___f_2909_);
lean_closure_set(v___f_3564_, 14, v___x_2901_);
lean_closure_set(v___f_3564_, 15, v___x_2902_);
lean_closure_set(v___f_3564_, 16, v___x_2903_);
lean_closure_set(v___f_3564_, 17, v___f_2919_);
lean_closure_set(v___f_3564_, 18, v_a_2990_);
lean_closure_set(v___f_3564_, 19, v_usingTk_x3f_2920_);
v___x_3565_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v___y_3555_, v___f_3564_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
lean_dec(v___y_3555_);
if (lean_obj_tag(v___x_3565_) == 0)
{
lean_object* v_a_3566_; lean_object* v_options_3567_; lean_object* v___x_3568_; uint8_t v___x_3569_; 
v_a_3566_ = lean_ctor_get(v___x_3565_, 0);
lean_inc(v_a_3566_);
lean_dec_ref_known(v___x_3565_, 1);
v_options_3567_ = lean_ctor_get(v_toCold_2991_, 2);
v___x_3568_ = l_Lean_Elab_Tactic_tactic_simp_trace;
v___x_3569_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__3(v_options_3567_, v___x_3568_);
if (v___x_3569_ == 0)
{
if (lean_obj_tag(v_squeeze_2921_) == 0)
{
v___y_3549_ = v_a_3566_;
v___y_3550_ = v___y_3557_;
v___y_3551_ = v___y_3556_;
v___y_3552_ = v___x_3569_;
goto v___jp_3548_;
}
else
{
v___y_3549_ = v_a_3566_;
v___y_3550_ = v___y_3557_;
v___y_3551_ = v___y_3556_;
v___y_3552_ = v___x_2918_;
goto v___jp_3548_;
}
}
else
{
v___y_3536_ = v_a_3566_;
v___y_3537_ = v___y_3556_;
v___y_3538_ = v___y_3557_;
goto v___jp_3535_;
}
}
else
{
lean_object* v_a_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3577_; 
lean_dec(v___y_3556_);
lean_dec(v___x_2996_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
lean_dec(v_usingArg_2916_);
lean_dec(v___x_2915_);
lean_dec(v___x_2913_);
lean_dec_ref(v___x_2910_);
lean_dec_ref(v___f_2909_);
lean_dec(v___x_2907_);
lean_dec(v___x_2906_);
lean_dec(v___x_2904_);
lean_dec_ref(v___x_2903_);
lean_dec_ref(v___x_2902_);
lean_dec_ref(v___x_2901_);
lean_dec(v_tk_2900_);
v_a_3570_ = lean_ctor_get(v___x_3565_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3565_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3572_ = v___x_3565_;
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_a_3570_);
lean_dec(v___x_3565_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v___x_3575_; 
if (v_isShared_3573_ == 0)
{
v___x_3575_ = v___x_3572_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_a_3570_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
}
}
}
}
v___jp_3578_:
{
lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; uint8_t v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; 
v___x_3582_ = l_Array_append___redArg(v___x_2999_, v___y_3581_);
lean_dec_ref(v___y_3581_);
lean_inc_n(v___x_2994_, 2);
v___x_3583_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3583_, 0, v___x_2994_);
lean_ctor_set(v___x_3583_, 1, v___x_2998_);
lean_ctor_set(v___x_3583_, 2, v___x_3582_);
v___x_3584_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3584_, 0, v___x_2994_);
lean_ctor_set(v___x_3584_, 1, v___x_2998_);
lean_ctor_set(v___x_3584_, 2, v___x_2999_);
lean_inc(v___x_2996_);
v___x_3585_ = l_Lean_Syntax_node6(v___x_2994_, v___x_2996_, v___x_2997_, v___x_2917_, v___y_3580_, v___y_3579_, v___x_3583_, v___x_3584_);
v___x_3586_ = 0;
v___x_3587_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__13));
v___x_3588_ = lean_box(v___x_2993_);
v___x_3589_ = lean_box(v___x_3586_);
v___x_3590_ = lean_box(v___x_2993_);
lean_inc(v___x_3585_);
v___x_3591_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_3591_, 0, v___x_3585_);
lean_closure_set(v___x_3591_, 1, v___x_3588_);
lean_closure_set(v___x_3591_, 2, v___x_3589_);
lean_closure_set(v___x_3591_, 3, v___x_3590_);
lean_closure_set(v___x_3591_, 4, v___x_3587_);
v___x_3592_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_3591_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
if (lean_obj_tag(v___x_3592_) == 0)
{
lean_object* v_a_3593_; 
v_a_3593_ = lean_ctor_get(v___x_3592_, 0);
lean_inc(v_a_3593_);
lean_dec_ref_known(v___x_3592_, 1);
if (lean_obj_tag(v_unfold_2922_) == 0)
{
lean_object* v_ctx_3594_; lean_object* v_simprocs_3595_; lean_object* v_dischargeWrapper_3596_; 
v_ctx_3594_ = lean_ctor_get(v_a_3593_, 0);
lean_inc_ref(v_ctx_3594_);
v_simprocs_3595_ = lean_ctor_get(v_a_3593_, 1);
lean_inc_ref(v_simprocs_3595_);
v_dischargeWrapper_3596_ = lean_ctor_get(v_a_3593_, 2);
lean_inc(v_dischargeWrapper_3596_);
lean_dec(v_a_3593_);
v___y_3554_ = v_simprocs_3595_;
v___y_3555_ = v_dischargeWrapper_3596_;
v___y_3556_ = v___x_3585_;
v___y_3557_ = v___x_2993_;
v___y_3558_ = v_ctx_3594_;
goto v___jp_3553_;
}
else
{
if (v___x_2918_ == 0)
{
lean_object* v_ctx_3597_; lean_object* v_simprocs_3598_; lean_object* v_dischargeWrapper_3599_; 
v_ctx_3597_ = lean_ctor_get(v_a_3593_, 0);
lean_inc_ref(v_ctx_3597_);
v_simprocs_3598_ = lean_ctor_get(v_a_3593_, 1);
lean_inc_ref(v_simprocs_3598_);
v_dischargeWrapper_3599_ = lean_ctor_get(v_a_3593_, 2);
lean_inc(v_dischargeWrapper_3599_);
lean_dec(v_a_3593_);
v___y_3554_ = v_simprocs_3598_;
v___y_3555_ = v_dischargeWrapper_3599_;
v___y_3556_ = v___x_3585_;
v___y_3557_ = v___x_2918_;
v___y_3558_ = v_ctx_3597_;
goto v___jp_3553_;
}
else
{
lean_object* v_ctx_3600_; lean_object* v_simprocs_3601_; lean_object* v_dischargeWrapper_3602_; lean_object* v___x_3603_; 
v_ctx_3600_ = lean_ctor_get(v_a_3593_, 0);
lean_inc_ref(v_ctx_3600_);
v_simprocs_3601_ = lean_ctor_get(v_a_3593_, 1);
lean_inc_ref(v_simprocs_3601_);
v_dischargeWrapper_3602_ = lean_ctor_get(v_a_3593_, 2);
lean_inc(v_dischargeWrapper_3602_);
lean_dec(v_a_3593_);
v___x_3603_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_3600_);
v___y_3554_ = v_simprocs_3601_;
v___y_3555_ = v_dischargeWrapper_3602_;
v___y_3556_ = v___x_3585_;
v___y_3557_ = v___x_2918_;
v___y_3558_ = v___x_3603_;
goto v___jp_3553_;
}
}
}
else
{
lean_object* v_a_3604_; lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3611_; 
lean_dec(v___x_3585_);
lean_dec(v___x_2996_);
lean_dec(v_a_2990_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
lean_dec(v_usingTk_x3f_2920_);
lean_dec_ref(v___f_2919_);
lean_dec(v_usingArg_2916_);
lean_dec(v___x_2915_);
lean_dec(v___x_2913_);
lean_dec_ref(v___x_2910_);
lean_dec_ref(v___f_2909_);
lean_dec(v___x_2907_);
lean_dec(v___x_2906_);
lean_dec(v___x_2904_);
lean_dec_ref(v___x_2903_);
lean_dec_ref(v___x_2902_);
lean_dec_ref(v___x_2901_);
lean_dec(v_tk_2900_);
v_a_3604_ = lean_ctor_get(v___x_3592_, 0);
v_isSharedCheck_3611_ = !lean_is_exclusive(v___x_3592_);
if (v_isSharedCheck_3611_ == 0)
{
v___x_3606_ = v___x_3592_;
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
else
{
lean_inc(v_a_3604_);
lean_dec(v___x_3592_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v___x_3609_; 
if (v_isShared_3607_ == 0)
{
v___x_3609_ = v___x_3606_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v_a_3604_);
v___x_3609_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
return v___x_3609_;
}
}
}
}
v___jp_3612_:
{
lean_object* v___x_3615_; lean_object* v___x_3616_; 
v___x_3615_ = l_Array_append___redArg(v___x_2999_, v___y_3614_);
lean_dec_ref(v___y_3614_);
lean_inc(v___x_2994_);
v___x_3616_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3616_, 0, v___x_2994_);
lean_ctor_set(v___x_3616_, 1, v___x_2998_);
lean_ctor_set(v___x_3616_, 2, v___x_3615_);
if (lean_obj_tag(v_args_2923_) == 1)
{
lean_object* v_val_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; 
v_val_3617_ = lean_ctor_get(v_args_2923_, 0);
v___x_3618_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___x_2994_, 3);
v___x_3619_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3619_, 0, v___x_2994_);
lean_ctor_set(v___x_3619_, 1, v___x_3618_);
v___x_3620_ = l_Array_append___redArg(v___x_2999_, v_val_3617_);
v___x_3621_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3621_, 0, v___x_2994_);
lean_ctor_set(v___x_3621_, 1, v___x_2998_);
lean_ctor_set(v___x_3621_, 2, v___x_3620_);
v___x_3622_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_3623_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3623_, 0, v___x_2994_);
lean_ctor_set(v___x_3623_, 1, v___x_3622_);
v___x_3624_ = l_Array_mkArray3___redArg(v___x_3619_, v___x_3621_, v___x_3623_);
v___y_3579_ = v___x_3616_;
v___y_3580_ = v___y_3613_;
v___y_3581_ = v___x_3624_;
goto v___jp_3578_;
}
else
{
lean_object* v___x_3625_; 
v___x_3625_ = lean_mk_empty_array_with_capacity(v___x_2904_);
v___y_3579_ = v___x_3616_;
v___y_3580_ = v___y_3613_;
v___y_3581_ = v___x_3625_;
goto v___jp_3578_;
}
}
v___jp_3626_:
{
lean_object* v___x_3628_; lean_object* v___x_3629_; 
v___x_3628_ = l_Array_append___redArg(v___x_2999_, v___y_3627_);
lean_dec_ref(v___y_3627_);
lean_inc(v___x_2994_);
v___x_3629_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3629_, 0, v___x_2994_);
lean_ctor_set(v___x_3629_, 1, v___x_2998_);
lean_ctor_set(v___x_3629_, 2, v___x_3628_);
if (lean_obj_tag(v_only_2924_) == 1)
{
lean_object* v_val_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; 
v_val_3630_ = lean_ctor_get(v_only_2924_, 0);
v___x_3631_ = l_Lean_SourceInfo_fromRef(v_val_3630_, v___x_2905_);
v___x_3632_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_3633_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3633_, 0, v___x_3631_);
lean_ctor_set(v___x_3633_, 1, v___x_3632_);
v___x_3634_ = l_Array_mkArray1___redArg(v___x_3633_);
v___y_3613_ = v___x_3629_;
v___y_3614_ = v___x_3634_;
goto v___jp_3612_;
}
else
{
lean_object* v___x_3635_; 
v___x_3635_ = lean_mk_empty_array_with_capacity(v___x_2904_);
v___y_3613_ = v___x_3629_;
v___y_3614_ = v___x_3635_;
goto v___jp_3612_;
}
}
}
else
{
lean_object* v_a_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3647_; 
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
lean_dec(v___y_2925_);
lean_dec(v_usingTk_x3f_2920_);
lean_dec_ref(v___f_2919_);
lean_dec(v___x_2917_);
lean_dec(v_usingArg_2916_);
lean_dec(v___x_2915_);
lean_dec(v___x_2913_);
lean_dec_ref(v___x_2910_);
lean_dec_ref(v___f_2909_);
lean_dec(v___x_2907_);
lean_dec(v___x_2906_);
lean_dec(v___x_2904_);
lean_dec_ref(v___x_2903_);
lean_dec_ref(v___x_2902_);
lean_dec_ref(v___x_2901_);
lean_dec(v_tk_2900_);
v_a_3640_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3647_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3642_ = v___x_2989_;
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_a_3640_);
lean_dec(v___x_2989_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v___x_3645_; 
if (v_isShared_3643_ == 0)
{
v___x_3645_ = v___x_3642_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_a_3640_);
v___x_3645_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
return v___x_3645_;
}
}
}
v___jp_2935_:
{
lean_object* v_diag_2937_; lean_object* v___x_2938_; 
v_diag_2937_ = lean_ctor_get(v___y_2936_, 1);
lean_inc_ref(v_diag_2937_);
lean_dec_ref(v___y_2936_);
v___x_2938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2938_, 0, v_diag_2937_);
return v___x_2938_;
}
v___jp_2939_:
{
lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; uint8_t v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2945_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__3));
v___x_2946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2946_, 0, v___x_2945_);
lean_ctor_set(v___x_2946_, 1, v_stx_2941_);
v___x_2947_ = lean_box(0);
v___x_2948_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2946_);
lean_ctor_set(v___x_2948_, 1, v___x_2947_);
lean_ctor_set(v___x_2948_, 2, v___x_2947_);
lean_ctor_set(v___x_2948_, 3, v___x_2947_);
lean_ctor_set(v___x_2948_, 4, v___x_2947_);
lean_ctor_set(v___x_2948_, 5, v___x_2947_);
v___x_2949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2949_, 0, v_ref_2943_);
v___x_2950_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__0));
v___x_2951_ = 4;
v___x_2952_ = l_Lean_MessageData_nil;
v___x_2953_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_2900_, v___x_2948_, v___x_2949_, v___x_2950_, v___x_2947_, v___x_2951_, v___x_2952_, v___y_2942_, v___y_2944_);
lean_dec(v___y_2944_);
lean_dec_ref(v___y_2942_);
if (lean_obj_tag(v___x_2953_) == 0)
{
lean_dec_ref_known(v___x_2953_, 1);
v___y_2936_ = v___y_2940_;
goto v___jp_2935_;
}
else
{
lean_object* v_a_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2961_; 
lean_dec_ref(v___y_2940_);
v_a_2954_ = lean_ctor_get(v___x_2953_, 0);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2953_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2956_ = v___x_2953_;
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_a_2954_);
lean_dec(v___x_2953_);
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
v___jp_2962_:
{
lean_object* v_ref_2967_; 
v_ref_2967_ = lean_ctor_get(v___y_2965_, 2);
lean_inc(v_ref_2967_);
v___y_2940_ = v___y_2963_;
v_stx_2941_ = v_stx_2964_;
v___y_2942_ = v___y_2965_;
v_ref_2943_ = v_ref_2967_;
v___y_2944_ = v___y_2966_;
goto v___jp_2939_;
}
v___jp_2968_:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2978_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__4, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__4_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__4);
v___x_2979_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_2978_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2973_);
lean_dec_ref(v___y_2972_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_object* v_a_2980_; 
v_a_2980_ = lean_ctor_get(v___x_2979_, 0);
lean_inc(v_a_2980_);
lean_dec_ref_known(v___x_2979_, 1);
v___y_2963_ = v___y_2969_;
v_stx_2964_ = v_a_2980_;
v___y_2965_ = v___y_2976_;
v___y_2966_ = v___y_2977_;
goto v___jp_2962_;
}
else
{
lean_object* v_a_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2988_; 
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec_ref(v___y_2969_);
lean_dec(v_tk_2900_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___boxed(lean_object** _args){
lean_object* v_tk_3648_ = _args[0];
lean_object* v___x_3649_ = _args[1];
lean_object* v___x_3650_ = _args[2];
lean_object* v___x_3651_ = _args[3];
lean_object* v___x_3652_ = _args[4];
lean_object* v___x_3653_ = _args[5];
lean_object* v___x_3654_ = _args[6];
lean_object* v___x_3655_ = _args[7];
lean_object* v_useReducible_3656_ = _args[8];
lean_object* v___f_3657_ = _args[9];
lean_object* v___x_3658_ = _args[10];
lean_object* v___x_3659_ = _args[11];
lean_object* v___x_3660_ = _args[12];
lean_object* v___x_3661_ = _args[13];
lean_object* v___x_3662_ = _args[14];
lean_object* v___x_3663_ = _args[15];
lean_object* v_usingArg_3664_ = _args[16];
lean_object* v___x_3665_ = _args[17];
lean_object* v___x_3666_ = _args[18];
lean_object* v___f_3667_ = _args[19];
lean_object* v_usingTk_x3f_3668_ = _args[20];
lean_object* v_squeeze_3669_ = _args[21];
lean_object* v_unfold_3670_ = _args[22];
lean_object* v_args_3671_ = _args[23];
lean_object* v_only_3672_ = _args[24];
lean_object* v___y_3673_ = _args[25];
lean_object* v___y_3674_ = _args[26];
lean_object* v___y_3675_ = _args[27];
lean_object* v___y_3676_ = _args[28];
lean_object* v___y_3677_ = _args[29];
lean_object* v___y_3678_ = _args[30];
lean_object* v___y_3679_ = _args[31];
lean_object* v___y_3680_ = _args[32];
lean_object* v___y_3681_ = _args[33];
lean_object* v___y_3682_ = _args[34];
_start:
{
uint8_t v___x_96791__boxed_3683_; uint8_t v_useReducible_boxed_3684_; uint8_t v___x_96802__boxed_3685_; lean_object* v_res_3686_; 
v___x_96791__boxed_3683_ = lean_unbox(v___x_3653_);
v_useReducible_boxed_3684_ = lean_unbox(v_useReducible_3656_);
v___x_96802__boxed_3685_ = lean_unbox(v___x_3666_);
v_res_3686_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7(v_tk_3648_, v___x_3649_, v___x_3650_, v___x_3651_, v___x_3652_, v___x_96791__boxed_3683_, v___x_3654_, v___x_3655_, v_useReducible_boxed_3684_, v___f_3657_, v___x_3658_, v___x_3659_, v___x_3660_, v___x_3661_, v___x_3662_, v___x_3663_, v_usingArg_3664_, v___x_3665_, v___x_96802__boxed_3685_, v___f_3667_, v_usingTk_x3f_3668_, v_squeeze_3669_, v_unfold_3670_, v_args_3671_, v_only_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_);
lean_dec(v_only_3672_);
lean_dec(v_args_3671_);
lean_dec(v_unfold_3670_);
lean_dec(v_squeeze_3669_);
lean_dec(v___x_3662_);
lean_dec(v___x_3660_);
lean_dec(v___x_3659_);
return v_res_3686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(uint8_t v_useReducible_3712_, lean_object* v_stx_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_){
_start:
{
lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; uint8_t v___x_3728_; 
v___x_3723_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4_));
v___x_3724_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0));
v___x_3725_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__1));
v___x_3726_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1));
v___x_3727_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
lean_inc(v_stx_3713_);
v___x_3728_ = l_Lean_Syntax_isOfKind(v_stx_3713_, v___x_3727_);
if (v___x_3728_ == 0)
{
lean_object* v___x_3729_; 
lean_dec(v_stx_3713_);
v___x_3729_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3729_;
}
else
{
lean_object* v___f_3730_; lean_object* v___x_3731_; lean_object* v_tk_3732_; lean_object* v___x_3733_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v___y_3737_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3742_; uint8_t v___y_3743_; lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v___y_3746_; lean_object* v___y_3747_; lean_object* v___y_3748_; lean_object* v___y_3749_; lean_object* v___y_3750_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; uint8_t v___y_3774_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v_usingTk_x3f_3787_; lean_object* v_usingArg_3788_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v___y_3806_; lean_object* v___y_3807_; uint8_t v___y_3808_; lean_object* v___y_3809_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v___y_3816_; lean_object* v___y_3817_; lean_object* v___y_3818_; lean_object* v___y_3819_; lean_object* v_args_3820_; lean_object* v___y_3832_; uint8_t v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v_only_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3851_; lean_object* v___y_3852_; lean_object* v___y_3866_; lean_object* v___y_3867_; lean_object* v___y_3868_; lean_object* v___y_3869_; lean_object* v___y_3870_; lean_object* v___y_3871_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v_unfold_3876_; lean_object* v_squeeze_3895_; lean_object* v___y_3896_; lean_object* v___y_3897_; lean_object* v___y_3898_; lean_object* v___y_3899_; lean_object* v___y_3900_; lean_object* v___y_3901_; lean_object* v___y_3902_; lean_object* v___y_3903_; lean_object* v___x_3912_; uint8_t v___x_3913_; 
v___f_3730_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3));
v___x_3731_ = lean_unsigned_to_nat(0u);
v_tk_3732_ = l_Lean_Syntax_getArg(v_stx_3713_, v___x_3731_);
v___x_3733_ = lean_unsigned_to_nat(1u);
v___x_3912_ = l_Lean_Syntax_getArg(v_stx_3713_, v___x_3733_);
v___x_3913_ = l_Lean_Syntax_isNone(v___x_3912_);
if (v___x_3913_ == 0)
{
uint8_t v___x_3914_; 
lean_inc(v___x_3912_);
v___x_3914_ = l_Lean_Syntax_matchesNull(v___x_3912_, v___x_3733_);
if (v___x_3914_ == 0)
{
lean_object* v___x_3915_; 
lean_dec(v___x_3912_);
lean_dec(v_tk_3732_);
lean_dec(v_stx_3713_);
v___x_3915_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3915_;
}
else
{
lean_object* v_squeeze_3916_; lean_object* v___x_3917_; 
v_squeeze_3916_ = l_Lean_Syntax_getArg(v___x_3912_, v___x_3731_);
lean_dec(v___x_3912_);
v___x_3917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3917_, 0, v_squeeze_3916_);
v_squeeze_3895_ = v___x_3917_;
v___y_3896_ = v_a_3714_;
v___y_3897_ = v_a_3715_;
v___y_3898_ = v_a_3716_;
v___y_3899_ = v_a_3717_;
v___y_3900_ = v_a_3718_;
v___y_3901_ = v_a_3719_;
v___y_3902_ = v_a_3720_;
v___y_3903_ = v_a_3721_;
goto v___jp_3894_;
}
}
else
{
lean_object* v___x_3918_; 
lean_dec(v___x_3912_);
v___x_3918_ = lean_box(0);
v_squeeze_3895_ = v___x_3918_;
v___y_3896_ = v_a_3714_;
v___y_3897_ = v_a_3715_;
v___y_3898_ = v_a_3716_;
v___y_3899_ = v_a_3717_;
v___y_3900_ = v_a_3718_;
v___y_3901_ = v_a_3719_;
v___y_3902_ = v_a_3720_;
v___y_3903_ = v_a_3721_;
goto v___jp_3894_;
}
v___jp_3734_:
{
lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___f_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___f_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; 
v___x_3757_ = lean_box(v___x_3728_);
v___x_3758_ = lean_box(v___y_3743_);
lean_inc(v___y_3751_);
lean_inc(v___y_3753_);
lean_inc(v___y_3756_);
lean_inc(v___y_3755_);
lean_inc(v___y_3738_);
lean_inc(v___y_3742_);
v___f_3759_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___boxed), 22, 12);
lean_closure_set(v___f_3759_, 0, v___y_3742_);
lean_closure_set(v___f_3759_, 1, v___x_3731_);
lean_closure_set(v___f_3759_, 2, v___y_3738_);
lean_closure_set(v___f_3759_, 3, v___y_3755_);
lean_closure_set(v___f_3759_, 4, v___x_3757_);
lean_closure_set(v___f_3759_, 5, v___x_3723_);
lean_closure_set(v___f_3759_, 6, v___x_3724_);
lean_closure_set(v___f_3759_, 7, v___x_3725_);
lean_closure_set(v___f_3759_, 8, v___y_3756_);
lean_closure_set(v___f_3759_, 9, v___y_3753_);
lean_closure_set(v___f_3759_, 10, v___x_3758_);
lean_closure_set(v___f_3759_, 11, v___y_3751_);
v___x_3760_ = lean_box(v___x_3728_);
v___x_3761_ = lean_box(v_useReducible_3712_);
v___x_3762_ = lean_box(v___y_3743_);
lean_inc(v___y_3739_);
lean_inc(v___y_3747_);
v___f_3763_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___boxed), 35, 26);
lean_closure_set(v___f_3763_, 0, v_tk_3732_);
lean_closure_set(v___f_3763_, 1, v___x_3723_);
lean_closure_set(v___f_3763_, 2, v___x_3724_);
lean_closure_set(v___f_3763_, 3, v___x_3725_);
lean_closure_set(v___f_3763_, 4, v___x_3731_);
lean_closure_set(v___f_3763_, 5, v___x_3760_);
lean_closure_set(v___f_3763_, 6, v___y_3747_);
lean_closure_set(v___f_3763_, 7, v___x_3727_);
lean_closure_set(v___f_3763_, 8, v___x_3761_);
lean_closure_set(v___f_3763_, 9, v___f_3730_);
lean_closure_set(v___f_3763_, 10, v___x_3726_);
lean_closure_set(v___f_3763_, 11, v___y_3752_);
lean_closure_set(v___f_3763_, 12, v___y_3750_);
lean_closure_set(v___f_3763_, 13, v___x_3733_);
lean_closure_set(v___f_3763_, 14, v___y_3739_);
lean_closure_set(v___f_3763_, 15, v___y_3736_);
lean_closure_set(v___f_3763_, 16, v___y_3740_);
lean_closure_set(v___f_3763_, 17, v___y_3742_);
lean_closure_set(v___f_3763_, 18, v___x_3762_);
lean_closure_set(v___f_3763_, 19, v___f_3759_);
lean_closure_set(v___f_3763_, 20, v___y_3744_);
lean_closure_set(v___f_3763_, 21, v___y_3751_);
lean_closure_set(v___f_3763_, 22, v___y_3753_);
lean_closure_set(v___f_3763_, 23, v___y_3738_);
lean_closure_set(v___f_3763_, 24, v___y_3755_);
lean_closure_set(v___f_3763_, 25, v___y_3756_);
v___x_3764_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_3764_, 0, v___f_3763_);
v___x_3765_ = l_Lean_Elab_Tactic_focus___redArg(v___x_3764_, v___y_3749_, v___y_3754_, v___y_3745_, v___y_3748_, v___y_3746_, v___y_3737_, v___y_3735_, v___y_3741_);
return v___x_3765_;
}
v___jp_3766_:
{
lean_object* v___x_3789_; 
v___x_3789_ = l_Lean_Syntax_getOptional_x3f(v___y_3784_);
lean_dec(v___y_3784_);
if (lean_obj_tag(v___x_3789_) == 0)
{
lean_object* v___x_3790_; 
v___x_3790_ = lean_box(0);
v___y_3735_ = v___y_3767_;
v___y_3736_ = v___y_3768_;
v___y_3737_ = v___y_3769_;
v___y_3738_ = v___y_3770_;
v___y_3739_ = v___y_3771_;
v___y_3740_ = v_usingArg_3788_;
v___y_3741_ = v___y_3772_;
v___y_3742_ = v___y_3773_;
v___y_3743_ = v___y_3774_;
v___y_3744_ = v_usingTk_x3f_3787_;
v___y_3745_ = v___y_3775_;
v___y_3746_ = v___y_3776_;
v___y_3747_ = v___y_3777_;
v___y_3748_ = v___y_3778_;
v___y_3749_ = v___y_3779_;
v___y_3750_ = v___y_3780_;
v___y_3751_ = v___y_3782_;
v___y_3752_ = v___y_3781_;
v___y_3753_ = v___y_3783_;
v___y_3754_ = v___y_3785_;
v___y_3755_ = v___y_3786_;
v___y_3756_ = v___x_3790_;
goto v___jp_3734_;
}
else
{
lean_object* v_val_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3798_; 
v_val_3791_ = lean_ctor_get(v___x_3789_, 0);
v_isSharedCheck_3798_ = !lean_is_exclusive(v___x_3789_);
if (v_isSharedCheck_3798_ == 0)
{
v___x_3793_ = v___x_3789_;
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_val_3791_);
lean_dec(v___x_3789_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v___x_3796_; 
if (v_isShared_3794_ == 0)
{
v___x_3796_ = v___x_3793_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v_val_3791_);
v___x_3796_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
v___y_3735_ = v___y_3767_;
v___y_3736_ = v___y_3768_;
v___y_3737_ = v___y_3769_;
v___y_3738_ = v___y_3770_;
v___y_3739_ = v___y_3771_;
v___y_3740_ = v_usingArg_3788_;
v___y_3741_ = v___y_3772_;
v___y_3742_ = v___y_3773_;
v___y_3743_ = v___y_3774_;
v___y_3744_ = v_usingTk_x3f_3787_;
v___y_3745_ = v___y_3775_;
v___y_3746_ = v___y_3776_;
v___y_3747_ = v___y_3777_;
v___y_3748_ = v___y_3778_;
v___y_3749_ = v___y_3779_;
v___y_3750_ = v___y_3780_;
v___y_3751_ = v___y_3782_;
v___y_3752_ = v___y_3781_;
v___y_3753_ = v___y_3783_;
v___y_3754_ = v___y_3785_;
v___y_3755_ = v___y_3786_;
v___y_3756_ = v___x_3796_;
goto v___jp_3734_;
}
}
}
}
v___jp_3799_:
{
lean_object* v___x_3821_; lean_object* v___x_3822_; uint8_t v___x_3823_; 
v___x_3821_ = lean_unsigned_to_nat(4u);
v___x_3822_ = l_Lean_Syntax_getArg(v___y_3800_, v___x_3821_);
lean_dec(v___y_3800_);
v___x_3823_ = l_Lean_Syntax_isNone(v___x_3822_);
if (v___x_3823_ == 0)
{
uint8_t v___x_3824_; 
lean_inc(v___x_3822_);
v___x_3824_ = l_Lean_Syntax_matchesNull(v___x_3822_, v___y_3802_);
lean_dec(v___y_3802_);
if (v___x_3824_ == 0)
{
lean_object* v___x_3825_; 
lean_dec(v___x_3822_);
lean_dec(v_args_3820_);
lean_dec(v___y_3819_);
lean_dec(v___y_3818_);
lean_dec(v___y_3816_);
lean_dec(v___y_3815_);
lean_dec(v___y_3814_);
lean_dec(v___y_3807_);
lean_dec(v___y_3803_);
lean_dec(v_tk_3732_);
v___x_3825_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3825_;
}
else
{
lean_object* v_usingTk_x3f_3826_; lean_object* v_usingArg_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; 
v_usingTk_x3f_3826_ = l_Lean_Syntax_getArg(v___x_3822_, v___x_3731_);
v_usingArg_3827_ = l_Lean_Syntax_getArg(v___x_3822_, v___x_3733_);
lean_dec(v___x_3822_);
v___x_3828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3828_, 0, v_usingTk_x3f_3826_);
v___x_3829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3829_, 0, v_usingArg_3827_);
v___y_3767_ = v___y_3801_;
v___y_3768_ = v___y_3803_;
v___y_3769_ = v___y_3804_;
v___y_3770_ = v_args_3820_;
v___y_3771_ = v___y_3805_;
v___y_3772_ = v___y_3806_;
v___y_3773_ = v___y_3807_;
v___y_3774_ = v___y_3808_;
v___y_3775_ = v___y_3809_;
v___y_3776_ = v___y_3810_;
v___y_3777_ = v___y_3811_;
v___y_3778_ = v___y_3812_;
v___y_3779_ = v___y_3813_;
v___y_3780_ = v___y_3814_;
v___y_3781_ = v___x_3821_;
v___y_3782_ = v___y_3815_;
v___y_3783_ = v___y_3816_;
v___y_3784_ = v___y_3818_;
v___y_3785_ = v___y_3817_;
v___y_3786_ = v___y_3819_;
v_usingTk_x3f_3787_ = v___x_3828_;
v_usingArg_3788_ = v___x_3829_;
goto v___jp_3766_;
}
}
else
{
lean_object* v___x_3830_; 
lean_dec(v___x_3822_);
lean_dec(v___y_3802_);
v___x_3830_ = lean_box(0);
v___y_3767_ = v___y_3801_;
v___y_3768_ = v___y_3803_;
v___y_3769_ = v___y_3804_;
v___y_3770_ = v_args_3820_;
v___y_3771_ = v___y_3805_;
v___y_3772_ = v___y_3806_;
v___y_3773_ = v___y_3807_;
v___y_3774_ = v___y_3808_;
v___y_3775_ = v___y_3809_;
v___y_3776_ = v___y_3810_;
v___y_3777_ = v___y_3811_;
v___y_3778_ = v___y_3812_;
v___y_3779_ = v___y_3813_;
v___y_3780_ = v___y_3814_;
v___y_3781_ = v___x_3821_;
v___y_3782_ = v___y_3815_;
v___y_3783_ = v___y_3816_;
v___y_3784_ = v___y_3818_;
v___y_3785_ = v___y_3817_;
v___y_3786_ = v___y_3819_;
v_usingTk_x3f_3787_ = v___x_3830_;
v_usingArg_3788_ = v___x_3830_;
goto v___jp_3766_;
}
}
v___jp_3831_:
{
lean_object* v___x_3853_; uint8_t v___x_3854_; 
v___x_3853_ = l_Lean_Syntax_getArg(v___y_3841_, v___y_3842_);
lean_dec(v___y_3842_);
v___x_3854_ = l_Lean_Syntax_isNone(v___x_3853_);
if (v___x_3854_ == 0)
{
uint8_t v___x_3855_; 
lean_inc(v___x_3853_);
v___x_3855_ = l_Lean_Syntax_matchesNull(v___x_3853_, v___x_3733_);
if (v___x_3855_ == 0)
{
lean_object* v___x_3856_; 
lean_dec(v___x_3853_);
lean_dec(v_only_3844_);
lean_dec(v___y_3843_);
lean_dec(v___y_3841_);
lean_dec(v___y_3840_);
lean_dec(v___y_3838_);
lean_dec(v___y_3837_);
lean_dec(v___y_3836_);
lean_dec(v___y_3835_);
lean_dec(v___y_3832_);
lean_dec(v_tk_3732_);
v___x_3856_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3856_;
}
else
{
lean_object* v___x_3857_; lean_object* v___x_3858_; uint8_t v___x_3859_; 
v___x_3857_ = l_Lean_Syntax_getArg(v___x_3853_, v___x_3731_);
lean_dec(v___x_3853_);
v___x_3858_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
lean_inc(v___x_3857_);
v___x_3859_ = l_Lean_Syntax_isOfKind(v___x_3857_, v___x_3858_);
if (v___x_3859_ == 0)
{
lean_object* v___x_3860_; 
lean_dec(v___x_3857_);
lean_dec(v_only_3844_);
lean_dec(v___y_3843_);
lean_dec(v___y_3841_);
lean_dec(v___y_3840_);
lean_dec(v___y_3838_);
lean_dec(v___y_3837_);
lean_dec(v___y_3836_);
lean_dec(v___y_3835_);
lean_dec(v___y_3832_);
lean_dec(v_tk_3732_);
v___x_3860_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3860_;
}
else
{
lean_object* v___x_3861_; lean_object* v_args_3862_; lean_object* v___x_3863_; 
v___x_3861_ = l_Lean_Syntax_getArg(v___x_3857_, v___x_3733_);
lean_dec(v___x_3857_);
v_args_3862_ = l_Lean_Syntax_getArgs(v___x_3861_);
lean_dec(v___x_3861_);
v___x_3863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3863_, 0, v_args_3862_);
v___y_3800_ = v___y_3841_;
v___y_3801_ = v___y_3851_;
v___y_3802_ = v___y_3843_;
v___y_3803_ = v___y_3838_;
v___y_3804_ = v___y_3850_;
v___y_3805_ = v___y_3839_;
v___y_3806_ = v___y_3852_;
v___y_3807_ = v___y_3832_;
v___y_3808_ = v___y_3833_;
v___y_3809_ = v___y_3847_;
v___y_3810_ = v___y_3849_;
v___y_3811_ = v___y_3834_;
v___y_3812_ = v___y_3848_;
v___y_3813_ = v___y_3845_;
v___y_3814_ = v___y_3835_;
v___y_3815_ = v___y_3836_;
v___y_3816_ = v___y_3837_;
v___y_3817_ = v___y_3846_;
v___y_3818_ = v___y_3840_;
v___y_3819_ = v_only_3844_;
v_args_3820_ = v___x_3863_;
goto v___jp_3799_;
}
}
}
else
{
lean_object* v___x_3864_; 
lean_dec(v___x_3853_);
v___x_3864_ = lean_box(0);
v___y_3800_ = v___y_3841_;
v___y_3801_ = v___y_3851_;
v___y_3802_ = v___y_3843_;
v___y_3803_ = v___y_3838_;
v___y_3804_ = v___y_3850_;
v___y_3805_ = v___y_3839_;
v___y_3806_ = v___y_3852_;
v___y_3807_ = v___y_3832_;
v___y_3808_ = v___y_3833_;
v___y_3809_ = v___y_3847_;
v___y_3810_ = v___y_3849_;
v___y_3811_ = v___y_3834_;
v___y_3812_ = v___y_3848_;
v___y_3813_ = v___y_3845_;
v___y_3814_ = v___y_3835_;
v___y_3815_ = v___y_3836_;
v___y_3816_ = v___y_3837_;
v___y_3817_ = v___y_3846_;
v___y_3818_ = v___y_3840_;
v___y_3819_ = v_only_3844_;
v_args_3820_ = v___x_3864_;
goto v___jp_3799_;
}
}
v___jp_3865_:
{
lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; uint8_t v___x_3880_; 
v___x_3877_ = lean_unsigned_to_nat(3u);
v___x_3878_ = l_Lean_Syntax_getArg(v_stx_3713_, v___x_3877_);
lean_dec(v_stx_3713_);
v___x_3879_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6));
lean_inc(v___x_3878_);
v___x_3880_ = l_Lean_Syntax_isOfKind(v___x_3878_, v___x_3879_);
if (v___x_3880_ == 0)
{
lean_object* v___x_3881_; 
lean_dec(v___x_3878_);
lean_dec(v_unfold_3876_);
lean_dec(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec(v_tk_3732_);
v___x_3881_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3881_;
}
else
{
lean_object* v___x_3882_; lean_object* v___x_3883_; uint8_t v___x_3884_; 
v___x_3882_ = l_Lean_Syntax_getArg(v___x_3878_, v___x_3731_);
v___x_3883_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8));
lean_inc(v___x_3882_);
v___x_3884_ = l_Lean_Syntax_isOfKind(v___x_3882_, v___x_3883_);
if (v___x_3884_ == 0)
{
lean_object* v___x_3885_; 
lean_dec(v___x_3882_);
lean_dec(v___x_3878_);
lean_dec(v_unfold_3876_);
lean_dec(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec(v_tk_3732_);
v___x_3885_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3885_;
}
else
{
lean_object* v___x_3886_; lean_object* v___x_3887_; uint8_t v___x_3888_; 
v___x_3886_ = l_Lean_Syntax_getArg(v___x_3878_, v___x_3733_);
v___x_3887_ = l_Lean_Syntax_getArg(v___x_3878_, v___y_3873_);
v___x_3888_ = l_Lean_Syntax_isNone(v___x_3887_);
if (v___x_3888_ == 0)
{
uint8_t v___x_3889_; 
lean_inc(v___x_3887_);
v___x_3889_ = l_Lean_Syntax_matchesNull(v___x_3887_, v___x_3733_);
if (v___x_3889_ == 0)
{
lean_object* v___x_3890_; 
lean_dec(v___x_3887_);
lean_dec(v___x_3886_);
lean_dec(v___x_3882_);
lean_dec(v___x_3878_);
lean_dec(v_unfold_3876_);
lean_dec(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec(v_tk_3732_);
v___x_3890_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3890_;
}
else
{
lean_object* v_only_3891_; lean_object* v___x_3892_; 
v_only_3891_ = l_Lean_Syntax_getArg(v___x_3887_, v___x_3731_);
lean_dec(v___x_3887_);
v___x_3892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3892_, 0, v_only_3891_);
lean_inc(v___y_3873_);
v___y_3832_ = v___x_3882_;
v___y_3833_ = v___x_3880_;
v___y_3834_ = v___x_3879_;
v___y_3835_ = v___x_3877_;
v___y_3836_ = v___y_3872_;
v___y_3837_ = v_unfold_3876_;
v___y_3838_ = v___y_3873_;
v___y_3839_ = v___x_3883_;
v___y_3840_ = v___x_3886_;
v___y_3841_ = v___x_3878_;
v___y_3842_ = v___x_3877_;
v___y_3843_ = v___y_3873_;
v_only_3844_ = v___x_3892_;
v___y_3845_ = v___y_3870_;
v___y_3846_ = v___y_3866_;
v___y_3847_ = v___y_3869_;
v___y_3848_ = v___y_3871_;
v___y_3849_ = v___y_3868_;
v___y_3850_ = v___y_3867_;
v___y_3851_ = v___y_3875_;
v___y_3852_ = v___y_3874_;
goto v___jp_3831_;
}
}
else
{
lean_object* v___x_3893_; 
lean_dec(v___x_3887_);
v___x_3893_ = lean_box(0);
lean_inc(v___y_3873_);
v___y_3832_ = v___x_3882_;
v___y_3833_ = v___x_3880_;
v___y_3834_ = v___x_3879_;
v___y_3835_ = v___x_3877_;
v___y_3836_ = v___y_3872_;
v___y_3837_ = v_unfold_3876_;
v___y_3838_ = v___y_3873_;
v___y_3839_ = v___x_3883_;
v___y_3840_ = v___x_3886_;
v___y_3841_ = v___x_3878_;
v___y_3842_ = v___x_3877_;
v___y_3843_ = v___y_3873_;
v_only_3844_ = v___x_3893_;
v___y_3845_ = v___y_3870_;
v___y_3846_ = v___y_3866_;
v___y_3847_ = v___y_3869_;
v___y_3848_ = v___y_3871_;
v___y_3849_ = v___y_3868_;
v___y_3850_ = v___y_3867_;
v___y_3851_ = v___y_3875_;
v___y_3852_ = v___y_3874_;
goto v___jp_3831_;
}
}
}
}
v___jp_3894_:
{
lean_object* v___x_3904_; lean_object* v___x_3905_; uint8_t v___x_3906_; 
v___x_3904_ = lean_unsigned_to_nat(2u);
v___x_3905_ = l_Lean_Syntax_getArg(v_stx_3713_, v___x_3904_);
v___x_3906_ = l_Lean_Syntax_isNone(v___x_3905_);
if (v___x_3906_ == 0)
{
uint8_t v___x_3907_; 
lean_inc(v___x_3905_);
v___x_3907_ = l_Lean_Syntax_matchesNull(v___x_3905_, v___x_3733_);
if (v___x_3907_ == 0)
{
lean_object* v___x_3908_; 
lean_dec(v___x_3905_);
lean_dec(v_squeeze_3895_);
lean_dec(v_tk_3732_);
lean_dec(v_stx_3713_);
v___x_3908_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3908_;
}
else
{
lean_object* v_unfold_3909_; lean_object* v___x_3910_; 
v_unfold_3909_ = l_Lean_Syntax_getArg(v___x_3905_, v___x_3731_);
lean_dec(v___x_3905_);
v___x_3910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3910_, 0, v_unfold_3909_);
v___y_3866_ = v___y_3897_;
v___y_3867_ = v___y_3901_;
v___y_3868_ = v___y_3900_;
v___y_3869_ = v___y_3898_;
v___y_3870_ = v___y_3896_;
v___y_3871_ = v___y_3899_;
v___y_3872_ = v_squeeze_3895_;
v___y_3873_ = v___x_3904_;
v___y_3874_ = v___y_3903_;
v___y_3875_ = v___y_3902_;
v_unfold_3876_ = v___x_3910_;
goto v___jp_3865_;
}
}
else
{
lean_object* v___x_3911_; 
lean_dec(v___x_3905_);
v___x_3911_ = lean_box(0);
v___y_3866_ = v___y_3897_;
v___y_3867_ = v___y_3901_;
v___y_3868_ = v___y_3900_;
v___y_3869_ = v___y_3898_;
v___y_3870_ = v___y_3896_;
v___y_3871_ = v___y_3899_;
v___y_3872_ = v_squeeze_3895_;
v___y_3873_ = v___x_3904_;
v___y_3874_ = v___y_3903_;
v___y_3875_ = v___y_3902_;
v_unfold_3876_ = v___x_3911_;
goto v___jp_3865_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___boxed(lean_object* v_useReducible_3919_, lean_object* v_stx_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_){
_start:
{
uint8_t v_useReducible_boxed_3930_; lean_object* v_res_3931_; 
v_useReducible_boxed_3930_ = lean_unbox(v_useReducible_3919_);
v_res_3931_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v_useReducible_boxed_3930_, v_stx_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_);
lean_dec(v_a_3928_);
lean_dec_ref(v_a_3927_);
lean_dec(v_a_3926_);
lean_dec_ref(v_a_3925_);
lean_dec(v_a_3924_);
lean_dec_ref(v_a_3923_);
lean_dec(v_a_3922_);
lean_dec_ref(v_a_3921_);
return v_res_3931_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(lean_object* v_mvarId_3932_, lean_object* v_val_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_){
_start:
{
lean_object* v___x_3943_; 
v___x_3943_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___redArg(v_mvarId_3932_, v_val_3933_, v___y_3939_);
return v___x_3943_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___boxed(lean_object* v_mvarId_3944_, lean_object* v_val_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_){
_start:
{
lean_object* v_res_3955_; 
v_res_3955_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(v_mvarId_3944_, v_val_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_);
lean_dec(v___y_3953_);
lean_dec_ref(v___y_3952_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
return v_res_3955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3(lean_object* v_o_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_){
_start:
{
lean_object* v___x_3966_; 
v___x_3966_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(v_o_3956_, v___y_3964_);
return v___x_3966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___boxed(lean_object* v_o_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_){
_start:
{
lean_object* v_res_3977_; 
v_res_3977_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3(v_o_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_);
lean_dec(v___y_3975_);
lean_dec_ref(v___y_3974_);
lean_dec(v___y_3973_);
lean_dec_ref(v___y_3972_);
lean_dec(v___y_3971_);
lean_dec_ref(v___y_3970_);
lean_dec(v___y_3969_);
lean_dec_ref(v___y_3968_);
return v_res_3977_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5(lean_object* v_00_u03b1_3978_, lean_object* v_msg_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_){
_start:
{
lean_object* v___x_3989_; 
v___x_3989_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_msg_3979_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
return v___x_3989_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___boxed(lean_object* v_00_u03b1_3990_, lean_object* v_msg_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_){
_start:
{
lean_object* v_res_4001_; 
v_res_4001_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5(v_00_u03b1_3990_, v_msg_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_);
lean_dec(v___y_3999_);
lean_dec_ref(v___y_3998_);
lean_dec(v___y_3997_);
lean_dec_ref(v___y_3996_);
lean_dec(v___y_3995_);
lean_dec_ref(v___y_3994_);
lean_dec(v___y_3993_);
lean_dec_ref(v___y_3992_);
return v_res_4001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7(lean_object* v_00_u03b1_4002_, lean_object* v_x_4003_, lean_object* v_mkInfoTree_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_){
_start:
{
lean_object* v___x_4014_; 
v___x_4014_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v_x_4003_, v_mkInfoTree_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_);
return v___x_4014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___boxed(lean_object* v_00_u03b1_4015_, lean_object* v_x_4016_, lean_object* v_mkInfoTree_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_){
_start:
{
lean_object* v_res_4027_; 
v_res_4027_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7(v_00_u03b1_4015_, v_x_4016_, v_mkInfoTree_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_);
lean_dec(v___y_4025_);
lean_dec_ref(v___y_4024_);
lean_dec(v___y_4023_);
lean_dec_ref(v___y_4022_);
lean_dec(v___y_4021_);
lean_dec_ref(v___y_4020_);
lean_dec(v___y_4019_);
lean_dec_ref(v___y_4018_);
return v_res_4027_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(lean_object* v_00_u03b2_4028_, lean_object* v_x_4029_, lean_object* v_x_4030_, lean_object* v_x_4031_){
_start:
{
lean_object* v___x_4032_; 
v___x_4032_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1___redArg(v_x_4029_, v_x_4030_, v_x_4031_);
return v___x_4032_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5(lean_object* v_00_u03b2_4033_, lean_object* v_x_4034_, size_t v_x_4035_, size_t v_x_4036_, lean_object* v_x_4037_, lean_object* v_x_4038_){
_start:
{
lean_object* v___x_4039_; 
v___x_4039_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(v_x_4034_, v_x_4035_, v_x_4036_, v_x_4037_, v_x_4038_);
return v___x_4039_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___boxed(lean_object* v_00_u03b2_4040_, lean_object* v_x_4041_, lean_object* v_x_4042_, lean_object* v_x_4043_, lean_object* v_x_4044_, lean_object* v_x_4045_){
_start:
{
size_t v_x_98953__boxed_4046_; size_t v_x_98954__boxed_4047_; lean_object* v_res_4048_; 
v_x_98953__boxed_4046_ = lean_unbox_usize(v_x_4042_);
lean_dec(v_x_4042_);
v_x_98954__boxed_4047_ = lean_unbox_usize(v_x_4043_);
lean_dec(v_x_4043_);
v_res_4048_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5(v_00_u03b2_4040_, v_x_4041_, v_x_98953__boxed_4046_, v_x_98954__boxed_4047_, v_x_4044_, v_x_4045_);
return v_res_4048_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10(lean_object* v_00_u03b2_4049_, lean_object* v_m_4050_, lean_object* v_a_4051_){
_start:
{
uint8_t v___x_4052_; 
v___x_4052_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10___redArg(v_m_4050_, v_a_4051_);
return v___x_4052_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10___boxed(lean_object* v_00_u03b2_4053_, lean_object* v_m_4054_, lean_object* v_a_4055_){
_start:
{
uint8_t v_res_4056_; lean_object* v_r_4057_; 
v_res_4056_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10(v_00_u03b2_4053_, v_m_4054_, v_a_4055_);
lean_dec_ref(v_a_4055_);
lean_dec_ref(v_m_4054_);
v_r_4057_ = lean_box(v_res_4056_);
return v_r_4057_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11(lean_object* v_00_u03b2_4058_, lean_object* v_m_4059_, lean_object* v_a_4060_, lean_object* v_b_4061_){
_start:
{
lean_object* v___x_4062_; 
v___x_4062_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11___redArg(v_m_4059_, v_a_4060_, v_b_4061_);
return v___x_4062_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19(lean_object* v_mvarId_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_){
_start:
{
lean_object* v___x_4074_; 
v___x_4074_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19___redArg(v_mvarId_4063_, v___y_4064_, v___y_4070_);
return v___x_4074_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19___boxed(lean_object* v_mvarId_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_){
_start:
{
lean_object* v_res_4086_; 
v_res_4086_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19(v_mvarId_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_);
lean_dec(v___y_4084_);
lean_dec_ref(v___y_4083_);
lean_dec(v___y_4082_);
lean_dec_ref(v___y_4081_);
lean_dec(v___y_4080_);
lean_dec_ref(v___y_4079_);
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
lean_dec(v_mvarId_4075_);
return v_res_4086_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20(lean_object* v_mvarId_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_){
_start:
{
lean_object* v___x_4098_; 
v___x_4098_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20___redArg(v_mvarId_4087_, v___y_4088_, v___y_4094_);
return v___x_4098_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20___boxed(lean_object* v_mvarId_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_){
_start:
{
lean_object* v_res_4110_; 
v_res_4110_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20(v_mvarId_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_);
lean_dec(v___y_4108_);
lean_dec_ref(v___y_4107_);
lean_dec(v___y_4106_);
lean_dec_ref(v___y_4105_);
lean_dec(v___y_4104_);
lean_dec_ref(v___y_4103_);
lean_dec(v___y_4102_);
lean_dec_ref(v___y_4101_);
lean_dec(v_mvarId_4099_);
return v_res_4110_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11(lean_object* v_00_u03b2_4111_, lean_object* v_n_4112_, lean_object* v_k_4113_, lean_object* v_v_4114_){
_start:
{
lean_object* v___x_4115_; 
v___x_4115_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___redArg(v_n_4112_, v_k_4113_, v_v_4114_);
return v___x_4115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12(lean_object* v_00_u03b2_4116_, size_t v_depth_4117_, lean_object* v_keys_4118_, lean_object* v_vals_4119_, lean_object* v_heq_4120_, lean_object* v_i_4121_, lean_object* v_entries_4122_){
_start:
{
lean_object* v___x_4123_; 
v___x_4123_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12___redArg(v_depth_4117_, v_keys_4118_, v_vals_4119_, v_i_4121_, v_entries_4122_);
return v___x_4123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12___boxed(lean_object* v_00_u03b2_4124_, lean_object* v_depth_4125_, lean_object* v_keys_4126_, lean_object* v_vals_4127_, lean_object* v_heq_4128_, lean_object* v_i_4129_, lean_object* v_entries_4130_){
_start:
{
size_t v_depth_boxed_4131_; lean_object* v_res_4132_; 
v_depth_boxed_4131_ = lean_unbox_usize(v_depth_4125_);
lean_dec(v_depth_4125_);
v_res_4132_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12(v_00_u03b2_4124_, v_depth_boxed_4131_, v_keys_4126_, v_vals_4127_, v_heq_4128_, v_i_4129_, v_entries_4130_);
lean_dec_ref(v_vals_4127_);
lean_dec_ref(v_keys_4126_);
return v_res_4132_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15(lean_object* v_00_u03b2_4133_, lean_object* v_a_4134_, lean_object* v_x_4135_){
_start:
{
uint8_t v___x_4136_; 
v___x_4136_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___redArg(v_a_4134_, v_x_4135_);
return v___x_4136_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___boxed(lean_object* v_00_u03b2_4137_, lean_object* v_a_4138_, lean_object* v_x_4139_){
_start:
{
uint8_t v_res_4140_; lean_object* v_r_4141_; 
v_res_4140_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15(v_00_u03b2_4137_, v_a_4138_, v_x_4139_);
lean_dec(v_x_4139_);
lean_dec_ref(v_a_4138_);
v_r_4141_ = lean_box(v_res_4140_);
return v_r_4141_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17(lean_object* v_00_u03b2_4142_, lean_object* v_data_4143_){
_start:
{
lean_object* v___x_4144_; 
v___x_4144_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17___redArg(v_data_4143_);
return v___x_4144_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11_spec__13(lean_object* v_00_u03b2_4145_, lean_object* v_x_4146_, lean_object* v_x_4147_, lean_object* v_x_4148_, lean_object* v_x_4149_){
_start:
{
lean_object* v___x_4150_; 
v___x_4150_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11_spec__13___redArg(v_x_4146_, v_x_4147_, v_x_4148_, v_x_4149_);
return v___x_4150_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19(lean_object* v_00_u03b2_4151_, lean_object* v_i_4152_, lean_object* v_source_4153_, lean_object* v_target_4154_){
_start:
{
lean_object* v___x_4155_; 
v___x_4155_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19___redArg(v_i_4152_, v_source_4153_, v_target_4154_);
return v___x_4155_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19_spec__23(lean_object* v_00_u03b2_4156_, lean_object* v_x_4157_, lean_object* v_x_4158_){
_start:
{
lean_object* v___x_4159_; 
v___x_4159_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19_spec__23___redArg(v_x_4157_, v_x_4158_);
return v___x_4159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa(lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_){
_start:
{
uint8_t v___x_4170_; lean_object* v___x_4171_; 
v___x_4170_ = 1;
v___x_4171_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v___x_4170_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
return v___x_4171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed(lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_){
_start:
{
lean_object* v_res_4182_; 
v_res_4182_ = l_Lean_Elab_Tactic_Simpa_evalSimpa(v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_, v_a_4180_);
lean_dec(v_a_4180_);
lean_dec_ref(v_a_4179_);
lean_dec(v_a_4178_);
lean_dec_ref(v_a_4177_);
lean_dec(v_a_4176_);
lean_dec_ref(v_a_4175_);
lean_dec(v_a_4174_);
lean_dec_ref(v_a_4173_);
return v_res_4182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1(){
_start:
{
lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; 
v___x_4192_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4193_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
v___x_4194_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2));
v___x_4195_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed), 10, 0);
v___x_4196_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4192_, v___x_4193_, v___x_4194_, v___x_4195_);
return v___x_4196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___boxed(lean_object* v_a_4197_){
_start:
{
lean_object* v_res_4198_; 
v_res_4198_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1();
return v_res_4198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3(){
_start:
{
lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; 
v___x_4225_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2));
v___x_4226_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6));
v___x_4227_ = l_Lean_addBuiltinDeclarationRanges(v___x_4225_, v___x_4226_);
return v___x_4227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___boxed(lean_object* v_a_4228_){
_start:
{
lean_object* v_res_4229_; 
v_res_4229_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3();
return v_res_4229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(lean_object* v_x_4232_){
_start:
{
lean_object* v___x_4233_; 
v___x_4233_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
return v___x_4233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___boxed(lean_object* v_x_4234_){
_start:
{
lean_object* v_res_4235_; 
v_res_4235_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v_x_4234_);
lean_dec(v_x_4234_);
return v_res_4235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang(lean_object* v_stx_4247_, lean_object* v_a_4248_, lean_object* v_a_4249_, lean_object* v_a_4250_, lean_object* v_a_4251_, lean_object* v_a_4252_, lean_object* v_a_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_){
_start:
{
lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v___y_4268_; lean_object* v___y_4269_; uint8_t v___y_4270_; lean_object* v___y_4271_; lean_object* v___y_4272_; lean_object* v___y_4273_; lean_object* v___y_4274_; lean_object* v___y_4275_; lean_object* v___y_4276_; lean_object* v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___x_4288_; uint8_t v___x_4289_; 
v___x_4288_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0));
lean_inc(v_stx_4247_);
v___x_4289_ = l_Lean_Syntax_isOfKind(v_stx_4247_, v___x_4288_);
if (v___x_4289_ == 0)
{
lean_object* v___x_4290_; 
lean_dec(v_stx_4247_);
v___x_4290_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4290_;
}
else
{
lean_object* v___x_4291_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4297_; lean_object* v___y_4298_; lean_object* v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v___y_4303_; lean_object* v___y_4304_; lean_object* v___y_4305_; uint8_t v___y_4306_; lean_object* v___y_4307_; lean_object* v___y_4308_; lean_object* v___y_4309_; lean_object* v___y_4310_; lean_object* v___y_4311_; lean_object* v___y_4312_; lean_object* v___y_4313_; lean_object* v___y_4314_; lean_object* v___y_4329_; lean_object* v___y_4330_; lean_object* v___y_4331_; lean_object* v___y_4332_; lean_object* v___y_4333_; lean_object* v___y_4334_; lean_object* v___y_4335_; lean_object* v___y_4336_; lean_object* v___y_4337_; lean_object* v___y_4338_; lean_object* v___y_4339_; lean_object* v___y_4340_; lean_object* v___y_4341_; uint8_t v___y_4342_; lean_object* v___y_4343_; lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v___y_4346_; lean_object* v___y_4347_; lean_object* v___y_4348_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v___y_4360_; lean_object* v___y_4361_; lean_object* v___y_4362_; lean_object* v___y_4363_; lean_object* v___y_4364_; lean_object* v___y_4365_; lean_object* v___y_4366_; lean_object* v___y_4367_; lean_object* v___y_4368_; lean_object* v___y_4369_; lean_object* v___y_4370_; lean_object* v___y_4371_; uint8_t v___y_4372_; lean_object* v___y_4373_; lean_object* v___y_4374_; lean_object* v___y_4375_; lean_object* v___y_4376_; lean_object* v___y_4377_; lean_object* v___y_4378_; lean_object* v___y_4379_; lean_object* v___y_4380_; lean_object* v___y_4389_; lean_object* v___y_4390_; lean_object* v___y_4391_; lean_object* v___y_4392_; lean_object* v___y_4393_; lean_object* v___y_4394_; lean_object* v___y_4395_; lean_object* v___y_4396_; lean_object* v___y_4397_; lean_object* v___y_4398_; lean_object* v___y_4399_; lean_object* v___y_4400_; uint8_t v___y_4401_; lean_object* v___y_4402_; lean_object* v___y_4403_; lean_object* v___y_4404_; lean_object* v___y_4405_; lean_object* v___y_4406_; lean_object* v___y_4407_; lean_object* v___y_4408_; lean_object* v___y_4409_; lean_object* v_tk_4418_; lean_object* v___y_4420_; lean_object* v___y_4421_; lean_object* v___y_4422_; lean_object* v___y_4423_; lean_object* v___y_4424_; lean_object* v___y_4425_; lean_object* v___y_4426_; lean_object* v___y_4427_; lean_object* v___y_4428_; lean_object* v___y_4429_; lean_object* v___y_4430_; lean_object* v___y_4431_; lean_object* v___y_4432_; lean_object* v___y_4433_; lean_object* v___y_4434_; lean_object* v___y_4451_; lean_object* v___y_4452_; lean_object* v___y_4453_; lean_object* v___y_4454_; lean_object* v___y_4455_; lean_object* v___y_4456_; lean_object* v_args_4457_; lean_object* v___y_4458_; lean_object* v___y_4459_; lean_object* v___y_4460_; lean_object* v___y_4461_; lean_object* v___y_4462_; lean_object* v___y_4463_; lean_object* v___y_4464_; lean_object* v___y_4465_; lean_object* v___x_4478_; lean_object* v___y_4480_; lean_object* v___y_4481_; lean_object* v___y_4482_; lean_object* v___y_4483_; lean_object* v___y_4484_; lean_object* v___y_4485_; lean_object* v_only_4486_; lean_object* v___y_4487_; lean_object* v___y_4488_; lean_object* v___y_4489_; lean_object* v___y_4490_; lean_object* v___y_4491_; lean_object* v___y_4492_; lean_object* v___y_4493_; lean_object* v___y_4494_; lean_object* v___y_4508_; lean_object* v___y_4509_; lean_object* v_unfold_4510_; lean_object* v___y_4511_; lean_object* v___y_4512_; lean_object* v___y_4513_; lean_object* v___y_4514_; lean_object* v___y_4515_; lean_object* v___y_4516_; lean_object* v___y_4517_; lean_object* v___y_4518_; lean_object* v_squeeze_4537_; lean_object* v___y_4538_; lean_object* v___y_4539_; lean_object* v___y_4540_; lean_object* v___y_4541_; lean_object* v___y_4542_; lean_object* v___y_4543_; lean_object* v___y_4544_; lean_object* v___y_4545_; lean_object* v___x_4554_; uint8_t v___x_4555_; 
v___x_4291_ = lean_unsigned_to_nat(0u);
v_tk_4418_ = l_Lean_Syntax_getArg(v_stx_4247_, v___x_4291_);
v___x_4478_ = lean_unsigned_to_nat(1u);
v___x_4554_ = l_Lean_Syntax_getArg(v_stx_4247_, v___x_4478_);
v___x_4555_ = l_Lean_Syntax_isNone(v___x_4554_);
if (v___x_4555_ == 0)
{
uint8_t v___x_4556_; 
lean_inc(v___x_4554_);
v___x_4556_ = l_Lean_Syntax_matchesNull(v___x_4554_, v___x_4478_);
if (v___x_4556_ == 0)
{
lean_object* v___x_4557_; 
lean_dec(v___x_4554_);
lean_dec(v_tk_4418_);
lean_dec(v_stx_4247_);
v___x_4557_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4557_;
}
else
{
lean_object* v_squeeze_4558_; lean_object* v___x_4559_; 
v_squeeze_4558_ = l_Lean_Syntax_getArg(v___x_4554_, v___x_4291_);
lean_dec(v___x_4554_);
v___x_4559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4559_, 0, v_squeeze_4558_);
v_squeeze_4537_ = v___x_4559_;
v___y_4538_ = v_a_4248_;
v___y_4539_ = v_a_4249_;
v___y_4540_ = v_a_4250_;
v___y_4541_ = v_a_4251_;
v___y_4542_ = v_a_4252_;
v___y_4543_ = v_a_4253_;
v___y_4544_ = v_a_4254_;
v___y_4545_ = v_a_4255_;
goto v___jp_4536_;
}
}
else
{
lean_object* v___x_4560_; 
lean_dec(v___x_4554_);
v___x_4560_ = lean_box(0);
v_squeeze_4537_ = v___x_4560_;
v___y_4538_ = v_a_4248_;
v___y_4539_ = v_a_4249_;
v___y_4540_ = v_a_4250_;
v___y_4541_ = v_a_4251_;
v___y_4542_ = v_a_4252_;
v___y_4543_ = v_a_4253_;
v___y_4544_ = v_a_4254_;
v___y_4545_ = v_a_4255_;
goto v___jp_4536_;
}
v___jp_4292_:
{
lean_object* v___x_4315_; lean_object* v___x_4316_; 
lean_inc_ref(v___y_4307_);
v___x_4315_ = l_Array_append___redArg(v___y_4307_, v___y_4314_);
lean_dec_ref(v___y_4314_);
lean_inc(v___y_4310_);
lean_inc(v___y_4303_);
v___x_4316_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4316_, 0, v___y_4303_);
lean_ctor_set(v___x_4316_, 1, v___y_4310_);
lean_ctor_set(v___x_4316_, 2, v___x_4315_);
if (lean_obj_tag(v___y_4300_) == 1)
{
lean_object* v_val_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; 
v_val_4317_ = lean_ctor_get(v___y_4300_, 0);
lean_inc(v_val_4317_);
lean_dec_ref_known(v___y_4300_, 1);
v___x_4318_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
v___x_4319_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_4303_, 4);
v___x_4320_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4320_, 0, v___y_4303_);
lean_ctor_set(v___x_4320_, 1, v___x_4319_);
lean_inc_ref(v___y_4307_);
v___x_4321_ = l_Array_append___redArg(v___y_4307_, v_val_4317_);
lean_dec(v_val_4317_);
lean_inc(v___y_4310_);
v___x_4322_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4322_, 0, v___y_4303_);
lean_ctor_set(v___x_4322_, 1, v___y_4310_);
lean_ctor_set(v___x_4322_, 2, v___x_4321_);
v___x_4323_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_4324_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4324_, 0, v___y_4303_);
lean_ctor_set(v___x_4324_, 1, v___x_4323_);
v___x_4325_ = l_Lean_Syntax_node3(v___y_4303_, v___x_4318_, v___x_4320_, v___x_4322_, v___x_4324_);
v___x_4326_ = l_Array_mkArray1___redArg(v___x_4325_);
v___y_4258_ = v___y_4293_;
v___y_4259_ = v___y_4294_;
v___y_4260_ = v___y_4295_;
v___y_4261_ = v___y_4296_;
v___y_4262_ = v___y_4297_;
v___y_4263_ = v___y_4298_;
v___y_4264_ = v___y_4299_;
v___y_4265_ = v___y_4301_;
v___y_4266_ = v___y_4302_;
v___y_4267_ = v___y_4303_;
v___y_4268_ = v___y_4304_;
v___y_4269_ = v___y_4305_;
v___y_4270_ = v___y_4306_;
v___y_4271_ = v___y_4307_;
v___y_4272_ = v___y_4308_;
v___y_4273_ = v___x_4316_;
v___y_4274_ = v___y_4309_;
v___y_4275_ = v___y_4310_;
v___y_4276_ = v___y_4311_;
v___y_4277_ = v___y_4312_;
v___y_4278_ = v___y_4313_;
v___y_4279_ = v___x_4326_;
goto v___jp_4257_;
}
else
{
lean_object* v___x_4327_; 
lean_dec(v___y_4300_);
v___x_4327_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___y_4258_ = v___y_4293_;
v___y_4259_ = v___y_4294_;
v___y_4260_ = v___y_4295_;
v___y_4261_ = v___y_4296_;
v___y_4262_ = v___y_4297_;
v___y_4263_ = v___y_4298_;
v___y_4264_ = v___y_4299_;
v___y_4265_ = v___y_4301_;
v___y_4266_ = v___y_4302_;
v___y_4267_ = v___y_4303_;
v___y_4268_ = v___y_4304_;
v___y_4269_ = v___y_4305_;
v___y_4270_ = v___y_4306_;
v___y_4271_ = v___y_4307_;
v___y_4272_ = v___y_4308_;
v___y_4273_ = v___x_4316_;
v___y_4274_ = v___y_4309_;
v___y_4275_ = v___y_4310_;
v___y_4276_ = v___y_4311_;
v___y_4277_ = v___y_4312_;
v___y_4278_ = v___y_4313_;
v___y_4279_ = v___x_4327_;
goto v___jp_4257_;
}
}
v___jp_4328_:
{
lean_object* v___x_4351_; lean_object* v___x_4352_; 
lean_inc_ref(v___y_4343_);
v___x_4351_ = l_Array_append___redArg(v___y_4343_, v___y_4350_);
lean_dec_ref(v___y_4350_);
lean_inc(v___y_4346_);
lean_inc(v___y_4339_);
v___x_4352_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4352_, 0, v___y_4339_);
lean_ctor_set(v___x_4352_, 1, v___y_4346_);
lean_ctor_set(v___x_4352_, 2, v___x_4351_);
if (lean_obj_tag(v___y_4331_) == 1)
{
lean_object* v_val_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; 
v_val_4353_ = lean_ctor_get(v___y_4331_, 0);
lean_inc(v_val_4353_);
lean_dec_ref_known(v___y_4331_, 1);
v___x_4354_ = l_Lean_SourceInfo_fromRef(v_val_4353_, v___x_4289_);
lean_dec(v_val_4353_);
v___x_4355_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_4356_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4356_, 0, v___x_4354_);
lean_ctor_set(v___x_4356_, 1, v___x_4355_);
v___x_4357_ = l_Array_mkArray1___redArg(v___x_4356_);
v___y_4293_ = v___y_4329_;
v___y_4294_ = v___y_4330_;
v___y_4295_ = v___y_4332_;
v___y_4296_ = v___x_4352_;
v___y_4297_ = v___y_4333_;
v___y_4298_ = v___y_4334_;
v___y_4299_ = v___y_4335_;
v___y_4300_ = v___y_4336_;
v___y_4301_ = v___y_4337_;
v___y_4302_ = v___y_4338_;
v___y_4303_ = v___y_4339_;
v___y_4304_ = v___y_4340_;
v___y_4305_ = v___y_4341_;
v___y_4306_ = v___y_4342_;
v___y_4307_ = v___y_4343_;
v___y_4308_ = v___y_4344_;
v___y_4309_ = v___y_4345_;
v___y_4310_ = v___y_4346_;
v___y_4311_ = v___y_4347_;
v___y_4312_ = v___y_4348_;
v___y_4313_ = v___y_4349_;
v___y_4314_ = v___x_4357_;
goto v___jp_4292_;
}
else
{
lean_object* v___x_4358_; 
v___x_4358_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_4331_);
lean_dec(v___y_4331_);
v___y_4293_ = v___y_4329_;
v___y_4294_ = v___y_4330_;
v___y_4295_ = v___y_4332_;
v___y_4296_ = v___x_4352_;
v___y_4297_ = v___y_4333_;
v___y_4298_ = v___y_4334_;
v___y_4299_ = v___y_4335_;
v___y_4300_ = v___y_4336_;
v___y_4301_ = v___y_4337_;
v___y_4302_ = v___y_4338_;
v___y_4303_ = v___y_4339_;
v___y_4304_ = v___y_4340_;
v___y_4305_ = v___y_4341_;
v___y_4306_ = v___y_4342_;
v___y_4307_ = v___y_4343_;
v___y_4308_ = v___y_4344_;
v___y_4309_ = v___y_4345_;
v___y_4310_ = v___y_4346_;
v___y_4311_ = v___y_4347_;
v___y_4312_ = v___y_4348_;
v___y_4313_ = v___y_4349_;
v___y_4314_ = v___x_4358_;
goto v___jp_4292_;
}
}
v___jp_4359_:
{
lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; 
lean_inc_ref(v___y_4373_);
v___x_4381_ = l_Array_append___redArg(v___y_4373_, v___y_4380_);
lean_dec_ref(v___y_4380_);
lean_inc(v___y_4376_);
lean_inc(v___y_4369_);
v___x_4382_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4382_, 0, v___y_4369_);
lean_ctor_set(v___x_4382_, 1, v___y_4376_);
lean_ctor_set(v___x_4382_, 2, v___x_4381_);
v___x_4383_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6));
if (lean_obj_tag(v___y_4377_) == 0)
{
lean_object* v___x_4384_; 
v___x_4384_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___y_4329_ = v___y_4360_;
v___y_4330_ = v___y_4361_;
v___y_4331_ = v___y_4362_;
v___y_4332_ = v___y_4363_;
v___y_4333_ = v___y_4364_;
v___y_4334_ = v___y_4365_;
v___y_4335_ = v___x_4382_;
v___y_4336_ = v___y_4366_;
v___y_4337_ = v___y_4367_;
v___y_4338_ = v___y_4368_;
v___y_4339_ = v___y_4369_;
v___y_4340_ = v___y_4370_;
v___y_4341_ = v___y_4371_;
v___y_4342_ = v___y_4372_;
v___y_4343_ = v___y_4373_;
v___y_4344_ = v___y_4374_;
v___y_4345_ = v___y_4375_;
v___y_4346_ = v___y_4376_;
v___y_4347_ = v___y_4378_;
v___y_4348_ = v___y_4379_;
v___y_4349_ = v___x_4383_;
v___y_4350_ = v___x_4384_;
goto v___jp_4328_;
}
else
{
lean_object* v_val_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; 
v_val_4385_ = lean_ctor_get(v___y_4377_, 0);
lean_inc(v_val_4385_);
lean_dec_ref_known(v___y_4377_, 1);
v___x_4386_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___x_4387_ = lean_array_push(v___x_4386_, v_val_4385_);
v___y_4329_ = v___y_4360_;
v___y_4330_ = v___y_4361_;
v___y_4331_ = v___y_4362_;
v___y_4332_ = v___y_4363_;
v___y_4333_ = v___y_4364_;
v___y_4334_ = v___y_4365_;
v___y_4335_ = v___x_4382_;
v___y_4336_ = v___y_4366_;
v___y_4337_ = v___y_4367_;
v___y_4338_ = v___y_4368_;
v___y_4339_ = v___y_4369_;
v___y_4340_ = v___y_4370_;
v___y_4341_ = v___y_4371_;
v___y_4342_ = v___y_4372_;
v___y_4343_ = v___y_4373_;
v___y_4344_ = v___y_4374_;
v___y_4345_ = v___y_4375_;
v___y_4346_ = v___y_4376_;
v___y_4347_ = v___y_4378_;
v___y_4348_ = v___y_4379_;
v___y_4349_ = v___x_4383_;
v___y_4350_ = v___x_4387_;
goto v___jp_4328_;
}
}
v___jp_4388_:
{
lean_object* v___x_4410_; lean_object* v___x_4411_; 
lean_inc_ref(v___y_4402_);
v___x_4410_ = l_Array_append___redArg(v___y_4402_, v___y_4409_);
lean_dec_ref(v___y_4409_);
lean_inc(v___y_4406_);
lean_inc(v___y_4398_);
v___x_4411_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4411_, 0, v___y_4398_);
lean_ctor_set(v___x_4411_, 1, v___y_4406_);
lean_ctor_set(v___x_4411_, 2, v___x_4410_);
if (lean_obj_tag(v___y_4404_) == 1)
{
lean_object* v_val_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; 
v_val_4412_ = lean_ctor_get(v___y_4404_, 0);
lean_inc(v_val_4412_);
lean_dec_ref_known(v___y_4404_, 1);
v___x_4413_ = l_Lean_SourceInfo_fromRef(v_val_4412_, v___x_4289_);
lean_dec(v_val_4412_);
v___x_4414_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__9));
v___x_4415_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4415_, 0, v___x_4413_);
lean_ctor_set(v___x_4415_, 1, v___x_4414_);
v___x_4416_ = l_Array_mkArray1___redArg(v___x_4415_);
v___y_4360_ = v___y_4389_;
v___y_4361_ = v___y_4390_;
v___y_4362_ = v___y_4391_;
v___y_4363_ = v___y_4392_;
v___y_4364_ = v___y_4393_;
v___y_4365_ = v___y_4394_;
v___y_4366_ = v___y_4395_;
v___y_4367_ = v___y_4396_;
v___y_4368_ = v___y_4397_;
v___y_4369_ = v___y_4398_;
v___y_4370_ = v___y_4399_;
v___y_4371_ = v___y_4400_;
v___y_4372_ = v___y_4401_;
v___y_4373_ = v___y_4402_;
v___y_4374_ = v___y_4403_;
v___y_4375_ = v___y_4405_;
v___y_4376_ = v___y_4406_;
v___y_4377_ = v___y_4407_;
v___y_4378_ = v___y_4408_;
v___y_4379_ = v___x_4411_;
v___y_4380_ = v___x_4416_;
goto v___jp_4359_;
}
else
{
lean_object* v___x_4417_; 
v___x_4417_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_4404_);
lean_dec(v___y_4404_);
v___y_4360_ = v___y_4389_;
v___y_4361_ = v___y_4390_;
v___y_4362_ = v___y_4391_;
v___y_4363_ = v___y_4392_;
v___y_4364_ = v___y_4393_;
v___y_4365_ = v___y_4394_;
v___y_4366_ = v___y_4395_;
v___y_4367_ = v___y_4396_;
v___y_4368_ = v___y_4397_;
v___y_4369_ = v___y_4398_;
v___y_4370_ = v___y_4399_;
v___y_4371_ = v___y_4400_;
v___y_4372_ = v___y_4401_;
v___y_4373_ = v___y_4402_;
v___y_4374_ = v___y_4403_;
v___y_4375_ = v___y_4405_;
v___y_4376_ = v___y_4406_;
v___y_4377_ = v___y_4407_;
v___y_4378_ = v___y_4408_;
v___y_4379_ = v___x_4411_;
v___y_4380_ = v___x_4417_;
goto v___jp_4359_;
}
}
v___jp_4419_:
{
lean_object* v_ref_4435_; uint8_t v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; 
v_ref_4435_ = lean_ctor_get(v___y_4429_, 2);
v___x_4436_ = 0;
v___x_4437_ = l_Lean_SourceInfo_fromRef(v_ref_4435_, v___x_4436_);
v___x_4438_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1));
v___x_4439_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
v___x_4440_ = l_Lean_SourceInfo_fromRef(v_tk_4418_, v___x_4289_);
lean_dec(v_tk_4418_);
v___x_4441_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4441_, 0, v___x_4440_);
lean_ctor_set(v___x_4441_, 1, v___x_4438_);
v___x_4442_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_4443_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6);
if (lean_obj_tag(v___y_4430_) == 1)
{
lean_object* v_val_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; 
v_val_4444_ = lean_ctor_get(v___y_4430_, 0);
lean_inc(v_val_4444_);
lean_dec_ref_known(v___y_4430_, 1);
v___x_4445_ = l_Lean_SourceInfo_fromRef(v_val_4444_, v___x_4289_);
lean_dec(v_val_4444_);
v___x_4446_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__1));
v___x_4447_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4447_, 0, v___x_4445_);
lean_ctor_set(v___x_4447_, 1, v___x_4446_);
v___x_4448_ = l_Array_mkArray1___redArg(v___x_4447_);
v___y_4389_ = v___y_4420_;
v___y_4390_ = v___y_4421_;
v___y_4391_ = v___y_4422_;
v___y_4392_ = v___y_4423_;
v___y_4393_ = v___y_4424_;
v___y_4394_ = v___x_4439_;
v___y_4395_ = v___y_4425_;
v___y_4396_ = v___y_4426_;
v___y_4397_ = v___x_4441_;
v___y_4398_ = v___x_4437_;
v___y_4399_ = v___y_4427_;
v___y_4400_ = v___y_4428_;
v___y_4401_ = v___x_4436_;
v___y_4402_ = v___x_4443_;
v___y_4403_ = v___y_4429_;
v___y_4404_ = v___y_4431_;
v___y_4405_ = v___y_4432_;
v___y_4406_ = v___x_4442_;
v___y_4407_ = v___y_4434_;
v___y_4408_ = v___y_4433_;
v___y_4409_ = v___x_4448_;
goto v___jp_4388_;
}
else
{
lean_object* v___x_4449_; 
v___x_4449_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_4430_);
lean_dec(v___y_4430_);
v___y_4389_ = v___y_4420_;
v___y_4390_ = v___y_4421_;
v___y_4391_ = v___y_4422_;
v___y_4392_ = v___y_4423_;
v___y_4393_ = v___y_4424_;
v___y_4394_ = v___x_4439_;
v___y_4395_ = v___y_4425_;
v___y_4396_ = v___y_4426_;
v___y_4397_ = v___x_4441_;
v___y_4398_ = v___x_4437_;
v___y_4399_ = v___y_4427_;
v___y_4400_ = v___y_4428_;
v___y_4401_ = v___x_4436_;
v___y_4402_ = v___x_4443_;
v___y_4403_ = v___y_4429_;
v___y_4404_ = v___y_4431_;
v___y_4405_ = v___y_4432_;
v___y_4406_ = v___x_4442_;
v___y_4407_ = v___y_4434_;
v___y_4408_ = v___y_4433_;
v___y_4409_ = v___x_4449_;
goto v___jp_4388_;
}
}
v___jp_4450_:
{
lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; 
v___x_4466_ = lean_unsigned_to_nat(5u);
v___x_4467_ = l_Lean_Syntax_getArg(v___y_4455_, v___x_4466_);
lean_dec(v___y_4455_);
v___x_4468_ = l_Lean_Syntax_getOptional_x3f(v___y_4456_);
lean_dec(v___y_4456_);
if (lean_obj_tag(v___x_4468_) == 0)
{
lean_object* v___x_4469_; 
v___x_4469_ = lean_box(0);
v___y_4420_ = v___y_4460_;
v___y_4421_ = v___x_4467_;
v___y_4422_ = v___y_4451_;
v___y_4423_ = v___y_4463_;
v___y_4424_ = v___y_4459_;
v___y_4425_ = v_args_4457_;
v___y_4426_ = v___y_4454_;
v___y_4427_ = v___y_4458_;
v___y_4428_ = v___y_4465_;
v___y_4429_ = v___y_4464_;
v___y_4430_ = v___y_4453_;
v___y_4431_ = v___y_4452_;
v___y_4432_ = v___y_4462_;
v___y_4433_ = v___y_4461_;
v___y_4434_ = v___x_4469_;
goto v___jp_4419_;
}
else
{
lean_object* v_val_4470_; lean_object* v___x_4472_; uint8_t v_isShared_4473_; uint8_t v_isSharedCheck_4477_; 
v_val_4470_ = lean_ctor_get(v___x_4468_, 0);
v_isSharedCheck_4477_ = !lean_is_exclusive(v___x_4468_);
if (v_isSharedCheck_4477_ == 0)
{
v___x_4472_ = v___x_4468_;
v_isShared_4473_ = v_isSharedCheck_4477_;
goto v_resetjp_4471_;
}
else
{
lean_inc(v_val_4470_);
lean_dec(v___x_4468_);
v___x_4472_ = lean_box(0);
v_isShared_4473_ = v_isSharedCheck_4477_;
goto v_resetjp_4471_;
}
v_resetjp_4471_:
{
lean_object* v___x_4475_; 
if (v_isShared_4473_ == 0)
{
v___x_4475_ = v___x_4472_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4476_; 
v_reuseFailAlloc_4476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4476_, 0, v_val_4470_);
v___x_4475_ = v_reuseFailAlloc_4476_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
v___y_4420_ = v___y_4460_;
v___y_4421_ = v___x_4467_;
v___y_4422_ = v___y_4451_;
v___y_4423_ = v___y_4463_;
v___y_4424_ = v___y_4459_;
v___y_4425_ = v_args_4457_;
v___y_4426_ = v___y_4454_;
v___y_4427_ = v___y_4458_;
v___y_4428_ = v___y_4465_;
v___y_4429_ = v___y_4464_;
v___y_4430_ = v___y_4453_;
v___y_4431_ = v___y_4452_;
v___y_4432_ = v___y_4462_;
v___y_4433_ = v___y_4461_;
v___y_4434_ = v___x_4475_;
goto v___jp_4419_;
}
}
}
}
v___jp_4479_:
{
lean_object* v___x_4495_; uint8_t v___x_4496_; 
v___x_4495_ = l_Lean_Syntax_getArg(v___y_4482_, v___y_4484_);
v___x_4496_ = l_Lean_Syntax_isNone(v___x_4495_);
if (v___x_4496_ == 0)
{
uint8_t v___x_4497_; 
lean_inc(v___x_4495_);
v___x_4497_ = l_Lean_Syntax_matchesNull(v___x_4495_, v___x_4478_);
if (v___x_4497_ == 0)
{
lean_object* v___x_4498_; 
lean_dec(v___x_4495_);
lean_dec(v_only_4486_);
lean_dec(v___y_4485_);
lean_dec(v___y_4483_);
lean_dec(v___y_4482_);
lean_dec(v___y_4481_);
lean_dec(v___y_4480_);
lean_dec(v_tk_4418_);
v___x_4498_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4498_;
}
else
{
lean_object* v___x_4499_; lean_object* v___x_4500_; uint8_t v___x_4501_; 
v___x_4499_ = l_Lean_Syntax_getArg(v___x_4495_, v___x_4291_);
lean_dec(v___x_4495_);
v___x_4500_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
lean_inc(v___x_4499_);
v___x_4501_ = l_Lean_Syntax_isOfKind(v___x_4499_, v___x_4500_);
if (v___x_4501_ == 0)
{
lean_object* v___x_4502_; 
lean_dec(v___x_4499_);
lean_dec(v_only_4486_);
lean_dec(v___y_4485_);
lean_dec(v___y_4483_);
lean_dec(v___y_4482_);
lean_dec(v___y_4481_);
lean_dec(v___y_4480_);
lean_dec(v_tk_4418_);
v___x_4502_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4502_;
}
else
{
lean_object* v___x_4503_; lean_object* v_args_4504_; lean_object* v___x_4505_; 
v___x_4503_ = l_Lean_Syntax_getArg(v___x_4499_, v___x_4478_);
lean_dec(v___x_4499_);
v_args_4504_ = l_Lean_Syntax_getArgs(v___x_4503_);
lean_dec(v___x_4503_);
v___x_4505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4505_, 0, v_args_4504_);
v___y_4451_ = v_only_4486_;
v___y_4452_ = v___y_4481_;
v___y_4453_ = v___y_4480_;
v___y_4454_ = v___y_4483_;
v___y_4455_ = v___y_4482_;
v___y_4456_ = v___y_4485_;
v_args_4457_ = v___x_4505_;
v___y_4458_ = v___y_4487_;
v___y_4459_ = v___y_4488_;
v___y_4460_ = v___y_4489_;
v___y_4461_ = v___y_4490_;
v___y_4462_ = v___y_4491_;
v___y_4463_ = v___y_4492_;
v___y_4464_ = v___y_4493_;
v___y_4465_ = v___y_4494_;
goto v___jp_4450_;
}
}
}
else
{
lean_object* v___x_4506_; 
lean_dec(v___x_4495_);
v___x_4506_ = lean_box(0);
v___y_4451_ = v_only_4486_;
v___y_4452_ = v___y_4481_;
v___y_4453_ = v___y_4480_;
v___y_4454_ = v___y_4483_;
v___y_4455_ = v___y_4482_;
v___y_4456_ = v___y_4485_;
v_args_4457_ = v___x_4506_;
v___y_4458_ = v___y_4487_;
v___y_4459_ = v___y_4488_;
v___y_4460_ = v___y_4489_;
v___y_4461_ = v___y_4490_;
v___y_4462_ = v___y_4491_;
v___y_4463_ = v___y_4492_;
v___y_4464_ = v___y_4493_;
v___y_4465_ = v___y_4494_;
goto v___jp_4450_;
}
}
v___jp_4507_:
{
lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; uint8_t v___x_4522_; 
v___x_4519_ = lean_unsigned_to_nat(3u);
v___x_4520_ = l_Lean_Syntax_getArg(v_stx_4247_, v___x_4519_);
lean_dec(v_stx_4247_);
v___x_4521_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2));
lean_inc(v___x_4520_);
v___x_4522_ = l_Lean_Syntax_isOfKind(v___x_4520_, v___x_4521_);
if (v___x_4522_ == 0)
{
lean_object* v___x_4523_; 
lean_dec(v___x_4520_);
lean_dec(v_unfold_4510_);
lean_dec(v___y_4508_);
lean_dec(v_tk_4418_);
v___x_4523_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4523_;
}
else
{
lean_object* v___x_4524_; lean_object* v___x_4525_; uint8_t v___x_4526_; 
v___x_4524_ = l_Lean_Syntax_getArg(v___x_4520_, v___x_4291_);
v___x_4525_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8));
lean_inc(v___x_4524_);
v___x_4526_ = l_Lean_Syntax_isOfKind(v___x_4524_, v___x_4525_);
if (v___x_4526_ == 0)
{
lean_object* v___x_4527_; 
lean_dec(v___x_4524_);
lean_dec(v___x_4520_);
lean_dec(v_unfold_4510_);
lean_dec(v___y_4508_);
lean_dec(v_tk_4418_);
v___x_4527_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4527_;
}
else
{
lean_object* v___x_4528_; lean_object* v___x_4529_; uint8_t v___x_4530_; 
v___x_4528_ = l_Lean_Syntax_getArg(v___x_4520_, v___x_4478_);
v___x_4529_ = l_Lean_Syntax_getArg(v___x_4520_, v___y_4509_);
v___x_4530_ = l_Lean_Syntax_isNone(v___x_4529_);
if (v___x_4530_ == 0)
{
uint8_t v___x_4531_; 
lean_inc(v___x_4529_);
v___x_4531_ = l_Lean_Syntax_matchesNull(v___x_4529_, v___x_4478_);
if (v___x_4531_ == 0)
{
lean_object* v___x_4532_; 
lean_dec(v___x_4529_);
lean_dec(v___x_4528_);
lean_dec(v___x_4524_);
lean_dec(v___x_4520_);
lean_dec(v_unfold_4510_);
lean_dec(v___y_4508_);
lean_dec(v_tk_4418_);
v___x_4532_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4532_;
}
else
{
lean_object* v_only_4533_; lean_object* v___x_4534_; 
v_only_4533_ = l_Lean_Syntax_getArg(v___x_4529_, v___x_4291_);
lean_dec(v___x_4529_);
v___x_4534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4534_, 0, v_only_4533_);
v___y_4480_ = v___y_4508_;
v___y_4481_ = v_unfold_4510_;
v___y_4482_ = v___x_4520_;
v___y_4483_ = v___x_4524_;
v___y_4484_ = v___x_4519_;
v___y_4485_ = v___x_4528_;
v_only_4486_ = v___x_4534_;
v___y_4487_ = v___y_4511_;
v___y_4488_ = v___y_4512_;
v___y_4489_ = v___y_4513_;
v___y_4490_ = v___y_4514_;
v___y_4491_ = v___y_4515_;
v___y_4492_ = v___y_4516_;
v___y_4493_ = v___y_4517_;
v___y_4494_ = v___y_4518_;
goto v___jp_4479_;
}
}
else
{
lean_object* v___x_4535_; 
lean_dec(v___x_4529_);
v___x_4535_ = lean_box(0);
v___y_4480_ = v___y_4508_;
v___y_4481_ = v_unfold_4510_;
v___y_4482_ = v___x_4520_;
v___y_4483_ = v___x_4524_;
v___y_4484_ = v___x_4519_;
v___y_4485_ = v___x_4528_;
v_only_4486_ = v___x_4535_;
v___y_4487_ = v___y_4511_;
v___y_4488_ = v___y_4512_;
v___y_4489_ = v___y_4513_;
v___y_4490_ = v___y_4514_;
v___y_4491_ = v___y_4515_;
v___y_4492_ = v___y_4516_;
v___y_4493_ = v___y_4517_;
v___y_4494_ = v___y_4518_;
goto v___jp_4479_;
}
}
}
}
v___jp_4536_:
{
lean_object* v___x_4546_; lean_object* v___x_4547_; uint8_t v___x_4548_; 
v___x_4546_ = lean_unsigned_to_nat(2u);
v___x_4547_ = l_Lean_Syntax_getArg(v_stx_4247_, v___x_4546_);
v___x_4548_ = l_Lean_Syntax_isNone(v___x_4547_);
if (v___x_4548_ == 0)
{
uint8_t v___x_4549_; 
lean_inc(v___x_4547_);
v___x_4549_ = l_Lean_Syntax_matchesNull(v___x_4547_, v___x_4478_);
if (v___x_4549_ == 0)
{
lean_object* v___x_4550_; 
lean_dec(v___x_4547_);
lean_dec(v_squeeze_4537_);
lean_dec(v_tk_4418_);
lean_dec(v_stx_4247_);
v___x_4550_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4550_;
}
else
{
lean_object* v_unfold_4551_; lean_object* v___x_4552_; 
v_unfold_4551_ = l_Lean_Syntax_getArg(v___x_4547_, v___x_4291_);
lean_dec(v___x_4547_);
v___x_4552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4552_, 0, v_unfold_4551_);
v___y_4508_ = v_squeeze_4537_;
v___y_4509_ = v___x_4546_;
v_unfold_4510_ = v___x_4552_;
v___y_4511_ = v___y_4538_;
v___y_4512_ = v___y_4539_;
v___y_4513_ = v___y_4540_;
v___y_4514_ = v___y_4541_;
v___y_4515_ = v___y_4542_;
v___y_4516_ = v___y_4543_;
v___y_4517_ = v___y_4544_;
v___y_4518_ = v___y_4545_;
goto v___jp_4507_;
}
}
else
{
lean_object* v___x_4553_; 
lean_dec(v___x_4547_);
v___x_4553_ = lean_box(0);
v___y_4508_ = v_squeeze_4537_;
v___y_4509_ = v___x_4546_;
v_unfold_4510_ = v___x_4553_;
v___y_4511_ = v___y_4538_;
v___y_4512_ = v___y_4539_;
v___y_4513_ = v___y_4540_;
v___y_4514_ = v___y_4541_;
v___y_4515_ = v___y_4542_;
v___y_4516_ = v___y_4543_;
v___y_4517_ = v___y_4544_;
v___y_4518_ = v___y_4545_;
goto v___jp_4507_;
}
}
}
v___jp_4257_:
{
lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; 
lean_inc_ref(v___y_4271_);
v___x_4280_ = l_Array_append___redArg(v___y_4271_, v___y_4279_);
lean_dec_ref(v___y_4279_);
lean_inc_n(v___y_4275_, 2);
lean_inc_n(v___y_4267_, 4);
v___x_4281_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4281_, 0, v___y_4267_);
lean_ctor_set(v___x_4281_, 1, v___y_4275_);
lean_ctor_set(v___x_4281_, 2, v___x_4280_);
v___x_4282_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__5));
v___x_4283_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4283_, 0, v___y_4267_);
lean_ctor_set(v___x_4283_, 1, v___x_4282_);
v___x_4284_ = l_Lean_Syntax_node2(v___y_4267_, v___y_4275_, v___x_4283_, v___y_4259_);
lean_inc(v___y_4278_);
v___x_4285_ = l_Lean_Syntax_node5(v___y_4267_, v___y_4278_, v___y_4265_, v___y_4261_, v___y_4273_, v___x_4281_, v___x_4284_);
lean_inc(v___y_4263_);
v___x_4286_ = l_Lean_Syntax_node4(v___y_4267_, v___y_4263_, v___y_4266_, v___y_4277_, v___y_4264_, v___x_4285_);
v___x_4287_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v___y_4270_, v___x_4286_, v___y_4268_, v___y_4262_, v___y_4258_, v___y_4276_, v___y_4274_, v___y_4260_, v___y_4272_, v___y_4269_);
return v___x_4287_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___boxed(lean_object* v_stx_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_){
_start:
{
lean_object* v_res_4571_; 
v_res_4571_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang(v_stx_4561_, v_a_4562_, v_a_4563_, v_a_4564_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_, v_a_4569_);
lean_dec(v_a_4569_);
lean_dec_ref(v_a_4568_);
lean_dec(v_a_4567_);
lean_dec_ref(v_a_4566_);
lean_dec(v_a_4565_);
lean_dec_ref(v_a_4564_);
lean_dec(v_a_4563_);
lean_dec_ref(v_a_4562_);
return v_res_4571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1(){
_start:
{
lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; 
v___x_4580_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4581_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0));
v___x_4582_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1));
v___x_4583_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___boxed), 10, 0);
v___x_4584_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4580_, v___x_4581_, v___x_4582_, v___x_4583_);
return v___x_4584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___boxed(lean_object* v_a_4585_){
_start:
{
lean_object* v_res_4586_; 
v_res_4586_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1();
return v_res_4586_;
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
