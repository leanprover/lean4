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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
uint8_t v_suppressElabErrors_boxed_116_; uint8_t v___y_4798__boxed_117_; uint8_t v_res_118_; lean_object* v_r_119_; 
v_suppressElabErrors_boxed_116_ = lean_unbox(v_suppressElabErrors_113_);
v___y_4798__boxed_117_ = lean_unbox(v___y_114_);
v_res_118_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0(v_suppressElabErrors_boxed_116_, v___y_4798__boxed_117_, v_x_115_);
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
lean_object* v___y_154_; lean_object* v___y_155_; uint8_t v___y_156_; lean_object* v___y_157_; lean_object* v___y_158_; lean_object* v___y_159_; uint8_t v___y_160_; lean_object* v___y_161_; lean_object* v___y_162_; lean_object* v___y_191_; lean_object* v___y_192_; uint8_t v___y_193_; lean_object* v___y_194_; uint8_t v___y_195_; lean_object* v___y_196_; uint8_t v___y_197_; lean_object* v___y_198_; lean_object* v___y_216_; lean_object* v___y_217_; uint8_t v___y_218_; uint8_t v___y_219_; lean_object* v___y_220_; lean_object* v___y_221_; uint8_t v___y_222_; lean_object* v___y_223_; lean_object* v___y_227_; lean_object* v___y_228_; lean_object* v___y_229_; uint8_t v___y_230_; lean_object* v___y_231_; uint8_t v___y_232_; uint8_t v___y_233_; uint8_t v___x_238_; lean_object* v___y_240_; lean_object* v___y_241_; lean_object* v___y_242_; lean_object* v___y_243_; uint8_t v___y_244_; uint8_t v___y_245_; uint8_t v___y_246_; uint8_t v___y_248_; uint8_t v___x_264_; 
v___x_238_ = 2;
v___x_264_ = l_Lean_instBEqMessageSeverity_beq(v_severity_146_, v___x_238_);
if (v___x_264_ == 0)
{
v___y_248_ = v___x_264_;
goto v___jp_247_;
}
else
{
uint8_t v___x_265_; 
lean_inc_ref(v_msgData_145_);
v___x_265_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_145_);
v___y_248_ = v___x_265_;
goto v___jp_247_;
}
v___jp_153_:
{
lean_object* v___x_163_; lean_object* v_toCold_164_; lean_object* v_currNamespace_165_; lean_object* v_openDecls_166_; lean_object* v_env_167_; lean_object* v_nextMacroScope_168_; lean_object* v_ngen_169_; lean_object* v_auxDeclNGen_170_; lean_object* v_traceState_171_; lean_object* v_cache_172_; lean_object* v_messages_173_; lean_object* v_infoState_174_; lean_object* v_snapshotTasks_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_189_; 
v___x_163_ = lean_st_ref_take(v___y_162_);
v_toCold_164_ = lean_ctor_get(v___y_161_, 0);
v_currNamespace_165_ = lean_ctor_get(v_toCold_164_, 4);
v_openDecls_166_ = lean_ctor_get(v_toCold_164_, 5);
v_env_167_ = lean_ctor_get(v___x_163_, 0);
v_nextMacroScope_168_ = lean_ctor_get(v___x_163_, 1);
v_ngen_169_ = lean_ctor_get(v___x_163_, 2);
v_auxDeclNGen_170_ = lean_ctor_get(v___x_163_, 3);
v_traceState_171_ = lean_ctor_get(v___x_163_, 4);
v_cache_172_ = lean_ctor_get(v___x_163_, 5);
v_messages_173_ = lean_ctor_get(v___x_163_, 6);
v_infoState_174_ = lean_ctor_get(v___x_163_, 7);
v_snapshotTasks_175_ = lean_ctor_get(v___x_163_, 8);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_163_);
if (v_isSharedCheck_189_ == 0)
{
v___x_177_ = v___x_163_;
v_isShared_178_ = v_isSharedCheck_189_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_snapshotTasks_175_);
lean_inc(v_infoState_174_);
lean_inc(v_messages_173_);
lean_inc(v_cache_172_);
lean_inc(v_traceState_171_);
lean_inc(v_auxDeclNGen_170_);
lean_inc(v_ngen_169_);
lean_inc(v_nextMacroScope_168_);
lean_inc(v_env_167_);
lean_dec(v___x_163_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_189_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_184_; 
lean_inc(v_openDecls_166_);
lean_inc(v_currNamespace_165_);
v___x_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_179_, 0, v_currNamespace_165_);
lean_ctor_set(v___x_179_, 1, v_openDecls_166_);
v___x_180_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
lean_ctor_set(v___x_180_, 1, v___y_159_);
lean_inc_ref(v___y_155_);
lean_inc_ref(v___y_158_);
v___x_181_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_181_, 0, v___y_158_);
lean_ctor_set(v___x_181_, 1, v___y_157_);
lean_ctor_set(v___x_181_, 2, v___y_154_);
lean_ctor_set(v___x_181_, 3, v___y_155_);
lean_ctor_set(v___x_181_, 4, v___x_180_);
lean_ctor_set_uint8(v___x_181_, sizeof(void*)*5, v___y_160_);
lean_ctor_set_uint8(v___x_181_, sizeof(void*)*5 + 1, v___y_156_);
lean_ctor_set_uint8(v___x_181_, sizeof(void*)*5 + 2, v_isSilent_147_);
v___x_182_ = l_Lean_MessageLog_add(v___x_181_, v_messages_173_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 6, v___x_182_);
v___x_184_ = v___x_177_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_env_167_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v_nextMacroScope_168_);
lean_ctor_set(v_reuseFailAlloc_188_, 2, v_ngen_169_);
lean_ctor_set(v_reuseFailAlloc_188_, 3, v_auxDeclNGen_170_);
lean_ctor_set(v_reuseFailAlloc_188_, 4, v_traceState_171_);
lean_ctor_set(v_reuseFailAlloc_188_, 5, v_cache_172_);
lean_ctor_set(v_reuseFailAlloc_188_, 6, v___x_182_);
lean_ctor_set(v_reuseFailAlloc_188_, 7, v_infoState_174_);
lean_ctor_set(v_reuseFailAlloc_188_, 8, v_snapshotTasks_175_);
v___x_184_ = v_reuseFailAlloc_188_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_185_ = lean_st_ref_put(v___y_162_, v___x_184_);
v___x_186_ = lean_box(0);
v___x_187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
return v___x_187_;
}
}
}
v___jp_190_:
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
lean_dec_ref(v___y_191_);
v___y_154_ = v___x_207_;
v___y_155_ = v___x_208_;
v___y_156_ = v___y_195_;
v___y_157_ = v___x_205_;
v___y_158_ = v___y_194_;
v___y_159_ = v_a_201_;
v___y_160_ = v___y_197_;
v___y_161_ = v___y_150_;
v___y_162_ = v___y_151_;
goto v___jp_153_;
}
else
{
uint8_t v___x_209_; 
lean_inc(v_a_201_);
v___x_209_ = l_Lean_MessageData_hasTag(v___y_191_, v_a_201_);
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
v___y_161_ = v___y_150_;
v___y_162_ = v___y_151_;
goto v___jp_153_;
}
}
}
}
v___jp_215_:
{
lean_object* v___x_224_; 
v___x_224_ = l_Lean_Syntax_getTailPos_x3f(v___y_221_, v___y_222_);
lean_dec(v___y_221_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_inc(v___y_223_);
v___y_191_ = v___y_216_;
v___y_192_ = v___y_217_;
v___y_193_ = v___y_218_;
v___y_194_ = v___y_220_;
v___y_195_ = v___y_219_;
v___y_196_ = v___y_223_;
v___y_197_ = v___y_222_;
v___y_198_ = v___y_223_;
goto v___jp_190_;
}
else
{
lean_object* v_val_225_; 
v_val_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_val_225_);
lean_dec_ref_known(v___x_224_, 1);
v___y_191_ = v___y_216_;
v___y_192_ = v___y_217_;
v___y_193_ = v___y_218_;
v___y_194_ = v___y_220_;
v___y_195_ = v___y_219_;
v___y_196_ = v___y_223_;
v___y_197_ = v___y_222_;
v___y_198_ = v_val_225_;
goto v___jp_190_;
}
}
v___jp_226_:
{
lean_object* v_ref_234_; lean_object* v___x_235_; 
v_ref_234_ = l_Lean_replaceRef(v_ref_144_, v___y_229_);
v___x_235_ = l_Lean_Syntax_getPos_x3f(v_ref_234_, v___y_232_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v___x_236_; 
v___x_236_ = lean_unsigned_to_nat(0u);
v___y_216_ = v___y_227_;
v___y_217_ = v___y_228_;
v___y_218_ = v___y_230_;
v___y_219_ = v___y_233_;
v___y_220_ = v___y_231_;
v___y_221_ = v_ref_234_;
v___y_222_ = v___y_232_;
v___y_223_ = v___x_236_;
goto v___jp_215_;
}
else
{
lean_object* v_val_237_; 
v_val_237_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_val_237_);
lean_dec_ref_known(v___x_235_, 1);
v___y_216_ = v___y_227_;
v___y_217_ = v___y_228_;
v___y_218_ = v___y_230_;
v___y_219_ = v___y_233_;
v___y_220_ = v___y_231_;
v___y_221_ = v_ref_234_;
v___y_222_ = v___y_232_;
v___y_223_ = v_val_237_;
goto v___jp_215_;
}
}
v___jp_239_:
{
if (v___y_246_ == 0)
{
v___y_227_ = v___y_240_;
v___y_228_ = v___y_241_;
v___y_229_ = v___y_243_;
v___y_230_ = v___y_244_;
v___y_231_ = v___y_242_;
v___y_232_ = v___y_245_;
v___y_233_ = v_severity_146_;
goto v___jp_226_;
}
else
{
v___y_227_ = v___y_240_;
v___y_228_ = v___y_241_;
v___y_229_ = v___y_243_;
v___y_230_ = v___y_244_;
v___y_231_ = v___y_242_;
v___y_232_ = v___y_245_;
v___y_233_ = v___x_238_;
goto v___jp_226_;
}
}
v___jp_247_:
{
if (v___y_248_ == 0)
{
lean_object* v_toCold_249_; lean_object* v_ref_250_; uint8_t v_suppressElabErrors_251_; lean_object* v_fileName_252_; lean_object* v_fileMap_253_; lean_object* v_options_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___f_257_; uint8_t v___x_258_; uint8_t v___x_259_; 
v_toCold_249_ = lean_ctor_get(v___y_150_, 0);
v_ref_250_ = lean_ctor_get(v___y_150_, 2);
v_suppressElabErrors_251_ = lean_ctor_get_uint8(v___y_150_, sizeof(void*)*3 + 1);
v_fileName_252_ = lean_ctor_get(v_toCold_249_, 0);
v_fileMap_253_ = lean_ctor_get(v_toCold_249_, 1);
v_options_254_ = lean_ctor_get(v_toCold_249_, 2);
v___x_255_ = lean_box(v_suppressElabErrors_251_);
v___x_256_ = lean_box(v___y_248_);
v___f_257_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_257_, 0, v___x_255_);
lean_closure_set(v___f_257_, 1, v___x_256_);
v___x_258_ = 1;
v___x_259_ = l_Lean_instBEqMessageSeverity_beq(v_severity_146_, v___x_258_);
if (v___x_259_ == 0)
{
v___y_240_ = v___f_257_;
v___y_241_ = v_fileMap_253_;
v___y_242_ = v_fileName_252_;
v___y_243_ = v_ref_250_;
v___y_244_ = v_suppressElabErrors_251_;
v___y_245_ = v___y_248_;
v___y_246_ = v___x_259_;
goto v___jp_239_;
}
else
{
lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_260_ = l_Lean_warningAsError;
v___x_261_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__3(v_options_254_, v___x_260_);
v___y_240_ = v___f_257_;
v___y_241_ = v_fileMap_253_;
v___y_242_ = v_fileName_252_;
v___y_243_ = v_ref_250_;
v___y_244_ = v_suppressElabErrors_251_;
v___y_245_ = v___y_248_;
v___y_246_ = v___x_261_;
goto v___jp_239_;
}
}
else
{
lean_object* v___x_262_; lean_object* v___x_263_; 
lean_dec_ref(v_msgData_145_);
v___x_262_ = lean_box(0);
v___x_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
return v___x_263_;
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0(lean_object* v_ref_278_, lean_object* v_msgData_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
uint8_t v___x_289_; uint8_t v___x_290_; lean_object* v___x_291_; 
v___x_289_ = 1;
v___x_290_ = 0;
v___x_291_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg(v_ref_278_, v_msgData_279_, v___x_289_, v___x_290_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0___boxed(lean_object* v_ref_292_, lean_object* v_msgData_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0(v_ref_292_, v_msgData_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v_ref_292_);
return v_res_303_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__1(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__0));
v___x_306_ = l_Lean_stringToMessageData(v___x_305_);
return v___x_306_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__3(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__2));
v___x_309_ = l_Lean_stringToMessageData(v___x_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0(lean_object* v_linterOption_310_, lean_object* v_stx_311_, lean_object* v_msg_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v_name_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_340_; 
v_name_322_ = lean_ctor_get(v_linterOption_310_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v_linterOption_310_);
if (v_isSharedCheck_340_ == 0)
{
lean_object* v_unused_341_; 
v_unused_341_ = lean_ctor_get(v_linterOption_310_, 1);
lean_dec(v_unused_341_);
v___x_324_ = v_linterOption_310_;
v_isShared_325_ = v_isSharedCheck_340_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_name_322_);
lean_dec(v_linterOption_310_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_340_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_329_; 
v___x_326_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__1, &l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__1_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__1);
lean_inc(v_name_322_);
v___x_327_ = l_Lean_MessageData_ofName(v_name_322_);
if (v_isShared_325_ == 0)
{
lean_ctor_set_tag(v___x_324_, 7);
lean_ctor_set(v___x_324_, 1, v___x_327_);
lean_ctor_set(v___x_324_, 0, v___x_326_);
v___x_329_ = v___x_324_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_326_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v___x_327_);
v___x_329_ = v_reuseFailAlloc_339_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v_disable_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_330_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__3, &l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__3_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__3);
v___x_331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_329_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
v_disable_332_ = l_Lean_MessageData_note(v___x_331_);
v___x_333_ = l_Lean_Linter_linterMessageTag;
v___x_334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_334_, 0, v_msg_312_);
lean_ctor_set(v___x_334_, 1, v_disable_332_);
v___x_335_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_333_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
v___x_336_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_336_, 0, v_name_322_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
lean_inc(v_stx_311_);
v___x_337_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_337_, 0, v_stx_311_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
v___x_338_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0(v_stx_311_, v___x_337_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
lean_dec(v_stx_311_);
return v___x_338_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___boxed(lean_object* v_linterOption_342_, lean_object* v_stx_343_, lean_object* v_msg_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0(v_linterOption_342_, v_stx_343_, v_msg_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
lean_dec(v___y_348_);
lean_dec_ref(v___y_347_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
return v_res_354_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__1(void){
_start:
{
lean_object* v___x_356_; lean_object* v_msg_357_; 
v___x_356_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__0));
v_msg_357_ = l_Lean_stringToMessageData(v___x_356_);
return v_msg_357_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__6(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__5));
v___x_365_ = l_Lean_MessageData_ofFormat(v___x_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa(lean_object* v_initialState_366_, lean_object* v_ref_367_, lean_object* v_replacement_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v_msg_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = lean_box(0);
lean_inc(v_replacement_368_);
v___x_391_ = l_Lean_Meta_Tactic_TryThis_isValidTactic(v_initialState_366_, v_replacement_368_, v___x_390_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v_a_392_; lean_object* v_msg_393_; uint8_t v___x_394_; 
v_a_392_ = lean_ctor_get(v___x_391_, 0);
lean_inc(v_a_392_);
lean_dec_ref_known(v___x_391_, 1);
v_msg_393_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__1, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__1_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__1);
v___x_394_ = lean_unbox(v_a_392_);
lean_dec(v_a_392_);
if (v___x_394_ == 0)
{
lean_dec(v_replacement_368_);
v_msg_379_ = v_msg_393_;
v___y_380_ = v_a_369_;
v___y_381_ = v_a_370_;
v___y_382_ = v_a_371_;
v___y_383_ = v_a_372_;
v___y_384_ = v_a_373_;
v___y_385_ = v_a_374_;
v___y_386_ = v_a_375_;
v___y_387_ = v_a_376_;
goto v___jp_378_;
}
else
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; uint8_t v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; uint8_t v___x_405_; lean_object* v___x_406_; 
v___x_395_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__3));
v___x_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
lean_ctor_set(v___x_396_, 1, v_replacement_368_);
v___x_397_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
lean_ctor_set(v___x_397_, 1, v___x_390_);
lean_ctor_set(v___x_397_, 2, v___x_390_);
lean_ctor_set(v___x_397_, 3, v___x_390_);
lean_ctor_set(v___x_397_, 4, v___x_390_);
lean_ctor_set(v___x_397_, 5, v___x_390_);
lean_inc(v_ref_367_);
v___x_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_398_, 0, v_ref_367_);
v___x_399_ = 4;
lean_inc_ref(v___x_398_);
v___x_400_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_400_, 0, v___x_397_);
lean_ctor_set(v___x_400_, 1, v___x_398_);
lean_ctor_set(v___x_400_, 2, v___x_390_);
lean_ctor_set_uint8(v___x_400_, sizeof(void*)*3, v___x_399_);
v___x_401_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__6);
v___x_402_ = lean_unsigned_to_nat(1u);
v___x_403_ = lean_mk_empty_array_with_capacity(v___x_402_);
v___x_404_ = lean_array_push(v___x_403_, v___x_400_);
v___x_405_ = 0;
v___x_406_ = l_Lean_MessageData_hint(v___x_401_, v___x_404_, v___x_398_, v___x_390_, v___x_405_, v_a_375_, v_a_376_);
lean_dec_ref(v___x_404_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; lean_object* v___x_408_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
lean_inc(v_a_407_);
lean_dec_ref_known(v___x_406_, 1);
v___x_408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_408_, 0, v_msg_393_);
lean_ctor_set(v___x_408_, 1, v_a_407_);
v_msg_379_ = v___x_408_;
v___y_380_ = v_a_369_;
v___y_381_ = v_a_370_;
v___y_382_ = v_a_371_;
v___y_383_ = v_a_372_;
v___y_384_ = v_a_373_;
v___y_385_ = v_a_374_;
v___y_386_ = v_a_375_;
v___y_387_ = v_a_376_;
goto v___jp_378_;
}
else
{
lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_416_; 
lean_dec(v_ref_367_);
v_a_409_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_416_ == 0)
{
v___x_411_ = v___x_406_;
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_dec(v___x_406_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_414_; 
if (v_isShared_412_ == 0)
{
v___x_414_ = v___x_411_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_a_409_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
}
}
else
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_424_; 
lean_dec(v_replacement_368_);
lean_dec(v_ref_367_);
v_a_417_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_424_ == 0)
{
v___x_419_ = v___x_391_;
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_391_);
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
v___jp_378_:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = l_Lean_linter_unnecessarySimpa;
v___x_389_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0(v___x_388_, v_ref_367_, v_msg_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
return v___x_389_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___boxed(lean_object* v_initialState_425_, lean_object* v_ref_426_, lean_object* v_replacement_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa(v_initialState_425_, v_ref_426_, v_replacement_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec(v_a_433_);
lean_dec_ref(v_a_432_);
lean_dec(v_a_431_);
lean_dec_ref(v_a_430_);
lean_dec(v_a_429_);
lean_dec_ref(v_a_428_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1(lean_object* v_ref_438_, lean_object* v_msgData_439_, uint8_t v_severity_440_, uint8_t v_isSilent_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg(v_ref_438_, v_msgData_439_, v_severity_440_, v_isSilent_441_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_452_, lean_object* v_msgData_453_, lean_object* v_severity_454_, lean_object* v_isSilent_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
uint8_t v_severity_boxed_465_; uint8_t v_isSilent_boxed_466_; lean_object* v_res_467_; 
v_severity_boxed_465_ = lean_unbox(v_severity_454_);
v_isSilent_boxed_466_ = lean_unbox(v_isSilent_455_);
v_res_467_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1(v_ref_452_, v_msgData_453_, v_severity_boxed_465_, v_isSilent_boxed_466_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v_ref_452_);
return v_res_467_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_468_ = lean_box(0);
v___x_469_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
lean_ctor_set(v___x_470_, 1, v___x_468_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg(){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0);
v___x_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___boxed(lean_object* v___y_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0(lean_object* v_00_u03b1_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___boxed(lean_object* v_00_u03b1_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0(v_00_u03b1_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___redArg___lam__0(lean_object* v_x_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
lean_object* v___x_508_; 
lean_inc(v___y_502_);
lean_inc_ref(v___y_501_);
lean_inc(v___y_500_);
lean_inc_ref(v___y_499_);
v___x_508_ = lean_apply_9(v_x_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, lean_box(0));
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___redArg___lam__0___boxed(lean_object* v_x_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___redArg___lam__0(v_x_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___redArg(lean_object* v_mvarId_520_, lean_object* v_x_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v___f_531_; lean_object* v___x_532_; 
lean_inc(v___y_525_);
lean_inc_ref(v___y_524_);
lean_inc(v___y_523_);
lean_inc_ref(v___y_522_);
v___f_531_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_531_, 0, v_x_521_);
lean_closure_set(v___f_531_, 1, v___y_522_);
lean_closure_set(v___f_531_, 2, v___y_523_);
lean_closure_set(v___f_531_, 3, v___y_524_);
lean_closure_set(v___f_531_, 4, v___y_525_);
v___x_532_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_520_, v___f_531_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
if (lean_obj_tag(v___x_532_) == 0)
{
return v___x_532_;
}
else
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_540_; 
v_a_533_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_540_ == 0)
{
v___x_535_ = v___x_532_;
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_532_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_533_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___redArg___boxed(lean_object* v_mvarId_541_, lean_object* v_x_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___redArg(v_mvarId_541_, v_x_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(lean_object* v_00_u03b1_553_, lean_object* v_mvarId_554_, lean_object* v_x_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___redArg(v_mvarId_554_, v_x_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___boxed(lean_object* v_00_u03b1_566_, lean_object* v_mvarId_567_, lean_object* v_x_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(v_00_u03b1_566_, v_mvarId_567_, v_x_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
return v_res_578_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_579_ = lean_unsigned_to_nat(32u);
v___x_580_ = lean_mk_empty_array_with_capacity(v___x_579_);
v___x_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
return v___x_581_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__1(void){
_start:
{
size_t v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_582_ = ((size_t)5ULL);
v___x_583_ = lean_unsigned_to_nat(0u);
v___x_584_ = lean_unsigned_to_nat(32u);
v___x_585_ = lean_mk_empty_array_with_capacity(v___x_584_);
v___x_586_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__0);
v___x_587_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_587_, 0, v___x_586_);
lean_ctor_set(v___x_587_, 1, v___x_585_);
lean_ctor_set(v___x_587_, 2, v___x_583_);
lean_ctor_set(v___x_587_, 3, v___x_583_);
lean_ctor_set_usize(v___x_587_, 4, v___x_582_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(lean_object* v___y_588_){
_start:
{
lean_object* v___x_590_; lean_object* v_infoState_591_; lean_object* v_trees_592_; lean_object* v___x_593_; lean_object* v_infoState_594_; lean_object* v_env_595_; lean_object* v_nextMacroScope_596_; lean_object* v_ngen_597_; lean_object* v_auxDeclNGen_598_; lean_object* v_traceState_599_; lean_object* v_cache_600_; lean_object* v_messages_601_; lean_object* v_snapshotTasks_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_623_; 
v___x_590_ = lean_st_ref_get(v___y_588_);
v_infoState_591_ = lean_ctor_get(v___x_590_, 7);
lean_inc_ref(v_infoState_591_);
lean_dec(v___x_590_);
v_trees_592_ = lean_ctor_get(v_infoState_591_, 2);
lean_inc_ref(v_trees_592_);
lean_dec_ref(v_infoState_591_);
v___x_593_ = lean_st_ref_take(v___y_588_);
v_infoState_594_ = lean_ctor_get(v___x_593_, 7);
v_env_595_ = lean_ctor_get(v___x_593_, 0);
v_nextMacroScope_596_ = lean_ctor_get(v___x_593_, 1);
v_ngen_597_ = lean_ctor_get(v___x_593_, 2);
v_auxDeclNGen_598_ = lean_ctor_get(v___x_593_, 3);
v_traceState_599_ = lean_ctor_get(v___x_593_, 4);
v_cache_600_ = lean_ctor_get(v___x_593_, 5);
v_messages_601_ = lean_ctor_get(v___x_593_, 6);
v_snapshotTasks_602_ = lean_ctor_get(v___x_593_, 8);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_623_ == 0)
{
v___x_604_ = v___x_593_;
v_isShared_605_ = v_isSharedCheck_623_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_snapshotTasks_602_);
lean_inc(v_infoState_594_);
lean_inc(v_messages_601_);
lean_inc(v_cache_600_);
lean_inc(v_traceState_599_);
lean_inc(v_auxDeclNGen_598_);
lean_inc(v_ngen_597_);
lean_inc(v_nextMacroScope_596_);
lean_inc(v_env_595_);
lean_dec(v___x_593_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_623_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
uint8_t v_enabled_606_; lean_object* v_assignment_607_; lean_object* v_lazyAssignment_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_621_; 
v_enabled_606_ = lean_ctor_get_uint8(v_infoState_594_, sizeof(void*)*3);
v_assignment_607_ = lean_ctor_get(v_infoState_594_, 0);
v_lazyAssignment_608_ = lean_ctor_get(v_infoState_594_, 1);
v_isSharedCheck_621_ = !lean_is_exclusive(v_infoState_594_);
if (v_isSharedCheck_621_ == 0)
{
lean_object* v_unused_622_; 
v_unused_622_ = lean_ctor_get(v_infoState_594_, 2);
lean_dec(v_unused_622_);
v___x_610_ = v_infoState_594_;
v_isShared_611_ = v_isSharedCheck_621_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_lazyAssignment_608_);
lean_inc(v_assignment_607_);
lean_dec(v_infoState_594_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_621_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_612_; lean_object* v___x_614_; 
v___x_612_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__1);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 2, v___x_612_);
v___x_614_ = v___x_610_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_assignment_607_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v_lazyAssignment_608_);
lean_ctor_set(v_reuseFailAlloc_620_, 2, v___x_612_);
lean_ctor_set_uint8(v_reuseFailAlloc_620_, sizeof(void*)*3, v_enabled_606_);
v___x_614_ = v_reuseFailAlloc_620_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_616_; 
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 7, v___x_614_);
v___x_616_ = v___x_604_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_env_595_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v_nextMacroScope_596_);
lean_ctor_set(v_reuseFailAlloc_619_, 2, v_ngen_597_);
lean_ctor_set(v_reuseFailAlloc_619_, 3, v_auxDeclNGen_598_);
lean_ctor_set(v_reuseFailAlloc_619_, 4, v_traceState_599_);
lean_ctor_set(v_reuseFailAlloc_619_, 5, v_cache_600_);
lean_ctor_set(v_reuseFailAlloc_619_, 6, v_messages_601_);
lean_ctor_set(v_reuseFailAlloc_619_, 7, v___x_614_);
lean_ctor_set(v_reuseFailAlloc_619_, 8, v_snapshotTasks_602_);
v___x_616_ = v_reuseFailAlloc_619_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = lean_st_ref_put(v___y_588_, v___x_616_);
v___x_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_618_, 0, v_trees_592_);
return v___x_618_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___boxed(lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___y_624_);
lean_dec(v___y_624_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6(lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___y_634_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___boxed(lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6(v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(lean_object* v_msg_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v___f_658_; lean_object* v___x_83782__overap_659_; lean_object* v___x_660_; 
v___f_658_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___closed__0));
v___x_83782__overap_659_ = lean_panic_fn_borrowed(v___f_658_, v_msg_648_);
lean_inc(v___y_656_);
lean_inc_ref(v___y_655_);
lean_inc(v___y_654_);
lean_inc_ref(v___y_653_);
lean_inc(v___y_652_);
lean_inc_ref(v___y_651_);
lean_inc(v___y_650_);
lean_inc_ref(v___y_649_);
v___x_660_ = lean_apply_9(v___x_83782__overap_659_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, lean_box(0));
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___boxed(lean_object* v_msg_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v_msg_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0(lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v_ref_681_; uint8_t v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v_ref_681_ = lean_ctor_get(v___y_678_, 2);
v___x_682_ = 0;
v___x_683_ = l_Lean_SourceInfo_fromRef(v_ref_681_, v___x_682_);
v___x_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0___boxed(lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0(v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
return v_res_694_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6(void){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_Array_mkArray0(lean_box(0));
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1(lean_object* v___x_711_, lean_object* v___x_712_, lean_object* v_args_713_, lean_object* v_only_714_, uint8_t v___x_715_, lean_object* v___x_716_, lean_object* v___x_717_, lean_object* v___x_718_, lean_object* v___y_719_, lean_object* v_unfold_720_, uint8_t v___x_721_, lean_object* v_squeeze_722_, lean_object* v_loc_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v___y_783_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v___y_786_; uint8_t v___y_796_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; uint8_t v___y_871_; 
if (lean_obj_tag(v_squeeze_722_) == 0)
{
uint8_t v___x_884_; 
v___x_884_ = 0;
v___y_871_ = v___x_884_;
goto v___jp_870_;
}
else
{
lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_1020_; 
v_isSharedCheck_1020_ = !lean_is_exclusive(v_squeeze_722_);
if (v_isSharedCheck_1020_ == 0)
{
lean_object* v_unused_1021_; 
v_unused_1021_ = lean_ctor_get(v_squeeze_722_, 0);
lean_dec(v_unused_1021_);
v___x_886_ = v_squeeze_722_;
v_isShared_887_ = v_isSharedCheck_1020_;
goto v_resetjp_885_;
}
else
{
lean_dec(v_squeeze_722_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_1020_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
if (v___x_721_ == 0)
{
lean_del_object(v___x_886_);
v___y_871_ = v___x_721_;
goto v___jp_870_;
}
else
{
if (lean_obj_tag(v_unfold_720_) == 0)
{
lean_object* v_ref_888_; uint8_t v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_903_; lean_object* v___y_904_; lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v___y_939_; 
v_ref_888_ = lean_ctor_get(v___y_730_, 2);
v___x_889_ = 0;
v___x_890_ = l_Lean_SourceInfo_fromRef(v_ref_888_, v___x_889_);
v___x_891_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__9));
lean_inc_ref_n(v___x_718_, 2);
lean_inc_ref_n(v___x_717_, 2);
lean_inc_ref_n(v___x_716_, 2);
v___x_892_ = l_Lean_Name_mkStr4(v___x_716_, v___x_717_, v___x_718_, v___x_891_);
v___x_893_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__10));
lean_inc_n(v___x_890_, 2);
v___x_894_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_890_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
v___x_895_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_896_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6);
v___x_897_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_897_, 0, v___x_890_);
lean_ctor_set(v___x_897_, 1, v___x_895_);
lean_ctor_set(v___x_897_, 2, v___x_896_);
v___x_898_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__11));
v___x_899_ = l_Lean_Name_mkStr4(v___x_716_, v___x_717_, v___x_718_, v___x_898_);
if (lean_obj_tag(v___y_719_) == 0)
{
lean_object* v___x_948_; 
v___x_948_ = lean_mk_empty_array_with_capacity(v___x_712_);
v___y_939_ = v___x_948_;
goto v___jp_938_;
}
else
{
lean_object* v_val_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v_val_949_ = lean_ctor_get(v___y_719_, 0);
lean_inc(v_val_949_);
lean_dec_ref_known(v___y_719_, 1);
v___x_950_ = lean_mk_empty_array_with_capacity(v___x_712_);
v___x_951_ = lean_array_push(v___x_950_, v_val_949_);
v___y_939_ = v___x_951_;
goto v___jp_938_;
}
v___jp_900_:
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_910_; 
v___x_905_ = l_Array_append___redArg(v___x_896_, v___y_904_);
lean_dec_ref(v___y_904_);
lean_inc_n(v___x_890_, 2);
v___x_906_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_906_, 0, v___x_890_);
lean_ctor_set(v___x_906_, 1, v___x_895_);
lean_ctor_set(v___x_906_, 2, v___x_905_);
v___x_907_ = l_Lean_Syntax_node5(v___x_890_, v___x_899_, v___x_711_, v___y_903_, v___y_902_, v___y_901_, v___x_906_);
v___x_908_ = l_Lean_Syntax_node3(v___x_890_, v___x_892_, v___x_894_, v___x_897_, v___x_907_);
if (v_isShared_887_ == 0)
{
lean_ctor_set_tag(v___x_886_, 0);
lean_ctor_set(v___x_886_, 0, v___x_908_);
v___x_910_ = v___x_886_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_908_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
v___jp_912_:
{
lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_916_ = l_Array_append___redArg(v___x_896_, v___y_915_);
lean_dec_ref(v___y_915_);
lean_inc(v___x_890_);
v___x_917_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_917_, 0, v___x_890_);
lean_ctor_set(v___x_917_, 1, v___x_895_);
lean_ctor_set(v___x_917_, 2, v___x_916_);
if (lean_obj_tag(v_loc_723_) == 1)
{
lean_object* v_val_918_; lean_object* v___x_919_; 
v_val_918_ = lean_ctor_get(v_loc_723_, 0);
lean_inc(v_val_918_);
lean_dec_ref_known(v_loc_723_, 1);
v___x_919_ = l_Array_mkArray1___redArg(v_val_918_);
v___y_901_ = v___x_917_;
v___y_902_ = v___y_913_;
v___y_903_ = v___y_914_;
v___y_904_ = v___x_919_;
goto v___jp_900_;
}
else
{
lean_object* v___x_920_; 
lean_dec(v_loc_723_);
v___x_920_ = lean_mk_empty_array_with_capacity(v___x_712_);
v___y_901_ = v___x_917_;
v___y_902_ = v___y_913_;
v___y_903_ = v___y_914_;
v___y_904_ = v___x_920_;
goto v___jp_900_;
}
}
v___jp_921_:
{
lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_924_ = l_Array_append___redArg(v___x_896_, v___y_923_);
lean_dec_ref(v___y_923_);
lean_inc(v___x_890_);
v___x_925_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_925_, 0, v___x_890_);
lean_ctor_set(v___x_925_, 1, v___x_895_);
lean_ctor_set(v___x_925_, 2, v___x_924_);
if (lean_obj_tag(v_args_713_) == 1)
{
lean_object* v_val_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v_val_926_ = lean_ctor_get(v_args_713_, 0);
v___x_927_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_928_ = l_Lean_Name_mkStr4(v___x_716_, v___x_717_, v___x_718_, v___x_927_);
v___x_929_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___x_890_, 4);
v___x_930_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_890_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
v___x_931_ = l_Array_append___redArg(v___x_896_, v_val_926_);
v___x_932_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_932_, 0, v___x_890_);
lean_ctor_set(v___x_932_, 1, v___x_895_);
lean_ctor_set(v___x_932_, 2, v___x_931_);
v___x_933_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_934_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_890_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
v___x_935_ = l_Lean_Syntax_node3(v___x_890_, v___x_928_, v___x_930_, v___x_932_, v___x_934_);
v___x_936_ = l_Array_mkArray1___redArg(v___x_935_);
v___y_913_ = v___x_925_;
v___y_914_ = v___y_922_;
v___y_915_ = v___x_936_;
goto v___jp_912_;
}
else
{
lean_object* v___x_937_; 
lean_dec_ref(v___x_718_);
lean_dec_ref(v___x_717_);
lean_dec_ref(v___x_716_);
v___x_937_ = lean_mk_empty_array_with_capacity(v___x_712_);
v___y_913_ = v___x_925_;
v___y_914_ = v___y_922_;
v___y_915_ = v___x_937_;
goto v___jp_912_;
}
}
v___jp_938_:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = l_Array_append___redArg(v___x_896_, v___y_939_);
lean_dec_ref(v___y_939_);
lean_inc(v___x_890_);
v___x_941_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_941_, 0, v___x_890_);
lean_ctor_set(v___x_941_, 1, v___x_895_);
lean_ctor_set(v___x_941_, 2, v___x_940_);
if (lean_obj_tag(v_only_714_) == 1)
{
lean_object* v_val_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v_val_942_ = lean_ctor_get(v_only_714_, 0);
v___x_943_ = l_Lean_SourceInfo_fromRef(v_val_942_, v___x_715_);
v___x_944_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_945_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_943_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
v___x_946_ = l_Array_mkArray1___redArg(v___x_945_);
v___y_922_ = v___x_941_;
v___y_923_ = v___x_946_;
goto v___jp_921_;
}
else
{
lean_object* v___x_947_; 
v___x_947_ = lean_mk_empty_array_with_capacity(v___x_712_);
v___y_922_ = v___x_941_;
v___y_923_ = v___x_947_;
goto v___jp_921_;
}
}
}
else
{
lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_1018_; 
lean_del_object(v___x_886_);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_unfold_720_);
if (v_isSharedCheck_1018_ == 0)
{
lean_object* v_unused_1019_; 
v_unused_1019_ = lean_ctor_get(v_unfold_720_, 0);
lean_dec(v_unused_1019_);
v___x_953_ = v_unfold_720_;
v_isShared_954_ = v_isSharedCheck_1018_;
goto v_resetjp_952_;
}
else
{
lean_dec(v_unfold_720_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_1018_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v_ref_955_; uint8_t v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_1005_; 
v_ref_955_ = lean_ctor_get(v___y_730_, 2);
v___x_956_ = 0;
v___x_957_ = l_Lean_SourceInfo_fromRef(v_ref_955_, v___x_956_);
v___x_958_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__13));
lean_inc_ref_n(v___x_718_, 2);
lean_inc_ref_n(v___x_717_, 2);
lean_inc_ref_n(v___x_716_, 2);
v___x_959_ = l_Lean_Name_mkStr4(v___x_716_, v___x_717_, v___x_718_, v___x_958_);
v___x_960_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__14));
lean_inc(v___x_957_);
v___x_961_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_957_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
v___x_962_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__11));
v___x_963_ = l_Lean_Name_mkStr4(v___x_716_, v___x_717_, v___x_718_, v___x_962_);
v___x_964_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_965_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6);
if (lean_obj_tag(v___y_719_) == 0)
{
lean_object* v___x_1014_; 
v___x_1014_ = lean_mk_empty_array_with_capacity(v___x_712_);
v___y_1005_ = v___x_1014_;
goto v___jp_1004_;
}
else
{
lean_object* v_val_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v_val_1015_ = lean_ctor_get(v___y_719_, 0);
lean_inc(v_val_1015_);
lean_dec_ref_known(v___y_719_, 1);
v___x_1016_ = lean_mk_empty_array_with_capacity(v___x_712_);
v___x_1017_ = lean_array_push(v___x_1016_, v_val_1015_);
v___y_1005_ = v___x_1017_;
goto v___jp_1004_;
}
v___jp_966_:
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_976_; 
v___x_971_ = l_Array_append___redArg(v___x_965_, v___y_970_);
lean_dec_ref(v___y_970_);
lean_inc_n(v___x_957_, 2);
v___x_972_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_972_, 0, v___x_957_);
lean_ctor_set(v___x_972_, 1, v___x_964_);
lean_ctor_set(v___x_972_, 2, v___x_971_);
v___x_973_ = l_Lean_Syntax_node5(v___x_957_, v___x_963_, v___x_711_, v___y_969_, v___y_967_, v___y_968_, v___x_972_);
v___x_974_ = l_Lean_Syntax_node2(v___x_957_, v___x_959_, v___x_961_, v___x_973_);
if (v_isShared_954_ == 0)
{
lean_ctor_set_tag(v___x_953_, 0);
lean_ctor_set(v___x_953_, 0, v___x_974_);
v___x_976_ = v___x_953_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_974_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
v___jp_978_:
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = l_Array_append___redArg(v___x_965_, v___y_981_);
lean_dec_ref(v___y_981_);
lean_inc(v___x_957_);
v___x_983_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_983_, 0, v___x_957_);
lean_ctor_set(v___x_983_, 1, v___x_964_);
lean_ctor_set(v___x_983_, 2, v___x_982_);
if (lean_obj_tag(v_loc_723_) == 1)
{
lean_object* v_val_984_; lean_object* v___x_985_; 
v_val_984_ = lean_ctor_get(v_loc_723_, 0);
lean_inc(v_val_984_);
lean_dec_ref_known(v_loc_723_, 1);
v___x_985_ = l_Array_mkArray1___redArg(v_val_984_);
v___y_967_ = v___y_979_;
v___y_968_ = v___x_983_;
v___y_969_ = v___y_980_;
v___y_970_ = v___x_985_;
goto v___jp_966_;
}
else
{
lean_object* v___x_986_; 
lean_dec(v_loc_723_);
v___x_986_ = lean_mk_empty_array_with_capacity(v___x_712_);
v___y_967_ = v___y_979_;
v___y_968_ = v___x_983_;
v___y_969_ = v___y_980_;
v___y_970_ = v___x_986_;
goto v___jp_966_;
}
}
v___jp_987_:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = l_Array_append___redArg(v___x_965_, v___y_989_);
lean_dec_ref(v___y_989_);
lean_inc(v___x_957_);
v___x_991_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_991_, 0, v___x_957_);
lean_ctor_set(v___x_991_, 1, v___x_964_);
lean_ctor_set(v___x_991_, 2, v___x_990_);
if (lean_obj_tag(v_args_713_) == 1)
{
lean_object* v_val_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v_val_992_ = lean_ctor_get(v_args_713_, 0);
v___x_993_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_994_ = l_Lean_Name_mkStr4(v___x_716_, v___x_717_, v___x_718_, v___x_993_);
v___x_995_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___x_957_, 4);
v___x_996_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_957_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
v___x_997_ = l_Array_append___redArg(v___x_965_, v_val_992_);
v___x_998_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_998_, 0, v___x_957_);
lean_ctor_set(v___x_998_, 1, v___x_964_);
lean_ctor_set(v___x_998_, 2, v___x_997_);
v___x_999_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_1000_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_957_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = l_Lean_Syntax_node3(v___x_957_, v___x_994_, v___x_996_, v___x_998_, v___x_1000_);
v___x_1002_ = l_Array_mkArray1___redArg(v___x_1001_);
v___y_979_ = v___x_991_;
v___y_980_ = v___y_988_;
v___y_981_ = v___x_1002_;
goto v___jp_978_;
}
else
{
lean_object* v___x_1003_; 
lean_dec_ref(v___x_718_);
lean_dec_ref(v___x_717_);
lean_dec_ref(v___x_716_);
v___x_1003_ = lean_mk_empty_array_with_capacity(v___x_712_);
v___y_979_ = v___x_991_;
v___y_980_ = v___y_988_;
v___y_981_ = v___x_1003_;
goto v___jp_978_;
}
}
v___jp_1004_:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1006_ = l_Array_append___redArg(v___x_965_, v___y_1005_);
lean_dec_ref(v___y_1005_);
lean_inc(v___x_957_);
v___x_1007_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1007_, 0, v___x_957_);
lean_ctor_set(v___x_1007_, 1, v___x_964_);
lean_ctor_set(v___x_1007_, 2, v___x_1006_);
if (lean_obj_tag(v_only_714_) == 1)
{
lean_object* v_val_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v_val_1008_ = lean_ctor_get(v_only_714_, 0);
v___x_1009_ = l_Lean_SourceInfo_fromRef(v_val_1008_, v___x_715_);
v___x_1010_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_1011_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = l_Array_mkArray1___redArg(v___x_1011_);
v___y_988_ = v___x_1007_;
v___y_989_ = v___x_1012_;
goto v___jp_987_;
}
else
{
lean_object* v___x_1013_; 
v___x_1013_ = lean_mk_empty_array_with_capacity(v___x_712_);
v___y_988_ = v___x_1007_;
v___y_989_ = v___x_1013_;
goto v___jp_987_;
}
}
}
}
}
}
}
v___jp_733_:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
lean_inc_ref(v___y_739_);
v___x_743_ = l_Array_append___redArg(v___y_739_, v___y_742_);
lean_dec_ref(v___y_742_);
lean_inc(v___y_738_);
lean_inc(v___y_741_);
v___x_744_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_744_, 0, v___y_741_);
lean_ctor_set(v___x_744_, 1, v___y_738_);
lean_ctor_set(v___x_744_, 2, v___x_743_);
v___x_745_ = l_Lean_Syntax_node6(v___y_741_, v___y_735_, v___y_737_, v___x_711_, v___y_734_, v___y_740_, v___y_736_, v___x_744_);
v___x_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
return v___x_746_;
}
v___jp_747_:
{
lean_object* v___x_756_; lean_object* v___x_757_; 
lean_inc_ref(v___y_752_);
v___x_756_ = l_Array_append___redArg(v___y_752_, v___y_755_);
lean_dec_ref(v___y_755_);
lean_inc(v___y_751_);
lean_inc(v___y_754_);
v___x_757_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_757_, 0, v___y_754_);
lean_ctor_set(v___x_757_, 1, v___y_751_);
lean_ctor_set(v___x_757_, 2, v___x_756_);
if (lean_obj_tag(v_loc_723_) == 1)
{
lean_object* v_val_758_; lean_object* v___x_759_; 
v_val_758_ = lean_ctor_get(v_loc_723_, 0);
lean_inc(v_val_758_);
lean_dec_ref_known(v_loc_723_, 1);
v___x_759_ = l_Array_mkArray1___redArg(v_val_758_);
v___y_734_ = v___y_748_;
v___y_735_ = v___y_749_;
v___y_736_ = v___x_757_;
v___y_737_ = v___y_750_;
v___y_738_ = v___y_751_;
v___y_739_ = v___y_752_;
v___y_740_ = v___y_753_;
v___y_741_ = v___y_754_;
v___y_742_ = v___x_759_;
goto v___jp_733_;
}
else
{
lean_object* v___x_760_; 
lean_dec(v_loc_723_);
v___x_760_ = lean_mk_empty_array_with_capacity(v___x_712_);
v___y_734_ = v___y_748_;
v___y_735_ = v___y_749_;
v___y_736_ = v___x_757_;
v___y_737_ = v___y_750_;
v___y_738_ = v___y_751_;
v___y_739_ = v___y_752_;
v___y_740_ = v___y_753_;
v___y_741_ = v___y_754_;
v___y_742_ = v___x_760_;
goto v___jp_733_;
}
}
v___jp_761_:
{
lean_object* v___x_769_; lean_object* v___x_770_; 
lean_inc_ref(v___y_766_);
v___x_769_ = l_Array_append___redArg(v___y_766_, v___y_768_);
lean_dec_ref(v___y_768_);
lean_inc(v___y_765_);
lean_inc(v___y_767_);
v___x_770_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_770_, 0, v___y_767_);
lean_ctor_set(v___x_770_, 1, v___y_765_);
lean_ctor_set(v___x_770_, 2, v___x_769_);
if (lean_obj_tag(v_args_713_) == 1)
{
lean_object* v_val_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v_val_771_ = lean_ctor_get(v_args_713_, 0);
v___x_772_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_767_, 3);
v___x_773_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_773_, 0, v___y_767_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
lean_inc_ref(v___y_766_);
v___x_774_ = l_Array_append___redArg(v___y_766_, v_val_771_);
lean_inc(v___y_765_);
v___x_775_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_775_, 0, v___y_767_);
lean_ctor_set(v___x_775_, 1, v___y_765_);
lean_ctor_set(v___x_775_, 2, v___x_774_);
v___x_776_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_777_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_777_, 0, v___y_767_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
v___x_778_ = l_Array_mkArray3___redArg(v___x_773_, v___x_775_, v___x_777_);
v___y_748_ = v___y_762_;
v___y_749_ = v___y_763_;
v___y_750_ = v___y_764_;
v___y_751_ = v___y_765_;
v___y_752_ = v___y_766_;
v___y_753_ = v___x_770_;
v___y_754_ = v___y_767_;
v___y_755_ = v___x_778_;
goto v___jp_747_;
}
else
{
lean_object* v___x_779_; 
v___x_779_ = lean_mk_empty_array_with_capacity(v___x_712_);
v___y_748_ = v___y_762_;
v___y_749_ = v___y_763_;
v___y_750_ = v___y_764_;
v___y_751_ = v___y_765_;
v___y_752_ = v___y_766_;
v___y_753_ = v___x_770_;
v___y_754_ = v___y_767_;
v___y_755_ = v___x_779_;
goto v___jp_747_;
}
}
v___jp_780_:
{
lean_object* v___x_787_; lean_object* v___x_788_; 
lean_inc_ref(v___y_784_);
v___x_787_ = l_Array_append___redArg(v___y_784_, v___y_786_);
lean_dec_ref(v___y_786_);
lean_inc(v___y_783_);
lean_inc(v___y_785_);
v___x_788_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_788_, 0, v___y_785_);
lean_ctor_set(v___x_788_, 1, v___y_783_);
lean_ctor_set(v___x_788_, 2, v___x_787_);
if (lean_obj_tag(v_only_714_) == 1)
{
lean_object* v_val_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v_val_789_ = lean_ctor_get(v_only_714_, 0);
v___x_790_ = l_Lean_SourceInfo_fromRef(v_val_789_, v___x_715_);
v___x_791_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_792_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_792_, 0, v___x_790_);
lean_ctor_set(v___x_792_, 1, v___x_791_);
v___x_793_ = l_Array_mkArray1___redArg(v___x_792_);
v___y_762_ = v___x_788_;
v___y_763_ = v___y_781_;
v___y_764_ = v___y_782_;
v___y_765_ = v___y_783_;
v___y_766_ = v___y_784_;
v___y_767_ = v___y_785_;
v___y_768_ = v___x_793_;
goto v___jp_761_;
}
else
{
lean_object* v___x_794_; 
v___x_794_ = lean_mk_empty_array_with_capacity(v___x_712_);
v___y_762_ = v___x_788_;
v___y_763_ = v___y_781_;
v___y_764_ = v___y_782_;
v___y_765_ = v___y_783_;
v___y_766_ = v___y_784_;
v___y_767_ = v___y_785_;
v___y_768_ = v___x_794_;
goto v___jp_761_;
}
}
v___jp_795_:
{
lean_object* v_ref_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v_ref_797_ = lean_ctor_get(v___y_730_, 2);
v___x_798_ = l_Lean_SourceInfo_fromRef(v_ref_797_, v___y_796_);
v___x_799_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__3));
v___x_800_ = l_Lean_Name_mkStr4(v___x_716_, v___x_717_, v___x_718_, v___x_799_);
lean_inc(v___x_798_);
v___x_801_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_801_, 0, v___x_798_);
lean_ctor_set(v___x_801_, 1, v___x_799_);
v___x_802_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_803_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6);
if (lean_obj_tag(v___y_719_) == 0)
{
lean_object* v___x_804_; 
v___x_804_ = lean_mk_empty_array_with_capacity(v___x_712_);
v___y_781_ = v___x_800_;
v___y_782_ = v___x_801_;
v___y_783_ = v___x_802_;
v___y_784_ = v___x_803_;
v___y_785_ = v___x_798_;
v___y_786_ = v___x_804_;
goto v___jp_780_;
}
else
{
lean_object* v_val_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v_val_805_ = lean_ctor_get(v___y_719_, 0);
lean_inc(v_val_805_);
lean_dec_ref_known(v___y_719_, 1);
v___x_806_ = lean_mk_empty_array_with_capacity(v___x_712_);
v___x_807_ = lean_array_push(v___x_806_, v_val_805_);
v___y_781_ = v___x_800_;
v___y_782_ = v___x_801_;
v___y_783_ = v___x_802_;
v___y_784_ = v___x_803_;
v___y_785_ = v___x_798_;
v___y_786_ = v___x_807_;
goto v___jp_780_;
}
}
v___jp_808_:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
lean_inc_ref(v___y_810_);
v___x_818_ = l_Array_append___redArg(v___y_810_, v___y_817_);
lean_dec_ref(v___y_817_);
lean_inc(v___y_811_);
lean_inc(v___y_815_);
v___x_819_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_819_, 0, v___y_815_);
lean_ctor_set(v___x_819_, 1, v___y_811_);
lean_ctor_set(v___x_819_, 2, v___x_818_);
v___x_820_ = l_Lean_Syntax_node6(v___y_815_, v___y_814_, v___y_809_, v___x_711_, v___y_813_, v___y_816_, v___y_812_, v___x_819_);
v___x_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
return v___x_821_;
}
v___jp_822_:
{
lean_object* v___x_831_; lean_object* v___x_832_; 
lean_inc_ref(v___y_824_);
v___x_831_ = l_Array_append___redArg(v___y_824_, v___y_830_);
lean_dec_ref(v___y_830_);
lean_inc(v___y_825_);
lean_inc(v___y_828_);
v___x_832_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_832_, 0, v___y_828_);
lean_ctor_set(v___x_832_, 1, v___y_825_);
lean_ctor_set(v___x_832_, 2, v___x_831_);
if (lean_obj_tag(v_loc_723_) == 1)
{
lean_object* v_val_833_; lean_object* v___x_834_; 
v_val_833_ = lean_ctor_get(v_loc_723_, 0);
lean_inc(v_val_833_);
lean_dec_ref_known(v_loc_723_, 1);
v___x_834_ = l_Array_mkArray1___redArg(v_val_833_);
v___y_809_ = v___y_823_;
v___y_810_ = v___y_824_;
v___y_811_ = v___y_825_;
v___y_812_ = v___x_832_;
v___y_813_ = v___y_826_;
v___y_814_ = v___y_827_;
v___y_815_ = v___y_828_;
v___y_816_ = v___y_829_;
v___y_817_ = v___x_834_;
goto v___jp_808_;
}
else
{
lean_object* v___x_835_; 
lean_dec(v_loc_723_);
v___x_835_ = lean_mk_empty_array_with_capacity(v___x_712_);
v___y_809_ = v___y_823_;
v___y_810_ = v___y_824_;
v___y_811_ = v___y_825_;
v___y_812_ = v___x_832_;
v___y_813_ = v___y_826_;
v___y_814_ = v___y_827_;
v___y_815_ = v___y_828_;
v___y_816_ = v___y_829_;
v___y_817_ = v___x_835_;
goto v___jp_808_;
}
}
v___jp_836_:
{
lean_object* v___x_844_; lean_object* v___x_845_; 
lean_inc_ref(v___y_838_);
v___x_844_ = l_Array_append___redArg(v___y_838_, v___y_843_);
lean_dec_ref(v___y_843_);
lean_inc(v___y_839_);
lean_inc(v___y_842_);
v___x_845_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_845_, 0, v___y_842_);
lean_ctor_set(v___x_845_, 1, v___y_839_);
lean_ctor_set(v___x_845_, 2, v___x_844_);
if (lean_obj_tag(v_args_713_) == 1)
{
lean_object* v_val_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v_val_846_ = lean_ctor_get(v_args_713_, 0);
v___x_847_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_842_, 3);
v___x_848_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_848_, 0, v___y_842_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
lean_inc_ref(v___y_838_);
v___x_849_ = l_Array_append___redArg(v___y_838_, v_val_846_);
lean_inc(v___y_839_);
v___x_850_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_850_, 0, v___y_842_);
lean_ctor_set(v___x_850_, 1, v___y_839_);
lean_ctor_set(v___x_850_, 2, v___x_849_);
v___x_851_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_852_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_852_, 0, v___y_842_);
lean_ctor_set(v___x_852_, 1, v___x_851_);
v___x_853_ = l_Array_mkArray3___redArg(v___x_848_, v___x_850_, v___x_852_);
v___y_823_ = v___y_837_;
v___y_824_ = v___y_838_;
v___y_825_ = v___y_839_;
v___y_826_ = v___y_840_;
v___y_827_ = v___y_841_;
v___y_828_ = v___y_842_;
v___y_829_ = v___x_845_;
v___y_830_ = v___x_853_;
goto v___jp_822_;
}
else
{
lean_object* v___x_854_; 
v___x_854_ = lean_mk_empty_array_with_capacity(v___x_712_);
v___y_823_ = v___y_837_;
v___y_824_ = v___y_838_;
v___y_825_ = v___y_839_;
v___y_826_ = v___y_840_;
v___y_827_ = v___y_841_;
v___y_828_ = v___y_842_;
v___y_829_ = v___x_845_;
v___y_830_ = v___x_854_;
goto v___jp_822_;
}
}
v___jp_855_:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
lean_inc_ref(v___y_857_);
v___x_862_ = l_Array_append___redArg(v___y_857_, v___y_861_);
lean_dec_ref(v___y_861_);
lean_inc(v___y_858_);
lean_inc(v___y_860_);
v___x_863_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_863_, 0, v___y_860_);
lean_ctor_set(v___x_863_, 1, v___y_858_);
lean_ctor_set(v___x_863_, 2, v___x_862_);
if (lean_obj_tag(v_only_714_) == 1)
{
lean_object* v_val_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v_val_864_ = lean_ctor_get(v_only_714_, 0);
v___x_865_ = l_Lean_SourceInfo_fromRef(v_val_864_, v___x_715_);
v___x_866_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_867_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_865_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
v___x_868_ = l_Array_mkArray1___redArg(v___x_867_);
v___y_837_ = v___y_856_;
v___y_838_ = v___y_857_;
v___y_839_ = v___y_858_;
v___y_840_ = v___x_863_;
v___y_841_ = v___y_859_;
v___y_842_ = v___y_860_;
v___y_843_ = v___x_868_;
goto v___jp_836_;
}
else
{
lean_object* v___x_869_; 
v___x_869_ = lean_mk_empty_array_with_capacity(v___x_712_);
v___y_837_ = v___y_856_;
v___y_838_ = v___y_857_;
v___y_839_ = v___y_858_;
v___y_840_ = v___x_863_;
v___y_841_ = v___y_859_;
v___y_842_ = v___y_860_;
v___y_843_ = v___x_869_;
goto v___jp_836_;
}
}
v___jp_870_:
{
if (lean_obj_tag(v_unfold_720_) == 0)
{
v___y_796_ = v___y_871_;
goto v___jp_795_;
}
else
{
lean_dec_ref_known(v_unfold_720_, 1);
if (v___x_721_ == 0)
{
v___y_796_ = v___x_721_;
goto v___jp_795_;
}
else
{
lean_object* v_ref_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v_ref_872_ = lean_ctor_get(v___y_730_, 2);
v___x_873_ = l_Lean_SourceInfo_fromRef(v_ref_872_, v___y_871_);
v___x_874_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__7));
v___x_875_ = l_Lean_Name_mkStr4(v___x_716_, v___x_717_, v___x_718_, v___x_874_);
v___x_876_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__8));
lean_inc(v___x_873_);
v___x_877_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_873_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
v___x_878_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_879_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6);
if (lean_obj_tag(v___y_719_) == 0)
{
lean_object* v___x_880_; 
v___x_880_ = lean_mk_empty_array_with_capacity(v___x_712_);
v___y_856_ = v___x_877_;
v___y_857_ = v___x_879_;
v___y_858_ = v___x_878_;
v___y_859_ = v___x_875_;
v___y_860_ = v___x_873_;
v___y_861_ = v___x_880_;
goto v___jp_855_;
}
else
{
lean_object* v_val_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v_val_881_ = lean_ctor_get(v___y_719_, 0);
lean_inc(v_val_881_);
lean_dec_ref_known(v___y_719_, 1);
v___x_882_ = lean_mk_empty_array_with_capacity(v___x_712_);
v___x_883_ = lean_array_push(v___x_882_, v_val_881_);
v___y_856_ = v___x_877_;
v___y_857_ = v___x_879_;
v___y_858_ = v___x_878_;
v___y_859_ = v___x_875_;
v___y_860_ = v___x_873_;
v___y_861_ = v___x_883_;
goto v___jp_855_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___boxed(lean_object** _args){
lean_object* v___x_1022_ = _args[0];
lean_object* v___x_1023_ = _args[1];
lean_object* v_args_1024_ = _args[2];
lean_object* v_only_1025_ = _args[3];
lean_object* v___x_1026_ = _args[4];
lean_object* v___x_1027_ = _args[5];
lean_object* v___x_1028_ = _args[6];
lean_object* v___x_1029_ = _args[7];
lean_object* v___y_1030_ = _args[8];
lean_object* v_unfold_1031_ = _args[9];
lean_object* v___x_1032_ = _args[10];
lean_object* v_squeeze_1033_ = _args[11];
lean_object* v_loc_1034_ = _args[12];
lean_object* v___y_1035_ = _args[13];
lean_object* v___y_1036_ = _args[14];
lean_object* v___y_1037_ = _args[15];
lean_object* v___y_1038_ = _args[16];
lean_object* v___y_1039_ = _args[17];
lean_object* v___y_1040_ = _args[18];
lean_object* v___y_1041_ = _args[19];
lean_object* v___y_1042_ = _args[20];
lean_object* v___y_1043_ = _args[21];
_start:
{
uint8_t v___x_92943__boxed_1044_; uint8_t v___x_92948__boxed_1045_; lean_object* v_res_1046_; 
v___x_92943__boxed_1044_ = lean_unbox(v___x_1026_);
v___x_92948__boxed_1045_ = lean_unbox(v___x_1032_);
v_res_1046_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1(v___x_1022_, v___x_1023_, v_args_1024_, v_only_1025_, v___x_92943__boxed_1044_, v___x_1027_, v___x_1028_, v___x_1029_, v___y_1030_, v_unfold_1031_, v___x_92948__boxed_1045_, v_squeeze_1033_, v_loc_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v_only_1025_);
lean_dec(v_args_1024_);
lean_dec(v___x_1023_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2(lean_object* v_a_1047_, lean_object* v_trees_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v___x_1058_; 
lean_inc(v___y_1056_);
lean_inc_ref(v___y_1055_);
lean_inc(v___y_1054_);
lean_inc_ref(v___y_1053_);
lean_inc(v___y_1052_);
lean_inc_ref(v___y_1051_);
lean_inc(v___y_1050_);
lean_inc_ref(v___y_1049_);
v___x_1058_ = lean_apply_9(v_a_1047_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, lean_box(0));
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1067_; 
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1061_ = v___x_1058_;
v_isShared_1062_ = v_isSharedCheck_1067_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1058_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1067_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1063_; lean_object* v___x_1065_; 
v___x_1063_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1063_, 0, v_a_1059_);
lean_ctor_set(v___x_1063_, 1, v_trees_1048_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v___x_1063_);
v___x_1065_ = v___x_1061_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v___x_1063_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
else
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
lean_dec_ref(v_trees_1048_);
v_a_1068_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1070_ = v___x_1058_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1058_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1068_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___boxed(lean_object* v_a_1076_, lean_object* v_trees_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2(v_a_1076_, v_trees_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
return v_res_1087_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__0));
v___x_1090_ = l_Lean_stringToMessageData(v___x_1089_);
return v___x_1090_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__3(void){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__2));
v___x_1093_ = l_Lean_stringToMessageData(v___x_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3(lean_object* v_a_1094_, lean_object* v_a_1095_, uint8_t v___x_1096_, uint8_t v___x_1097_, lean_object* v_a_1098_, lean_object* v_mvarCounter_1099_, lean_object* v___x_1100_, lean_object* v___x_1101_, uint8_t v_useReducible_1102_, uint8_t v___x_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v___x_1113_; 
lean_inc(v_a_1094_);
v___x_1113_ = l_Lean_MVarId_getType(v_a_1094_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v_a_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
lean_inc_n(v_a_1114_, 2);
lean_dec_ref_known(v___x_1113_, 1);
v___x_1115_ = l_Lean_mkIdent(v_a_1095_);
v___x_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1116_, 0, v_a_1114_);
v___x_1117_ = l_Lean_Elab_Term_elabTerm(v___x_1115_, v___x_1116_, v___x_1096_, v___x_1096_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___x_1152_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1118_);
lean_dec_ref_known(v___x_1117_, 1);
v___x_1152_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_1097_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1335_; 
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1335_ == 0)
{
lean_object* v_unused_1336_; 
v_unused_1336_ = lean_ctor_get(v___x_1152_, 0);
lean_dec(v_unused_1336_);
v___x_1154_ = v___x_1152_;
v_isShared_1155_ = v_isSharedCheck_1335_;
goto v_resetjp_1153_;
}
else
{
lean_dec(v___x_1152_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1335_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1156_; 
lean_inc(v___y_1111_);
lean_inc_ref(v___y_1110_);
lean_inc(v___y_1109_);
lean_inc_ref(v___y_1108_);
lean_inc(v_a_1118_);
v___x_1156_ = lean_infer_type(v_a_1118_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; uint8_t v_____do__lift_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1178_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_a_1157_);
lean_dec_ref_known(v___x_1156_, 1);
if (v_useReducible_1102_ == 0)
{
lean_object* v___x_1189_; uint8_t v_foApprox_1190_; uint8_t v_ctxApprox_1191_; uint8_t v_quasiPatternApprox_1192_; uint8_t v_constApprox_1193_; uint8_t v_isDefEqStuckEx_1194_; uint8_t v_unificationHints_1195_; uint8_t v_proofIrrelevance_1196_; uint8_t v_offsetCnstrs_1197_; uint8_t v_transparency_1198_; uint8_t v_etaStruct_1199_; uint8_t v_univApprox_1200_; uint8_t v_iota_1201_; uint8_t v_beta_1202_; uint8_t v_proj_1203_; uint8_t v_zeta_1204_; uint8_t v_zetaDelta_1205_; uint8_t v_zetaUnused_1206_; uint8_t v_zetaHave_1207_; uint8_t v_canUnfoldPredicateConfig_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1239_; 
v___x_1189_ = l_Lean_Meta_Context_config(v___y_1108_);
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
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1210_ = v___x_1189_;
v_isShared_1211_ = v_isSharedCheck_1239_;
goto v_resetjp_1209_;
}
else
{
lean_dec(v___x_1189_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1239_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
uint8_t v_trackZetaDelta_1212_; lean_object* v_zetaDeltaSet_1213_; lean_object* v_lctx_1214_; lean_object* v_localInstances_1215_; lean_object* v_defEqCtx_x3f_1216_; lean_object* v_synthPendingDepth_1217_; lean_object* v_customCanUnfoldPredicate_x3f_1218_; uint8_t v_univApprox_1219_; uint8_t v_inTypeClassResolution_1220_; uint8_t v_cacheInferType_1221_; lean_object* v___x_1223_; 
v_trackZetaDelta_1212_ = lean_ctor_get_uint8(v___y_1108_, sizeof(void*)*7);
v_zetaDeltaSet_1213_ = lean_ctor_get(v___y_1108_, 1);
v_lctx_1214_ = lean_ctor_get(v___y_1108_, 2);
v_localInstances_1215_ = lean_ctor_get(v___y_1108_, 3);
v_defEqCtx_x3f_1216_ = lean_ctor_get(v___y_1108_, 4);
v_synthPendingDepth_1217_ = lean_ctor_get(v___y_1108_, 5);
v_customCanUnfoldPredicate_x3f_1218_ = lean_ctor_get(v___y_1108_, 6);
v_univApprox_1219_ = lean_ctor_get_uint8(v___y_1108_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1220_ = lean_ctor_get_uint8(v___y_1108_, sizeof(void*)*7 + 2);
v_cacheInferType_1221_ = lean_ctor_get_uint8(v___y_1108_, sizeof(void*)*7 + 3);
if (v_isShared_1211_ == 0)
{
v___x_1223_ = v___x_1210_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_1238_, 0, v_foApprox_1190_);
lean_ctor_set_uint8(v_reuseFailAlloc_1238_, 1, v_ctxApprox_1191_);
lean_ctor_set_uint8(v_reuseFailAlloc_1238_, 2, v_quasiPatternApprox_1192_);
lean_ctor_set_uint8(v_reuseFailAlloc_1238_, 3, v_constApprox_1193_);
lean_ctor_set_uint8(v_reuseFailAlloc_1238_, 4, v_isDefEqStuckEx_1194_);
lean_ctor_set_uint8(v_reuseFailAlloc_1238_, 5, v_unificationHints_1195_);
lean_ctor_set_uint8(v_reuseFailAlloc_1238_, 6, v_proofIrrelevance_1196_);
lean_ctor_set_uint8(v_reuseFailAlloc_1238_, 8, v_offsetCnstrs_1197_);
lean_ctor_set_uint8(v_reuseFailAlloc_1238_, 9, v_transparency_1198_);
lean_ctor_set_uint8(v_reuseFailAlloc_1238_, 10, v_etaStruct_1199_);
lean_ctor_set_uint8(v_reuseFailAlloc_1238_, 11, v_univApprox_1200_);
lean_ctor_set_uint8(v_reuseFailAlloc_1238_, 12, v_iota_1201_);
lean_ctor_set_uint8(v_reuseFailAlloc_1238_, 13, v_beta_1202_);
lean_ctor_set_uint8(v_reuseFailAlloc_1238_, 14, v_proj_1203_);
lean_ctor_set_uint8(v_reuseFailAlloc_1238_, 15, v_zeta_1204_);
lean_ctor_set_uint8(v_reuseFailAlloc_1238_, 16, v_zetaDelta_1205_);
lean_ctor_set_uint8(v_reuseFailAlloc_1238_, 17, v_zetaUnused_1206_);
lean_ctor_set_uint8(v_reuseFailAlloc_1238_, 18, v_zetaHave_1207_);
lean_ctor_set_uint8(v_reuseFailAlloc_1238_, 19, v_canUnfoldPredicateConfig_1208_);
v___x_1223_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
uint64_t v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
lean_ctor_set_uint8(v___x_1223_, 7, v___x_1103_);
v___x_1224_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1223_);
v___x_1225_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1225_, 0, v___x_1223_);
lean_ctor_set_uint64(v___x_1225_, sizeof(void*)*1, v___x_1224_);
lean_inc(v_customCanUnfoldPredicate_x3f_1218_);
lean_inc(v_synthPendingDepth_1217_);
lean_inc(v_defEqCtx_x3f_1216_);
lean_inc_ref(v_localInstances_1215_);
lean_inc_ref(v_lctx_1214_);
lean_inc(v_zetaDeltaSet_1213_);
v___x_1226_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
lean_ctor_set(v___x_1226_, 1, v_zetaDeltaSet_1213_);
lean_ctor_set(v___x_1226_, 2, v_lctx_1214_);
lean_ctor_set(v___x_1226_, 3, v_localInstances_1215_);
lean_ctor_set(v___x_1226_, 4, v_defEqCtx_x3f_1216_);
lean_ctor_set(v___x_1226_, 5, v_synthPendingDepth_1217_);
lean_ctor_set(v___x_1226_, 6, v_customCanUnfoldPredicate_x3f_1218_);
lean_ctor_set_uint8(v___x_1226_, sizeof(void*)*7, v_trackZetaDelta_1212_);
lean_ctor_set_uint8(v___x_1226_, sizeof(void*)*7 + 1, v_univApprox_1219_);
lean_ctor_set_uint8(v___x_1226_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1220_);
lean_ctor_set_uint8(v___x_1226_, sizeof(void*)*7 + 3, v_cacheInferType_1221_);
lean_inc(v_a_1157_);
lean_inc(v_a_1114_);
v___x_1227_ = l_Lean_Meta_isExprDefEq(v_a_1114_, v_a_1157_, v___x_1226_, v___y_1109_, v___y_1110_, v___y_1111_);
lean_dec_ref_known(v___x_1226_, 7);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v_a_1228_; uint8_t v___x_1229_; 
v_a_1228_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_a_1228_);
lean_dec_ref_known(v___x_1227_, 1);
v___x_1229_ = lean_unbox(v_a_1228_);
lean_dec(v_a_1228_);
v_____do__lift_1159_ = v___x_1229_;
v___y_1160_ = v___y_1104_;
v___y_1161_ = v___y_1105_;
v___y_1162_ = v___y_1106_;
v___y_1163_ = v___y_1107_;
v___y_1164_ = v___y_1108_;
v___y_1165_ = v___y_1109_;
v___y_1166_ = v___y_1110_;
v___y_1167_ = v___y_1111_;
goto v___jp_1158_;
}
else
{
lean_object* v_a_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1237_; 
lean_dec(v_a_1157_);
lean_del_object(v___x_1154_);
lean_dec(v_a_1118_);
lean_dec(v_a_1114_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec(v___x_1101_);
lean_dec_ref(v___x_1100_);
lean_dec_ref(v_a_1098_);
lean_dec(v_a_1094_);
v_a_1230_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1232_ = v___x_1227_;
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_a_1230_);
lean_dec(v___x_1227_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1235_; 
if (v_isShared_1233_ == 0)
{
v___x_1235_ = v___x_1232_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_a_1230_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
}
}
}
else
{
lean_object* v___x_1240_; uint8_t v_foApprox_1241_; uint8_t v_ctxApprox_1242_; uint8_t v_quasiPatternApprox_1243_; uint8_t v_constApprox_1244_; uint8_t v_isDefEqStuckEx_1245_; uint8_t v_unificationHints_1246_; uint8_t v_proofIrrelevance_1247_; uint8_t v_offsetCnstrs_1248_; uint8_t v_transparency_1249_; uint8_t v_etaStruct_1250_; uint8_t v_univApprox_1251_; uint8_t v_iota_1252_; uint8_t v_beta_1253_; uint8_t v_proj_1254_; uint8_t v_zeta_1255_; uint8_t v_zetaDelta_1256_; uint8_t v_zetaUnused_1257_; uint8_t v_zetaHave_1258_; uint8_t v_canUnfoldPredicateConfig_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1326_; 
v___x_1240_ = l_Lean_Meta_Context_config(v___y_1108_);
v_foApprox_1241_ = lean_ctor_get_uint8(v___x_1240_, 0);
v_ctxApprox_1242_ = lean_ctor_get_uint8(v___x_1240_, 1);
v_quasiPatternApprox_1243_ = lean_ctor_get_uint8(v___x_1240_, 2);
v_constApprox_1244_ = lean_ctor_get_uint8(v___x_1240_, 3);
v_isDefEqStuckEx_1245_ = lean_ctor_get_uint8(v___x_1240_, 4);
v_unificationHints_1246_ = lean_ctor_get_uint8(v___x_1240_, 5);
v_proofIrrelevance_1247_ = lean_ctor_get_uint8(v___x_1240_, 6);
v_offsetCnstrs_1248_ = lean_ctor_get_uint8(v___x_1240_, 8);
v_transparency_1249_ = lean_ctor_get_uint8(v___x_1240_, 9);
v_etaStruct_1250_ = lean_ctor_get_uint8(v___x_1240_, 10);
v_univApprox_1251_ = lean_ctor_get_uint8(v___x_1240_, 11);
v_iota_1252_ = lean_ctor_get_uint8(v___x_1240_, 12);
v_beta_1253_ = lean_ctor_get_uint8(v___x_1240_, 13);
v_proj_1254_ = lean_ctor_get_uint8(v___x_1240_, 14);
v_zeta_1255_ = lean_ctor_get_uint8(v___x_1240_, 15);
v_zetaDelta_1256_ = lean_ctor_get_uint8(v___x_1240_, 16);
v_zetaUnused_1257_ = lean_ctor_get_uint8(v___x_1240_, 17);
v_zetaHave_1258_ = lean_ctor_get_uint8(v___x_1240_, 18);
v_canUnfoldPredicateConfig_1259_ = lean_ctor_get_uint8(v___x_1240_, 19);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1261_ = v___x_1240_;
v_isShared_1262_ = v_isSharedCheck_1326_;
goto v_resetjp_1260_;
}
else
{
lean_dec(v___x_1240_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1326_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
uint8_t v___x_1263_; uint8_t v___x_1264_; 
v___x_1263_ = 2;
v___x_1264_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1249_, v___x_1263_);
if (v___x_1264_ == 0)
{
lean_object* v_keyedConfig_1265_; uint8_t v_trackZetaDelta_1266_; lean_object* v_zetaDeltaSet_1267_; lean_object* v_lctx_1268_; lean_object* v_localInstances_1269_; lean_object* v_defEqCtx_x3f_1270_; lean_object* v_synthPendingDepth_1271_; lean_object* v_customCanUnfoldPredicate_x3f_1272_; uint8_t v_univApprox_1273_; uint8_t v_inTypeClassResolution_1274_; uint8_t v_cacheInferType_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; uint8_t v_foApprox_1279_; uint8_t v_ctxApprox_1280_; uint8_t v_quasiPatternApprox_1281_; uint8_t v_constApprox_1282_; uint8_t v_isDefEqStuckEx_1283_; uint8_t v_unificationHints_1284_; uint8_t v_proofIrrelevance_1285_; uint8_t v_offsetCnstrs_1286_; uint8_t v_transparency_1287_; uint8_t v_etaStruct_1288_; uint8_t v_univApprox_1289_; uint8_t v_iota_1290_; uint8_t v_beta_1291_; uint8_t v_proj_1292_; uint8_t v_zeta_1293_; uint8_t v_zetaDelta_1294_; uint8_t v_zetaUnused_1295_; uint8_t v_zetaHave_1296_; uint8_t v_canUnfoldPredicateConfig_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1308_; 
lean_del_object(v___x_1261_);
v_keyedConfig_1265_ = lean_ctor_get(v___y_1108_, 0);
v_trackZetaDelta_1266_ = lean_ctor_get_uint8(v___y_1108_, sizeof(void*)*7);
v_zetaDeltaSet_1267_ = lean_ctor_get(v___y_1108_, 1);
v_lctx_1268_ = lean_ctor_get(v___y_1108_, 2);
v_localInstances_1269_ = lean_ctor_get(v___y_1108_, 3);
v_defEqCtx_x3f_1270_ = lean_ctor_get(v___y_1108_, 4);
v_synthPendingDepth_1271_ = lean_ctor_get(v___y_1108_, 5);
v_customCanUnfoldPredicate_x3f_1272_ = lean_ctor_get(v___y_1108_, 6);
v_univApprox_1273_ = lean_ctor_get_uint8(v___y_1108_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1274_ = lean_ctor_get_uint8(v___y_1108_, sizeof(void*)*7 + 2);
v_cacheInferType_1275_ = lean_ctor_get_uint8(v___y_1108_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1265_);
v___x_1276_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1263_, v_keyedConfig_1265_);
lean_inc(v_customCanUnfoldPredicate_x3f_1272_);
lean_inc(v_synthPendingDepth_1271_);
lean_inc(v_defEqCtx_x3f_1270_);
lean_inc_ref(v_localInstances_1269_);
lean_inc_ref(v_lctx_1268_);
lean_inc(v_zetaDeltaSet_1267_);
v___x_1277_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1277_, 0, v___x_1276_);
lean_ctor_set(v___x_1277_, 1, v_zetaDeltaSet_1267_);
lean_ctor_set(v___x_1277_, 2, v_lctx_1268_);
lean_ctor_set(v___x_1277_, 3, v_localInstances_1269_);
lean_ctor_set(v___x_1277_, 4, v_defEqCtx_x3f_1270_);
lean_ctor_set(v___x_1277_, 5, v_synthPendingDepth_1271_);
lean_ctor_set(v___x_1277_, 6, v_customCanUnfoldPredicate_x3f_1272_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*7, v_trackZetaDelta_1266_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*7 + 1, v_univApprox_1273_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1274_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*7 + 3, v_cacheInferType_1275_);
v___x_1278_ = l_Lean_Meta_Context_config(v___x_1277_);
lean_dec_ref_known(v___x_1277_, 7);
v_foApprox_1279_ = lean_ctor_get_uint8(v___x_1278_, 0);
v_ctxApprox_1280_ = lean_ctor_get_uint8(v___x_1278_, 1);
v_quasiPatternApprox_1281_ = lean_ctor_get_uint8(v___x_1278_, 2);
v_constApprox_1282_ = lean_ctor_get_uint8(v___x_1278_, 3);
v_isDefEqStuckEx_1283_ = lean_ctor_get_uint8(v___x_1278_, 4);
v_unificationHints_1284_ = lean_ctor_get_uint8(v___x_1278_, 5);
v_proofIrrelevance_1285_ = lean_ctor_get_uint8(v___x_1278_, 6);
v_offsetCnstrs_1286_ = lean_ctor_get_uint8(v___x_1278_, 8);
v_transparency_1287_ = lean_ctor_get_uint8(v___x_1278_, 9);
v_etaStruct_1288_ = lean_ctor_get_uint8(v___x_1278_, 10);
v_univApprox_1289_ = lean_ctor_get_uint8(v___x_1278_, 11);
v_iota_1290_ = lean_ctor_get_uint8(v___x_1278_, 12);
v_beta_1291_ = lean_ctor_get_uint8(v___x_1278_, 13);
v_proj_1292_ = lean_ctor_get_uint8(v___x_1278_, 14);
v_zeta_1293_ = lean_ctor_get_uint8(v___x_1278_, 15);
v_zetaDelta_1294_ = lean_ctor_get_uint8(v___x_1278_, 16);
v_zetaUnused_1295_ = lean_ctor_get_uint8(v___x_1278_, 17);
v_zetaHave_1296_ = lean_ctor_get_uint8(v___x_1278_, 18);
v_canUnfoldPredicateConfig_1297_ = lean_ctor_get_uint8(v___x_1278_, 19);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1299_ = v___x_1278_;
v_isShared_1300_ = v_isSharedCheck_1308_;
goto v_resetjp_1298_;
}
else
{
lean_dec(v___x_1278_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1308_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_1307_, 0, v_foApprox_1279_);
lean_ctor_set_uint8(v_reuseFailAlloc_1307_, 1, v_ctxApprox_1280_);
lean_ctor_set_uint8(v_reuseFailAlloc_1307_, 2, v_quasiPatternApprox_1281_);
lean_ctor_set_uint8(v_reuseFailAlloc_1307_, 3, v_constApprox_1282_);
lean_ctor_set_uint8(v_reuseFailAlloc_1307_, 4, v_isDefEqStuckEx_1283_);
lean_ctor_set_uint8(v_reuseFailAlloc_1307_, 5, v_unificationHints_1284_);
lean_ctor_set_uint8(v_reuseFailAlloc_1307_, 6, v_proofIrrelevance_1285_);
lean_ctor_set_uint8(v_reuseFailAlloc_1307_, 8, v_offsetCnstrs_1286_);
lean_ctor_set_uint8(v_reuseFailAlloc_1307_, 9, v_transparency_1287_);
lean_ctor_set_uint8(v_reuseFailAlloc_1307_, 10, v_etaStruct_1288_);
lean_ctor_set_uint8(v_reuseFailAlloc_1307_, 11, v_univApprox_1289_);
lean_ctor_set_uint8(v_reuseFailAlloc_1307_, 12, v_iota_1290_);
lean_ctor_set_uint8(v_reuseFailAlloc_1307_, 13, v_beta_1291_);
lean_ctor_set_uint8(v_reuseFailAlloc_1307_, 14, v_proj_1292_);
lean_ctor_set_uint8(v_reuseFailAlloc_1307_, 15, v_zeta_1293_);
lean_ctor_set_uint8(v_reuseFailAlloc_1307_, 16, v_zetaDelta_1294_);
lean_ctor_set_uint8(v_reuseFailAlloc_1307_, 17, v_zetaUnused_1295_);
lean_ctor_set_uint8(v_reuseFailAlloc_1307_, 18, v_zetaHave_1296_);
lean_ctor_set_uint8(v_reuseFailAlloc_1307_, 19, v_canUnfoldPredicateConfig_1297_);
v___x_1302_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
uint64_t v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
lean_ctor_set_uint8(v___x_1302_, 7, v___x_1103_);
v___x_1303_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1302_);
v___x_1304_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1304_, 0, v___x_1302_);
lean_ctor_set_uint64(v___x_1304_, sizeof(void*)*1, v___x_1303_);
lean_inc(v_customCanUnfoldPredicate_x3f_1272_);
lean_inc(v_synthPendingDepth_1271_);
lean_inc(v_defEqCtx_x3f_1270_);
lean_inc_ref(v_localInstances_1269_);
lean_inc_ref(v_lctx_1268_);
lean_inc(v_zetaDeltaSet_1267_);
v___x_1305_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1305_, 0, v___x_1304_);
lean_ctor_set(v___x_1305_, 1, v_zetaDeltaSet_1267_);
lean_ctor_set(v___x_1305_, 2, v_lctx_1268_);
lean_ctor_set(v___x_1305_, 3, v_localInstances_1269_);
lean_ctor_set(v___x_1305_, 4, v_defEqCtx_x3f_1270_);
lean_ctor_set(v___x_1305_, 5, v_synthPendingDepth_1271_);
lean_ctor_set(v___x_1305_, 6, v_customCanUnfoldPredicate_x3f_1272_);
lean_ctor_set_uint8(v___x_1305_, sizeof(void*)*7, v_trackZetaDelta_1266_);
lean_ctor_set_uint8(v___x_1305_, sizeof(void*)*7 + 1, v_univApprox_1273_);
lean_ctor_set_uint8(v___x_1305_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1274_);
lean_ctor_set_uint8(v___x_1305_, sizeof(void*)*7 + 3, v_cacheInferType_1275_);
lean_inc(v_a_1157_);
lean_inc(v_a_1114_);
v___x_1306_ = l_Lean_Meta_isExprDefEq(v_a_1114_, v_a_1157_, v___x_1305_, v___y_1109_, v___y_1110_, v___y_1111_);
lean_dec_ref_known(v___x_1305_, 7);
v___y_1178_ = v___x_1306_;
goto v___jp_1177_;
}
}
}
else
{
uint8_t v_trackZetaDelta_1309_; lean_object* v_zetaDeltaSet_1310_; lean_object* v_lctx_1311_; lean_object* v_localInstances_1312_; lean_object* v_defEqCtx_x3f_1313_; lean_object* v_synthPendingDepth_1314_; lean_object* v_customCanUnfoldPredicate_x3f_1315_; uint8_t v_univApprox_1316_; uint8_t v_inTypeClassResolution_1317_; uint8_t v_cacheInferType_1318_; lean_object* v___x_1320_; 
v_trackZetaDelta_1309_ = lean_ctor_get_uint8(v___y_1108_, sizeof(void*)*7);
v_zetaDeltaSet_1310_ = lean_ctor_get(v___y_1108_, 1);
v_lctx_1311_ = lean_ctor_get(v___y_1108_, 2);
v_localInstances_1312_ = lean_ctor_get(v___y_1108_, 3);
v_defEqCtx_x3f_1313_ = lean_ctor_get(v___y_1108_, 4);
v_synthPendingDepth_1314_ = lean_ctor_get(v___y_1108_, 5);
v_customCanUnfoldPredicate_x3f_1315_ = lean_ctor_get(v___y_1108_, 6);
v_univApprox_1316_ = lean_ctor_get_uint8(v___y_1108_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1317_ = lean_ctor_get_uint8(v___y_1108_, sizeof(void*)*7 + 2);
v_cacheInferType_1318_ = lean_ctor_get_uint8(v___y_1108_, sizeof(void*)*7 + 3);
if (v_isShared_1262_ == 0)
{
v___x_1320_ = v___x_1261_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_1325_, 0, v_foApprox_1241_);
lean_ctor_set_uint8(v_reuseFailAlloc_1325_, 1, v_ctxApprox_1242_);
lean_ctor_set_uint8(v_reuseFailAlloc_1325_, 2, v_quasiPatternApprox_1243_);
lean_ctor_set_uint8(v_reuseFailAlloc_1325_, 3, v_constApprox_1244_);
lean_ctor_set_uint8(v_reuseFailAlloc_1325_, 4, v_isDefEqStuckEx_1245_);
lean_ctor_set_uint8(v_reuseFailAlloc_1325_, 5, v_unificationHints_1246_);
lean_ctor_set_uint8(v_reuseFailAlloc_1325_, 6, v_proofIrrelevance_1247_);
lean_ctor_set_uint8(v_reuseFailAlloc_1325_, 8, v_offsetCnstrs_1248_);
lean_ctor_set_uint8(v_reuseFailAlloc_1325_, 9, v_transparency_1249_);
lean_ctor_set_uint8(v_reuseFailAlloc_1325_, 10, v_etaStruct_1250_);
lean_ctor_set_uint8(v_reuseFailAlloc_1325_, 11, v_univApprox_1251_);
lean_ctor_set_uint8(v_reuseFailAlloc_1325_, 12, v_iota_1252_);
lean_ctor_set_uint8(v_reuseFailAlloc_1325_, 13, v_beta_1253_);
lean_ctor_set_uint8(v_reuseFailAlloc_1325_, 14, v_proj_1254_);
lean_ctor_set_uint8(v_reuseFailAlloc_1325_, 15, v_zeta_1255_);
lean_ctor_set_uint8(v_reuseFailAlloc_1325_, 16, v_zetaDelta_1256_);
lean_ctor_set_uint8(v_reuseFailAlloc_1325_, 17, v_zetaUnused_1257_);
lean_ctor_set_uint8(v_reuseFailAlloc_1325_, 18, v_zetaHave_1258_);
lean_ctor_set_uint8(v_reuseFailAlloc_1325_, 19, v_canUnfoldPredicateConfig_1259_);
v___x_1320_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
uint64_t v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
lean_ctor_set_uint8(v___x_1320_, 7, v___x_1103_);
v___x_1321_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1320_);
v___x_1322_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1322_, 0, v___x_1320_);
lean_ctor_set_uint64(v___x_1322_, sizeof(void*)*1, v___x_1321_);
lean_inc(v_customCanUnfoldPredicate_x3f_1315_);
lean_inc(v_synthPendingDepth_1314_);
lean_inc(v_defEqCtx_x3f_1313_);
lean_inc_ref(v_localInstances_1312_);
lean_inc_ref(v_lctx_1311_);
lean_inc(v_zetaDeltaSet_1310_);
v___x_1323_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
lean_ctor_set(v___x_1323_, 1, v_zetaDeltaSet_1310_);
lean_ctor_set(v___x_1323_, 2, v_lctx_1311_);
lean_ctor_set(v___x_1323_, 3, v_localInstances_1312_);
lean_ctor_set(v___x_1323_, 4, v_defEqCtx_x3f_1313_);
lean_ctor_set(v___x_1323_, 5, v_synthPendingDepth_1314_);
lean_ctor_set(v___x_1323_, 6, v_customCanUnfoldPredicate_x3f_1315_);
lean_ctor_set_uint8(v___x_1323_, sizeof(void*)*7, v_trackZetaDelta_1309_);
lean_ctor_set_uint8(v___x_1323_, sizeof(void*)*7 + 1, v_univApprox_1316_);
lean_ctor_set_uint8(v___x_1323_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1317_);
lean_ctor_set_uint8(v___x_1323_, sizeof(void*)*7 + 3, v_cacheInferType_1318_);
lean_inc(v_a_1157_);
lean_inc(v_a_1114_);
v___x_1324_ = l_Lean_Meta_isExprDefEq(v_a_1114_, v_a_1157_, v___x_1323_, v___y_1109_, v___y_1110_, v___y_1111_);
lean_dec_ref_known(v___x_1323_, 7);
v___y_1178_ = v___x_1324_;
goto v___jp_1177_;
}
}
}
}
v___jp_1158_:
{
if (v_____do__lift_1159_ == 0)
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1174_; 
v___x_1168_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__1, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__1);
lean_inc_ref(v_a_1098_);
v___x_1169_ = l_Lean_indentExpr(v_a_1098_);
v___x_1170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1168_);
lean_ctor_set(v___x_1170_, 1, v___x_1169_);
v___x_1171_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__3, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__3_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__3);
v___x_1172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1170_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set_tag(v___x_1154_, 1);
lean_ctor_set(v___x_1154_, 0, v___x_1172_);
v___x_1174_ = v___x_1154_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v___x_1172_);
v___x_1174_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
lean_object* v___x_1175_; 
lean_inc(v_a_1118_);
v___x_1175_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(v___x_1174_, v_a_1114_, v_a_1157_, v_a_1118_, v___x_1101_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
lean_dec_ref(v___x_1174_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_dec_ref_known(v___x_1175_, 1);
v___y_1120_ = v___y_1160_;
v___y_1121_ = v___y_1161_;
v___y_1122_ = v___y_1162_;
v___y_1123_ = v___y_1163_;
v___y_1124_ = v___y_1164_;
v___y_1125_ = v___y_1165_;
v___y_1126_ = v___y_1166_;
v___y_1127_ = v___y_1167_;
goto v___jp_1119_;
}
else
{
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v_a_1118_);
lean_dec_ref(v___x_1100_);
lean_dec_ref(v_a_1098_);
lean_dec(v_a_1094_);
return v___x_1175_;
}
}
}
else
{
lean_dec(v_a_1157_);
lean_del_object(v___x_1154_);
lean_dec(v_a_1114_);
lean_dec(v___x_1101_);
v___y_1120_ = v___y_1160_;
v___y_1121_ = v___y_1161_;
v___y_1122_ = v___y_1162_;
v___y_1123_ = v___y_1163_;
v___y_1124_ = v___y_1164_;
v___y_1125_ = v___y_1165_;
v___y_1126_ = v___y_1166_;
v___y_1127_ = v___y_1167_;
goto v___jp_1119_;
}
}
v___jp_1177_:
{
if (lean_obj_tag(v___y_1178_) == 0)
{
lean_object* v_a_1179_; uint8_t v___x_1180_; 
v_a_1179_ = lean_ctor_get(v___y_1178_, 0);
lean_inc(v_a_1179_);
lean_dec_ref_known(v___y_1178_, 1);
v___x_1180_ = lean_unbox(v_a_1179_);
lean_dec(v_a_1179_);
v_____do__lift_1159_ = v___x_1180_;
v___y_1160_ = v___y_1104_;
v___y_1161_ = v___y_1105_;
v___y_1162_ = v___y_1106_;
v___y_1163_ = v___y_1107_;
v___y_1164_ = v___y_1108_;
v___y_1165_ = v___y_1109_;
v___y_1166_ = v___y_1110_;
v___y_1167_ = v___y_1111_;
goto v___jp_1158_;
}
else
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1188_; 
lean_dec(v_a_1157_);
lean_del_object(v___x_1154_);
lean_dec(v_a_1118_);
lean_dec(v_a_1114_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec(v___x_1101_);
lean_dec_ref(v___x_1100_);
lean_dec_ref(v_a_1098_);
lean_dec(v_a_1094_);
v_a_1181_ = lean_ctor_get(v___y_1178_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___y_1178_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1183_ = v___y_1178_;
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___y_1178_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1181_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
lean_del_object(v___x_1154_);
lean_dec(v_a_1118_);
lean_dec(v_a_1114_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec(v___x_1101_);
lean_dec_ref(v___x_1100_);
lean_dec_ref(v_a_1098_);
lean_dec(v_a_1094_);
v_a_1327_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1156_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1156_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
}
else
{
lean_dec(v_a_1118_);
lean_dec(v_a_1114_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec(v___x_1101_);
lean_dec_ref(v___x_1100_);
lean_dec_ref(v_a_1098_);
lean_dec(v_a_1094_);
return v___x_1152_;
}
v___jp_1119_:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_Lean_Meta_getMVars(v_a_1098_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; lean_object* v___x_1130_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_a_1129_);
lean_dec_ref_known(v___x_1128_, 1);
v___x_1130_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(v_a_1129_, v_mvarCounter_1099_, v___y_1125_);
lean_dec(v_a_1129_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1131_; lean_object* v___x_1132_; 
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_a_1131_);
lean_dec_ref_known(v___x_1130_, 1);
v___x_1132_ = l_Lean_Elab_Tactic_logUnassignedAndAbort(v_a_1131_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
lean_dec(v_a_1131_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v___x_1133_; 
lean_dec_ref_known(v___x_1132_, 1);
v___x_1133_ = l_Lean_Elab_Tactic_pushGoal___redArg(v_a_1094_, v___y_1121_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
lean_dec_ref_known(v___x_1133_, 1);
v___x_1134_ = l_Lean_Name_mkStr1(v___x_1100_);
v___x_1135_ = l_Lean_Elab_Tactic_closeMainGoal___redArg(v___x_1134_, v_a_1118_, v___x_1097_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
return v___x_1135_;
}
else
{
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v_a_1118_);
lean_dec_ref(v___x_1100_);
return v___x_1133_;
}
}
else
{
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v_a_1118_);
lean_dec_ref(v___x_1100_);
lean_dec(v_a_1094_);
return v___x_1132_;
}
}
else
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v_a_1118_);
lean_dec_ref(v___x_1100_);
lean_dec(v_a_1094_);
v_a_1136_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1138_ = v___x_1130_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1130_);
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
else
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v_a_1118_);
lean_dec_ref(v___x_1100_);
lean_dec(v_a_1094_);
v_a_1144_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1146_ = v___x_1128_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1128_);
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
}
else
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1344_; 
lean_dec(v_a_1114_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec(v___x_1101_);
lean_dec_ref(v___x_1100_);
lean_dec_ref(v_a_1098_);
lean_dec(v_a_1094_);
v_a_1337_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1339_ = v___x_1117_;
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1117_);
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
else
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1352_; 
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec(v___x_1101_);
lean_dec_ref(v___x_1100_);
lean_dec_ref(v_a_1098_);
lean_dec(v_a_1095_);
lean_dec(v_a_1094_);
v_a_1345_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1347_ = v___x_1113_;
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1113_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___boxed(lean_object** _args){
lean_object* v_a_1353_ = _args[0];
lean_object* v_a_1354_ = _args[1];
lean_object* v___x_1355_ = _args[2];
lean_object* v___x_1356_ = _args[3];
lean_object* v_a_1357_ = _args[4];
lean_object* v_mvarCounter_1358_ = _args[5];
lean_object* v___x_1359_ = _args[6];
lean_object* v___x_1360_ = _args[7];
lean_object* v_useReducible_1361_ = _args[8];
lean_object* v___x_1362_ = _args[9];
lean_object* v___y_1363_ = _args[10];
lean_object* v___y_1364_ = _args[11];
lean_object* v___y_1365_ = _args[12];
lean_object* v___y_1366_ = _args[13];
lean_object* v___y_1367_ = _args[14];
lean_object* v___y_1368_ = _args[15];
lean_object* v___y_1369_ = _args[16];
lean_object* v___y_1370_ = _args[17];
lean_object* v___y_1371_ = _args[18];
_start:
{
uint8_t v___x_93658__boxed_1372_; uint8_t v___x_93659__boxed_1373_; uint8_t v_useReducible_boxed_1374_; uint8_t v___x_93663__boxed_1375_; lean_object* v_res_1376_; 
v___x_93658__boxed_1372_ = lean_unbox(v___x_1355_);
v___x_93659__boxed_1373_ = lean_unbox(v___x_1356_);
v_useReducible_boxed_1374_ = lean_unbox(v_useReducible_1361_);
v___x_93663__boxed_1375_ = lean_unbox(v___x_1362_);
v_res_1376_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3(v_a_1353_, v_a_1354_, v___x_93658__boxed_1372_, v___x_93659__boxed_1373_, v_a_1357_, v_mvarCounter_1358_, v___x_1359_, v___x_1360_, v_useReducible_boxed_1374_, v___x_93663__boxed_1375_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec(v_mvarCounter_1358_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4(lean_object* v_a_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v___x_1387_; lean_object* v_infoState_1388_; lean_object* v_env_1389_; lean_object* v_nextMacroScope_1390_; lean_object* v_ngen_1391_; lean_object* v_auxDeclNGen_1392_; lean_object* v_traceState_1393_; lean_object* v_cache_1394_; lean_object* v_messages_1395_; lean_object* v_snapshotTasks_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1417_; 
v___x_1387_ = lean_st_ref_take(v___y_1385_);
v_infoState_1388_ = lean_ctor_get(v___x_1387_, 7);
v_env_1389_ = lean_ctor_get(v___x_1387_, 0);
v_nextMacroScope_1390_ = lean_ctor_get(v___x_1387_, 1);
v_ngen_1391_ = lean_ctor_get(v___x_1387_, 2);
v_auxDeclNGen_1392_ = lean_ctor_get(v___x_1387_, 3);
v_traceState_1393_ = lean_ctor_get(v___x_1387_, 4);
v_cache_1394_ = lean_ctor_get(v___x_1387_, 5);
v_messages_1395_ = lean_ctor_get(v___x_1387_, 6);
v_snapshotTasks_1396_ = lean_ctor_get(v___x_1387_, 8);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1398_ = v___x_1387_;
v_isShared_1399_ = v_isSharedCheck_1417_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_snapshotTasks_1396_);
lean_inc(v_infoState_1388_);
lean_inc(v_messages_1395_);
lean_inc(v_cache_1394_);
lean_inc(v_traceState_1393_);
lean_inc(v_auxDeclNGen_1392_);
lean_inc(v_ngen_1391_);
lean_inc(v_nextMacroScope_1390_);
lean_inc(v_env_1389_);
lean_dec(v___x_1387_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1417_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
uint8_t v_enabled_1400_; lean_object* v_assignment_1401_; lean_object* v_lazyAssignment_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1415_; 
v_enabled_1400_ = lean_ctor_get_uint8(v_infoState_1388_, sizeof(void*)*3);
v_assignment_1401_ = lean_ctor_get(v_infoState_1388_, 0);
v_lazyAssignment_1402_ = lean_ctor_get(v_infoState_1388_, 1);
v_isSharedCheck_1415_ = !lean_is_exclusive(v_infoState_1388_);
if (v_isSharedCheck_1415_ == 0)
{
lean_object* v_unused_1416_; 
v_unused_1416_ = lean_ctor_get(v_infoState_1388_, 2);
lean_dec(v_unused_1416_);
v___x_1404_ = v_infoState_1388_;
v_isShared_1405_ = v_isSharedCheck_1415_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_lazyAssignment_1402_);
lean_inc(v_assignment_1401_);
lean_dec(v_infoState_1388_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1415_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1407_; 
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 2, v_a_1377_);
v___x_1407_ = v___x_1404_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_assignment_1401_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v_lazyAssignment_1402_);
lean_ctor_set(v_reuseFailAlloc_1414_, 2, v_a_1377_);
lean_ctor_set_uint8(v_reuseFailAlloc_1414_, sizeof(void*)*3, v_enabled_1400_);
v___x_1407_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
lean_object* v___x_1409_; 
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 7, v___x_1407_);
v___x_1409_ = v___x_1398_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_env_1389_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v_nextMacroScope_1390_);
lean_ctor_set(v_reuseFailAlloc_1413_, 2, v_ngen_1391_);
lean_ctor_set(v_reuseFailAlloc_1413_, 3, v_auxDeclNGen_1392_);
lean_ctor_set(v_reuseFailAlloc_1413_, 4, v_traceState_1393_);
lean_ctor_set(v_reuseFailAlloc_1413_, 5, v_cache_1394_);
lean_ctor_set(v_reuseFailAlloc_1413_, 6, v_messages_1395_);
lean_ctor_set(v_reuseFailAlloc_1413_, 7, v___x_1407_);
lean_ctor_set(v_reuseFailAlloc_1413_, 8, v_snapshotTasks_1396_);
v___x_1409_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1410_ = lean_st_ref_put(v___y_1385_, v___x_1409_);
v___x_1411_ = lean_box(0);
v___x_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1411_);
return v___x_1412_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___boxed(lean_object* v_a_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4(v_a_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
return v_res_1428_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___redArg(lean_object* v_a_1429_, lean_object* v_x_1430_){
_start:
{
if (lean_obj_tag(v_x_1430_) == 0)
{
uint8_t v___x_1431_; 
v___x_1431_ = 0;
return v___x_1431_;
}
else
{
lean_object* v_key_1432_; lean_object* v_tail_1433_; uint8_t v___x_1434_; 
v_key_1432_ = lean_ctor_get(v_x_1430_, 0);
v_tail_1433_ = lean_ctor_get(v_x_1430_, 2);
v___x_1434_ = lean_expr_eqv(v_key_1432_, v_a_1429_);
if (v___x_1434_ == 0)
{
v_x_1430_ = v_tail_1433_;
goto _start;
}
else
{
return v___x_1434_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___redArg___boxed(lean_object* v_a_1436_, lean_object* v_x_1437_){
_start:
{
uint8_t v_res_1438_; lean_object* v_r_1439_; 
v_res_1438_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___redArg(v_a_1436_, v_x_1437_);
lean_dec(v_x_1437_);
lean_dec_ref(v_a_1436_);
v_r_1439_ = lean_box(v_res_1438_);
return v_r_1439_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(lean_object* v_m_1440_, lean_object* v_a_1441_){
_start:
{
lean_object* v_buckets_1442_; lean_object* v___x_1443_; uint64_t v___x_1444_; uint64_t v___x_1445_; uint64_t v___x_1446_; uint64_t v_fold_1447_; uint64_t v___x_1448_; uint64_t v___x_1449_; uint64_t v___x_1450_; size_t v___x_1451_; size_t v___x_1452_; size_t v___x_1453_; size_t v___x_1454_; size_t v___x_1455_; lean_object* v___x_1456_; uint8_t v___x_1457_; 
v_buckets_1442_ = lean_ctor_get(v_m_1440_, 1);
v___x_1443_ = lean_array_get_size(v_buckets_1442_);
v___x_1444_ = l_Lean_Expr_hash(v_a_1441_);
v___x_1445_ = 32ULL;
v___x_1446_ = lean_uint64_shift_right(v___x_1444_, v___x_1445_);
v_fold_1447_ = lean_uint64_xor(v___x_1444_, v___x_1446_);
v___x_1448_ = 16ULL;
v___x_1449_ = lean_uint64_shift_right(v_fold_1447_, v___x_1448_);
v___x_1450_ = lean_uint64_xor(v_fold_1447_, v___x_1449_);
v___x_1451_ = lean_uint64_to_usize(v___x_1450_);
v___x_1452_ = lean_usize_of_nat(v___x_1443_);
v___x_1453_ = ((size_t)1ULL);
v___x_1454_ = lean_usize_sub(v___x_1452_, v___x_1453_);
v___x_1455_ = lean_usize_land(v___x_1451_, v___x_1454_);
v___x_1456_ = lean_array_uget_borrowed(v_buckets_1442_, v___x_1455_);
v___x_1457_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___redArg(v_a_1441_, v___x_1456_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg___boxed(lean_object* v_m_1458_, lean_object* v_a_1459_){
_start:
{
uint8_t v_res_1460_; lean_object* v_r_1461_; 
v_res_1460_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(v_m_1458_, v_a_1459_);
lean_dec_ref(v_a_1459_);
lean_dec_ref(v_m_1458_);
v_r_1461_ = lean_box(v_res_1460_);
return v_r_1461_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13_spec__15_spec__20___redArg(lean_object* v_x_1462_, lean_object* v_x_1463_){
_start:
{
if (lean_obj_tag(v_x_1463_) == 0)
{
return v_x_1462_;
}
else
{
lean_object* v_key_1464_; lean_object* v_value_1465_; lean_object* v_tail_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1489_; 
v_key_1464_ = lean_ctor_get(v_x_1463_, 0);
v_value_1465_ = lean_ctor_get(v_x_1463_, 1);
v_tail_1466_ = lean_ctor_get(v_x_1463_, 2);
v_isSharedCheck_1489_ = !lean_is_exclusive(v_x_1463_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1468_ = v_x_1463_;
v_isShared_1469_ = v_isSharedCheck_1489_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_tail_1466_);
lean_inc(v_value_1465_);
lean_inc(v_key_1464_);
lean_dec(v_x_1463_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1489_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1470_; uint64_t v___x_1471_; uint64_t v___x_1472_; uint64_t v___x_1473_; uint64_t v_fold_1474_; uint64_t v___x_1475_; uint64_t v___x_1476_; uint64_t v___x_1477_; size_t v___x_1478_; size_t v___x_1479_; size_t v___x_1480_; size_t v___x_1481_; size_t v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1485_; 
v___x_1470_ = lean_array_get_size(v_x_1462_);
v___x_1471_ = l_Lean_Expr_hash(v_key_1464_);
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
v___x_1483_ = lean_array_uget_borrowed(v_x_1462_, v___x_1482_);
lean_inc(v___x_1483_);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 2, v___x_1483_);
v___x_1485_ = v___x_1468_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_key_1464_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v_value_1465_);
lean_ctor_set(v_reuseFailAlloc_1488_, 2, v___x_1483_);
v___x_1485_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
lean_object* v___x_1486_; 
v___x_1486_ = lean_array_uset(v_x_1462_, v___x_1482_, v___x_1485_);
v_x_1462_ = v___x_1486_;
v_x_1463_ = v_tail_1466_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13_spec__15___redArg(lean_object* v_i_1490_, lean_object* v_source_1491_, lean_object* v_target_1492_){
_start:
{
lean_object* v___x_1493_; uint8_t v___x_1494_; 
v___x_1493_ = lean_array_get_size(v_source_1491_);
v___x_1494_ = lean_nat_dec_lt(v_i_1490_, v___x_1493_);
if (v___x_1494_ == 0)
{
lean_dec_ref(v_source_1491_);
lean_dec(v_i_1490_);
return v_target_1492_;
}
else
{
lean_object* v_es_1495_; lean_object* v___x_1496_; lean_object* v_source_1497_; lean_object* v_target_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v_es_1495_ = lean_array_fget(v_source_1491_, v_i_1490_);
v___x_1496_ = lean_box(0);
v_source_1497_ = lean_array_fset(v_source_1491_, v_i_1490_, v___x_1496_);
v_target_1498_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13_spec__15_spec__20___redArg(v_target_1492_, v_es_1495_);
v___x_1499_ = lean_unsigned_to_nat(1u);
v___x_1500_ = lean_nat_add(v_i_1490_, v___x_1499_);
lean_dec(v_i_1490_);
v_i_1490_ = v___x_1500_;
v_source_1491_ = v_source_1497_;
v_target_1492_ = v_target_1498_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13___redArg(lean_object* v_data_1502_){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v_nbuckets_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1503_ = lean_array_get_size(v_data_1502_);
v___x_1504_ = lean_unsigned_to_nat(2u);
v_nbuckets_1505_ = lean_nat_mul(v___x_1503_, v___x_1504_);
v___x_1506_ = lean_unsigned_to_nat(0u);
v___x_1507_ = lean_box(0);
v___x_1508_ = lean_mk_array(v_nbuckets_1505_, v___x_1507_);
v___x_1509_ = lean_array_propagate_mark(v_data_1502_, v___x_1508_);
v___x_1510_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13_spec__15___redArg(v___x_1506_, v_data_1502_, v___x_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(lean_object* v_m_1511_, lean_object* v_a_1512_, lean_object* v_b_1513_){
_start:
{
lean_object* v_size_1514_; lean_object* v_buckets_1515_; lean_object* v___x_1516_; uint64_t v___x_1517_; uint64_t v___x_1518_; uint64_t v___x_1519_; uint64_t v_fold_1520_; uint64_t v___x_1521_; uint64_t v___x_1522_; uint64_t v___x_1523_; size_t v___x_1524_; size_t v___x_1525_; size_t v___x_1526_; size_t v___x_1527_; size_t v___x_1528_; lean_object* v_bkt_1529_; uint8_t v___x_1530_; 
v_size_1514_ = lean_ctor_get(v_m_1511_, 0);
v_buckets_1515_ = lean_ctor_get(v_m_1511_, 1);
v___x_1516_ = lean_array_get_size(v_buckets_1515_);
v___x_1517_ = l_Lean_Expr_hash(v_a_1512_);
v___x_1518_ = 32ULL;
v___x_1519_ = lean_uint64_shift_right(v___x_1517_, v___x_1518_);
v_fold_1520_ = lean_uint64_xor(v___x_1517_, v___x_1519_);
v___x_1521_ = 16ULL;
v___x_1522_ = lean_uint64_shift_right(v_fold_1520_, v___x_1521_);
v___x_1523_ = lean_uint64_xor(v_fold_1520_, v___x_1522_);
v___x_1524_ = lean_uint64_to_usize(v___x_1523_);
v___x_1525_ = lean_usize_of_nat(v___x_1516_);
v___x_1526_ = ((size_t)1ULL);
v___x_1527_ = lean_usize_sub(v___x_1525_, v___x_1526_);
v___x_1528_ = lean_usize_land(v___x_1524_, v___x_1527_);
v_bkt_1529_ = lean_array_uget_borrowed(v_buckets_1515_, v___x_1528_);
v___x_1530_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___redArg(v_a_1512_, v_bkt_1529_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1551_; 
lean_inc_ref(v_buckets_1515_);
lean_inc(v_size_1514_);
v_isSharedCheck_1551_ = !lean_is_exclusive(v_m_1511_);
if (v_isSharedCheck_1551_ == 0)
{
lean_object* v_unused_1552_; lean_object* v_unused_1553_; 
v_unused_1552_ = lean_ctor_get(v_m_1511_, 1);
lean_dec(v_unused_1552_);
v_unused_1553_ = lean_ctor_get(v_m_1511_, 0);
lean_dec(v_unused_1553_);
v___x_1532_ = v_m_1511_;
v_isShared_1533_ = v_isSharedCheck_1551_;
goto v_resetjp_1531_;
}
else
{
lean_dec(v_m_1511_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1551_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1534_; lean_object* v_size_x27_1535_; lean_object* v___x_1536_; lean_object* v_buckets_x27_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; uint8_t v___x_1543_; 
v___x_1534_ = lean_unsigned_to_nat(1u);
v_size_x27_1535_ = lean_nat_add(v_size_1514_, v___x_1534_);
lean_dec(v_size_1514_);
lean_inc(v_bkt_1529_);
v___x_1536_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1536_, 0, v_a_1512_);
lean_ctor_set(v___x_1536_, 1, v_b_1513_);
lean_ctor_set(v___x_1536_, 2, v_bkt_1529_);
v_buckets_x27_1537_ = lean_array_uset(v_buckets_1515_, v___x_1528_, v___x_1536_);
v___x_1538_ = lean_unsigned_to_nat(4u);
v___x_1539_ = lean_nat_mul(v_size_x27_1535_, v___x_1538_);
v___x_1540_ = lean_unsigned_to_nat(3u);
v___x_1541_ = lean_nat_div(v___x_1539_, v___x_1540_);
lean_dec(v___x_1539_);
v___x_1542_ = lean_array_get_size(v_buckets_x27_1537_);
v___x_1543_ = lean_nat_dec_le(v___x_1541_, v___x_1542_);
lean_dec(v___x_1541_);
if (v___x_1543_ == 0)
{
lean_object* v_val_1544_; lean_object* v___x_1546_; 
v_val_1544_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13___redArg(v_buckets_x27_1537_);
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 1, v_val_1544_);
lean_ctor_set(v___x_1532_, 0, v_size_x27_1535_);
v___x_1546_ = v___x_1532_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_size_x27_1535_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v_val_1544_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
else
{
lean_object* v___x_1549_; 
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 1, v_buckets_x27_1537_);
lean_ctor_set(v___x_1532_, 0, v_size_x27_1535_);
v___x_1549_ = v___x_1532_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_size_x27_1535_);
lean_ctor_set(v_reuseFailAlloc_1550_, 1, v_buckets_x27_1537_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
}
else
{
lean_dec(v_b_1513_);
lean_dec_ref(v_a_1512_);
return v_m_1511_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg(lean_object* v_mvarId_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
lean_object* v___x_1558_; lean_object* v_mctx_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1558_ = lean_st_ref_get(v___y_1556_);
v_mctx_1559_ = lean_ctor_get(v___x_1558_, 0);
lean_inc_ref(v_mctx_1559_);
lean_dec(v___x_1558_);
v___x_1560_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_1559_, v_mvarId_1554_);
lean_dec_ref(v_mctx_1559_);
v___x_1561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1560_);
v___x_1562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1561_);
lean_ctor_set(v___x_1562_, 1, v___y_1555_);
v___x_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg___boxed(lean_object* v_mvarId_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg(v_mvarId_1564_, v___y_1565_, v___y_1566_);
lean_dec(v___y_1566_);
lean_dec(v_mvarId_1564_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__15___redArg(lean_object* v_mvarId_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v___x_1573_; lean_object* v_mctx_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1573_ = lean_st_ref_get(v___y_1571_);
v_mctx_1574_ = lean_ctor_get(v___x_1573_, 0);
lean_inc_ref(v_mctx_1574_);
lean_dec(v___x_1573_);
v___x_1575_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_1574_, v_mvarId_1569_);
lean_dec_ref(v_mctx_1574_);
v___x_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
v___x_1577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1576_);
lean_ctor_set(v___x_1577_, 1, v___y_1570_);
v___x_1578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__15___redArg___boxed(lean_object* v_mvarId_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__15___redArg(v_mvarId_1579_, v___y_1580_, v___y_1581_);
lean_dec(v___y_1581_);
lean_dec(v_mvarId_1579_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(lean_object* v_mvarId_1588_, lean_object* v_e_1589_, lean_object* v_a_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v_d_1601_; lean_object* v_b_1602_; lean_object* v___y_1603_; uint8_t v___x_1609_; 
v___x_1609_ = l_Lean_Expr_hasExprMVar(v_e_1589_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
lean_dec_ref(v_e_1589_);
v___x_1610_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___closed__0));
v___x_1611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1610_);
lean_ctor_set(v___x_1611_, 1, v_a_1590_);
v___x_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1611_);
return v___x_1612_;
}
else
{
uint8_t v___x_1613_; 
v___x_1613_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(v_a_1590_, v_e_1589_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1614_ = lean_box(0);
lean_inc_ref(v_e_1589_);
v___x_1615_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(v_a_1590_, v_e_1589_, v___x_1614_);
switch(lean_obj_tag(v_e_1589_))
{
case 11:
{
lean_object* v_struct_1616_; 
v_struct_1616_ = lean_ctor_get(v_e_1589_, 2);
lean_inc_ref(v_struct_1616_);
lean_dec_ref_known(v_e_1589_, 3);
v_e_1589_ = v_struct_1616_;
v_a_1590_ = v___x_1615_;
goto _start;
}
case 7:
{
lean_object* v_binderType_1618_; lean_object* v_body_1619_; 
v_binderType_1618_ = lean_ctor_get(v_e_1589_, 1);
lean_inc_ref(v_binderType_1618_);
v_body_1619_ = lean_ctor_get(v_e_1589_, 2);
lean_inc_ref(v_body_1619_);
lean_dec_ref_known(v_e_1589_, 3);
v_d_1601_ = v_binderType_1618_;
v_b_1602_ = v_body_1619_;
v___y_1603_ = v___x_1615_;
goto v___jp_1600_;
}
case 6:
{
lean_object* v_binderType_1620_; lean_object* v_body_1621_; 
v_binderType_1620_ = lean_ctor_get(v_e_1589_, 1);
lean_inc_ref(v_binderType_1620_);
v_body_1621_ = lean_ctor_get(v_e_1589_, 2);
lean_inc_ref(v_body_1621_);
lean_dec_ref_known(v_e_1589_, 3);
v_d_1601_ = v_binderType_1620_;
v_b_1602_ = v_body_1621_;
v___y_1603_ = v___x_1615_;
goto v___jp_1600_;
}
case 8:
{
lean_object* v_type_1622_; lean_object* v_value_1623_; lean_object* v_body_1624_; lean_object* v___x_1625_; 
v_type_1622_ = lean_ctor_get(v_e_1589_, 1);
lean_inc_ref(v_type_1622_);
v_value_1623_ = lean_ctor_get(v_e_1589_, 2);
lean_inc_ref(v_value_1623_);
v_body_1624_ = lean_ctor_get(v_e_1589_, 3);
lean_inc_ref(v_body_1624_);
lean_dec_ref_known(v_e_1589_, 4);
v___x_1625_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_1588_, v_type_1622_, v___x_1615_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; lean_object* v_fst_1627_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_a_1626_);
v_fst_1627_ = lean_ctor_get(v_a_1626_, 0);
if (lean_obj_tag(v_fst_1627_) == 0)
{
lean_dec(v_a_1626_);
lean_dec_ref(v_body_1624_);
lean_dec_ref(v_value_1623_);
return v___x_1625_;
}
else
{
lean_object* v_snd_1628_; lean_object* v___x_1629_; 
lean_dec_ref_known(v___x_1625_, 1);
v_snd_1628_ = lean_ctor_get(v_a_1626_, 1);
lean_inc(v_snd_1628_);
lean_dec(v_a_1626_);
v___x_1629_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_1588_, v_value_1623_, v_snd_1628_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; lean_object* v_fst_1631_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_a_1630_);
v_fst_1631_ = lean_ctor_get(v_a_1630_, 0);
if (lean_obj_tag(v_fst_1631_) == 0)
{
lean_dec(v_a_1630_);
lean_dec_ref(v_body_1624_);
return v___x_1629_;
}
else
{
lean_object* v_snd_1632_; 
lean_dec_ref_known(v___x_1629_, 1);
v_snd_1632_ = lean_ctor_get(v_a_1630_, 1);
lean_inc(v_snd_1632_);
lean_dec(v_a_1630_);
v_e_1589_ = v_body_1624_;
v_a_1590_ = v_snd_1632_;
goto _start;
}
}
else
{
lean_dec_ref(v_body_1624_);
return v___x_1629_;
}
}
}
else
{
lean_dec_ref(v_body_1624_);
lean_dec_ref(v_value_1623_);
return v___x_1625_;
}
}
case 10:
{
lean_object* v_expr_1634_; 
v_expr_1634_ = lean_ctor_get(v_e_1589_, 1);
lean_inc_ref(v_expr_1634_);
lean_dec_ref_known(v_e_1589_, 2);
v_e_1589_ = v_expr_1634_;
v_a_1590_ = v___x_1615_;
goto _start;
}
case 5:
{
lean_object* v_fn_1636_; lean_object* v_arg_1637_; lean_object* v___x_1638_; 
v_fn_1636_ = lean_ctor_get(v_e_1589_, 0);
lean_inc_ref(v_fn_1636_);
v_arg_1637_ = lean_ctor_get(v_e_1589_, 1);
lean_inc_ref(v_arg_1637_);
lean_dec_ref_known(v_e_1589_, 2);
v___x_1638_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_1588_, v_fn_1636_, v___x_1615_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v_a_1639_; lean_object* v_fst_1640_; 
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_a_1639_);
v_fst_1640_ = lean_ctor_get(v_a_1639_, 0);
if (lean_obj_tag(v_fst_1640_) == 0)
{
lean_dec(v_a_1639_);
lean_dec_ref(v_arg_1637_);
return v___x_1638_;
}
else
{
lean_object* v_snd_1641_; 
lean_dec_ref_known(v___x_1638_, 1);
v_snd_1641_ = lean_ctor_get(v_a_1639_, 1);
lean_inc(v_snd_1641_);
lean_dec(v_a_1639_);
v_e_1589_ = v_arg_1637_;
v_a_1590_ = v_snd_1641_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_1637_);
return v___x_1638_;
}
}
case 2:
{
lean_object* v_mvarId_1643_; lean_object* v___x_1644_; 
v_mvarId_1643_ = lean_ctor_get(v_e_1589_, 0);
lean_inc(v_mvarId_1643_);
lean_dec_ref_known(v_e_1589_, 1);
v___x_1644_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7(v_mvarId_1588_, v_mvarId_1643_, v___x_1615_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
return v___x_1644_;
}
default: 
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
lean_dec_ref(v_e_1589_);
v___x_1645_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___closed__0));
v___x_1646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1645_);
lean_ctor_set(v___x_1646_, 1, v___x_1615_);
v___x_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1646_);
return v___x_1647_;
}
}
}
else
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
lean_dec_ref(v_e_1589_);
v___x_1648_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___closed__0));
v___x_1649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
lean_ctor_set(v___x_1649_, 1, v_a_1590_);
v___x_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1649_);
return v___x_1650_;
}
}
v___jp_1600_:
{
lean_object* v___x_1604_; 
v___x_1604_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_1588_, v_d_1601_, v___y_1603_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v_a_1605_; lean_object* v_fst_1606_; 
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_a_1605_);
v_fst_1606_ = lean_ctor_get(v_a_1605_, 0);
if (lean_obj_tag(v_fst_1606_) == 0)
{
lean_dec(v_a_1605_);
lean_dec_ref(v_b_1602_);
return v___x_1604_;
}
else
{
lean_object* v_snd_1607_; 
lean_dec_ref_known(v___x_1604_, 1);
v_snd_1607_ = lean_ctor_get(v_a_1605_, 1);
lean_inc(v_snd_1607_);
lean_dec(v_a_1605_);
v_e_1589_ = v_b_1602_;
v_a_1590_ = v_snd_1607_;
goto _start;
}
}
else
{
lean_dec_ref(v_b_1602_);
return v___x_1604_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7(lean_object* v_mvarId_1651_, lean_object* v_mvarId_x27_1652_, lean_object* v_a_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
uint8_t v___x_1663_; 
v___x_1663_ = l_Lean_instBEqMVarId_beq(v_mvarId_1651_, v_mvarId_x27_1652_);
if (v___x_1663_ == 0)
{
lean_object* v___x_1664_; 
v___x_1664_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__15___redArg(v_mvarId_x27_1652_, v_a_1653_, v___y_1659_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1748_; 
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1667_ = v___x_1664_;
v_isShared_1668_ = v_isSharedCheck_1748_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1664_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1748_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v_fst_1669_; 
v_fst_1669_ = lean_ctor_get(v_a_1665_, 0);
lean_inc(v_fst_1669_);
if (lean_obj_tag(v_fst_1669_) == 0)
{
lean_object* v_snd_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1688_; 
lean_dec(v_mvarId_x27_1652_);
v_snd_1670_ = lean_ctor_get(v_a_1665_, 1);
v_isSharedCheck_1688_ = !lean_is_exclusive(v_a_1665_);
if (v_isSharedCheck_1688_ == 0)
{
lean_object* v_unused_1689_; 
v_unused_1689_ = lean_ctor_get(v_a_1665_, 0);
lean_dec(v_unused_1689_);
v___x_1672_ = v_a_1665_;
v_isShared_1673_ = v_isSharedCheck_1688_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_snd_1670_);
lean_dec(v_a_1665_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1688_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1687_; 
v_a_1674_ = lean_ctor_get(v_fst_1669_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v_fst_1669_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1676_ = v_fst_1669_;
v_isShared_1677_ = v_isSharedCheck_1687_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v_fst_1669_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1687_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1679_; 
if (v_isShared_1677_ == 0)
{
v___x_1679_ = v___x_1676_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1674_);
v___x_1679_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
lean_object* v___x_1681_; 
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 0, v___x_1679_);
v___x_1681_ = v___x_1672_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1679_);
lean_ctor_set(v_reuseFailAlloc_1685_, 1, v_snd_1670_);
v___x_1681_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
lean_object* v___x_1683_; 
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 0, v___x_1681_);
v___x_1683_ = v___x_1667_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1681_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
}
}
else
{
lean_object* v_a_1690_; 
lean_del_object(v___x_1667_);
v_a_1690_ = lean_ctor_get(v_fst_1669_, 0);
lean_inc(v_a_1690_);
lean_dec_ref_known(v_fst_1669_, 1);
if (lean_obj_tag(v_a_1690_) == 0)
{
lean_object* v_snd_1691_; lean_object* v___x_1692_; 
v_snd_1691_ = lean_ctor_get(v_a_1665_, 1);
lean_inc(v_snd_1691_);
lean_dec(v_a_1665_);
v___x_1692_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg(v_mvarId_x27_1652_, v_snd_1691_, v___y_1659_);
lean_dec(v_mvarId_x27_1652_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1736_; 
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1695_ = v___x_1692_;
v_isShared_1696_ = v_isSharedCheck_1736_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1692_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1736_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v_fst_1697_; 
v_fst_1697_ = lean_ctor_get(v_a_1693_, 0);
lean_inc(v_fst_1697_);
if (lean_obj_tag(v_fst_1697_) == 0)
{
lean_object* v_snd_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1716_; 
v_snd_1698_ = lean_ctor_get(v_a_1693_, 1);
v_isSharedCheck_1716_ = !lean_is_exclusive(v_a_1693_);
if (v_isSharedCheck_1716_ == 0)
{
lean_object* v_unused_1717_; 
v_unused_1717_ = lean_ctor_get(v_a_1693_, 0);
lean_dec(v_unused_1717_);
v___x_1700_ = v_a_1693_;
v_isShared_1701_ = v_isSharedCheck_1716_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_snd_1698_);
lean_dec(v_a_1693_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1716_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1715_; 
v_a_1702_ = lean_ctor_get(v_fst_1697_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v_fst_1697_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1704_ = v_fst_1697_;
v_isShared_1705_ = v_isSharedCheck_1715_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v_fst_1697_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1715_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_a_1702_);
v___x_1707_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
lean_object* v___x_1709_; 
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 0, v___x_1707_);
v___x_1709_ = v___x_1700_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1707_);
lean_ctor_set(v_reuseFailAlloc_1713_, 1, v_snd_1698_);
v___x_1709_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
lean_object* v___x_1711_; 
if (v_isShared_1696_ == 0)
{
lean_ctor_set(v___x_1695_, 0, v___x_1709_);
v___x_1711_ = v___x_1695_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v___x_1709_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
}
}
}
else
{
lean_object* v_a_1718_; 
v_a_1718_ = lean_ctor_get(v_fst_1697_, 0);
lean_inc(v_a_1718_);
lean_dec_ref_known(v_fst_1697_, 1);
if (lean_obj_tag(v_a_1718_) == 0)
{
lean_object* v_snd_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1730_; 
v_snd_1719_ = lean_ctor_get(v_a_1693_, 1);
v_isSharedCheck_1730_ = !lean_is_exclusive(v_a_1693_);
if (v_isSharedCheck_1730_ == 0)
{
lean_object* v_unused_1731_; 
v_unused_1731_ = lean_ctor_get(v_a_1693_, 0);
lean_dec(v_unused_1731_);
v___x_1721_ = v_a_1693_;
v_isShared_1722_ = v_isSharedCheck_1730_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_snd_1719_);
lean_dec(v_a_1693_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1730_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1723_; lean_object* v___x_1725_; 
v___x_1723_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___closed__0));
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 0, v___x_1723_);
v___x_1725_ = v___x_1721_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1723_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v_snd_1719_);
v___x_1725_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
lean_object* v___x_1727_; 
if (v_isShared_1696_ == 0)
{
lean_ctor_set(v___x_1695_, 0, v___x_1725_);
v___x_1727_ = v___x_1695_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1725_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
else
{
lean_object* v_val_1732_; lean_object* v_snd_1733_; lean_object* v_mvarIdPending_1734_; 
lean_del_object(v___x_1695_);
v_val_1732_ = lean_ctor_get(v_a_1718_, 0);
lean_inc(v_val_1732_);
lean_dec_ref_known(v_a_1718_, 1);
v_snd_1733_ = lean_ctor_get(v_a_1693_, 1);
lean_inc(v_snd_1733_);
lean_dec(v_a_1693_);
v_mvarIdPending_1734_ = lean_ctor_get(v_val_1732_, 1);
lean_inc(v_mvarIdPending_1734_);
lean_dec(v_val_1732_);
v_mvarId_x27_1652_ = v_mvarIdPending_1734_;
v_a_1653_ = v_snd_1733_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1744_; 
v_a_1737_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1739_ = v___x_1692_;
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_a_1737_);
lean_dec(v___x_1692_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1742_; 
if (v_isShared_1740_ == 0)
{
v___x_1742_ = v___x_1739_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_a_1737_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
}
else
{
lean_object* v_snd_1745_; lean_object* v_val_1746_; lean_object* v___x_1747_; 
lean_dec(v_mvarId_x27_1652_);
v_snd_1745_ = lean_ctor_get(v_a_1665_, 1);
lean_inc(v_snd_1745_);
lean_dec(v_a_1665_);
v_val_1746_ = lean_ctor_get(v_a_1690_, 0);
lean_inc(v_val_1746_);
lean_dec_ref_known(v_a_1690_, 1);
v___x_1747_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_1651_, v_val_1746_, v_snd_1745_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
return v___x_1747_;
}
}
}
}
else
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1756_; 
lean_dec(v_mvarId_x27_1652_);
v_a_1749_ = lean_ctor_get(v___x_1664_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1751_ = v___x_1664_;
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1664_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1754_; 
if (v_isShared_1752_ == 0)
{
v___x_1754_ = v___x_1751_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_a_1749_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
}
else
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
lean_dec(v_mvarId_x27_1652_);
v___x_1757_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___closed__1));
v___x_1758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1757_);
lean_ctor_set(v___x_1758_, 1, v_a_1653_);
v___x_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
return v___x_1759_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___boxed(lean_object* v_mvarId_1760_, lean_object* v_mvarId_x27_1761_, lean_object* v_a_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7(v_mvarId_1760_, v_mvarId_x27_1761_, v_a_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v_mvarId_1760_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1___boxed(lean_object* v_mvarId_1773_, lean_object* v_e_1774_, lean_object* v_a_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_1773_, v_e_1774_, v_a_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec(v_mvarId_1773_);
return v_res_1785_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1786_ = lean_box(0);
v___x_1787_ = lean_unsigned_to_nat(16u);
v___x_1788_ = lean_mk_array(v___x_1787_, v___x_1786_);
return v___x_1788_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1789_ = lean_obj_once(&l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0, &l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0_once, _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0);
v___x_1790_ = lean_unsigned_to_nat(0u);
v___x_1791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1790_);
lean_ctor_set(v___x_1791_, 1, v___x_1789_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(lean_object* v_mvarId_1792_, lean_object* v_e_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
uint8_t v___x_1803_; 
v___x_1803_ = l_Lean_Expr_hasExprMVar(v_e_1793_);
if (v___x_1803_ == 0)
{
uint8_t v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
lean_dec_ref(v_e_1793_);
v___x_1804_ = 1;
v___x_1805_ = lean_box(v___x_1804_);
v___x_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
return v___x_1806_;
}
else
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1807_ = lean_obj_once(&l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1, &l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1_once, _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1);
v___x_1808_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_1792_, v_e_1793_, v___x_1807_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1823_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1811_ = v___x_1808_;
v_isShared_1812_ = v_isSharedCheck_1823_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1808_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1823_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v_fst_1813_; 
v_fst_1813_ = lean_ctor_get(v_a_1809_, 0);
lean_inc(v_fst_1813_);
lean_dec(v_a_1809_);
if (lean_obj_tag(v_fst_1813_) == 0)
{
uint8_t v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1817_; 
lean_dec_ref_known(v_fst_1813_, 1);
v___x_1814_ = 0;
v___x_1815_ = lean_box(v___x_1814_);
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 0, v___x_1815_);
v___x_1817_ = v___x_1811_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1815_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
else
{
lean_object* v___x_1819_; lean_object* v___x_1821_; 
lean_dec_ref_known(v_fst_1813_, 1);
v___x_1819_ = lean_box(v___x_1803_);
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 0, v___x_1819_);
v___x_1821_ = v___x_1811_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1819_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
}
else
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
v_a_1824_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1808_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1808_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___boxed(lean_object* v_mvarId_1832_, lean_object* v_e_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(v_mvarId_1832_, v_e_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
lean_dec(v_mvarId_1832_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0(lean_object* v___y_1844_, lean_object* v_mkInfoTree_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v_a_1853_, lean_object* v_a_x3f_1854_){
_start:
{
lean_object* v___x_1856_; lean_object* v_infoState_1857_; lean_object* v_trees_1858_; lean_object* v___x_1859_; 
v___x_1856_ = lean_st_ref_get(v___y_1844_);
v_infoState_1857_ = lean_ctor_get(v___x_1856_, 7);
lean_inc_ref(v_infoState_1857_);
lean_dec(v___x_1856_);
v_trees_1858_ = lean_ctor_get(v_infoState_1857_, 2);
lean_inc_ref(v_trees_1858_);
lean_dec_ref(v_infoState_1857_);
lean_inc(v___y_1844_);
lean_inc_ref(v___y_1852_);
lean_inc(v___y_1851_);
lean_inc_ref(v___y_1850_);
lean_inc(v___y_1849_);
lean_inc_ref(v___y_1848_);
lean_inc(v___y_1847_);
lean_inc_ref(v___y_1846_);
v___x_1859_ = lean_apply_10(v_mkInfoTree_1845_, v_trees_1858_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1844_, lean_box(0));
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1898_; 
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1862_ = v___x_1859_;
v_isShared_1863_ = v_isSharedCheck_1898_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1859_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1898_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1864_; lean_object* v_infoState_1865_; lean_object* v_env_1866_; lean_object* v_nextMacroScope_1867_; lean_object* v_ngen_1868_; lean_object* v_auxDeclNGen_1869_; lean_object* v_traceState_1870_; lean_object* v_cache_1871_; lean_object* v_messages_1872_; lean_object* v_snapshotTasks_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1897_; 
v___x_1864_ = lean_st_ref_take(v___y_1844_);
v_infoState_1865_ = lean_ctor_get(v___x_1864_, 7);
v_env_1866_ = lean_ctor_get(v___x_1864_, 0);
v_nextMacroScope_1867_ = lean_ctor_get(v___x_1864_, 1);
v_ngen_1868_ = lean_ctor_get(v___x_1864_, 2);
v_auxDeclNGen_1869_ = lean_ctor_get(v___x_1864_, 3);
v_traceState_1870_ = lean_ctor_get(v___x_1864_, 4);
v_cache_1871_ = lean_ctor_get(v___x_1864_, 5);
v_messages_1872_ = lean_ctor_get(v___x_1864_, 6);
v_snapshotTasks_1873_ = lean_ctor_get(v___x_1864_, 8);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1875_ = v___x_1864_;
v_isShared_1876_ = v_isSharedCheck_1897_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_snapshotTasks_1873_);
lean_inc(v_infoState_1865_);
lean_inc(v_messages_1872_);
lean_inc(v_cache_1871_);
lean_inc(v_traceState_1870_);
lean_inc(v_auxDeclNGen_1869_);
lean_inc(v_ngen_1868_);
lean_inc(v_nextMacroScope_1867_);
lean_inc(v_env_1866_);
lean_dec(v___x_1864_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1897_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
uint8_t v_enabled_1877_; lean_object* v_assignment_1878_; lean_object* v_lazyAssignment_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1895_; 
v_enabled_1877_ = lean_ctor_get_uint8(v_infoState_1865_, sizeof(void*)*3);
v_assignment_1878_ = lean_ctor_get(v_infoState_1865_, 0);
v_lazyAssignment_1879_ = lean_ctor_get(v_infoState_1865_, 1);
v_isSharedCheck_1895_ = !lean_is_exclusive(v_infoState_1865_);
if (v_isSharedCheck_1895_ == 0)
{
lean_object* v_unused_1896_; 
v_unused_1896_ = lean_ctor_get(v_infoState_1865_, 2);
lean_dec(v_unused_1896_);
v___x_1881_ = v_infoState_1865_;
v_isShared_1882_ = v_isSharedCheck_1895_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_lazyAssignment_1879_);
lean_inc(v_assignment_1878_);
lean_dec(v_infoState_1865_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1895_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1883_; lean_object* v___x_1885_; 
v___x_1883_ = l_Lean_PersistentArray_push___redArg(v_a_1853_, v_a_1860_);
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 2, v___x_1883_);
v___x_1885_ = v___x_1881_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_assignment_1878_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v_lazyAssignment_1879_);
lean_ctor_set(v_reuseFailAlloc_1894_, 2, v___x_1883_);
lean_ctor_set_uint8(v_reuseFailAlloc_1894_, sizeof(void*)*3, v_enabled_1877_);
v___x_1885_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
lean_object* v___x_1887_; 
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 7, v___x_1885_);
v___x_1887_ = v___x_1875_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_env_1866_);
lean_ctor_set(v_reuseFailAlloc_1893_, 1, v_nextMacroScope_1867_);
lean_ctor_set(v_reuseFailAlloc_1893_, 2, v_ngen_1868_);
lean_ctor_set(v_reuseFailAlloc_1893_, 3, v_auxDeclNGen_1869_);
lean_ctor_set(v_reuseFailAlloc_1893_, 4, v_traceState_1870_);
lean_ctor_set(v_reuseFailAlloc_1893_, 5, v_cache_1871_);
lean_ctor_set(v_reuseFailAlloc_1893_, 6, v_messages_1872_);
lean_ctor_set(v_reuseFailAlloc_1893_, 7, v___x_1885_);
lean_ctor_set(v_reuseFailAlloc_1893_, 8, v_snapshotTasks_1873_);
v___x_1887_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1891_; 
v___x_1888_ = lean_st_ref_put(v___y_1844_, v___x_1887_);
v___x_1889_ = lean_box(0);
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 0, v___x_1889_);
v___x_1891_ = v___x_1862_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1889_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1906_; 
lean_dec_ref(v_a_1853_);
v_a_1899_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1901_ = v___x_1859_;
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1859_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1902_ == 0)
{
v___x_1904_ = v___x_1901_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_a_1899_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0___boxed(lean_object* v___y_1907_, lean_object* v_mkInfoTree_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v_a_1916_, lean_object* v_a_x3f_1917_, lean_object* v___y_1918_){
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0(v___y_1907_, v_mkInfoTree_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v_a_1916_, v_a_x3f_1917_);
lean_dec(v_a_x3f_1917_);
lean_dec_ref(v___y_1915_);
lean_dec(v___y_1914_);
lean_dec_ref(v___y_1913_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1907_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(lean_object* v_x_1920_, lean_object* v_mkInfoTree_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v___x_1931_; lean_object* v_infoState_1932_; uint8_t v_enabled_1933_; 
v___x_1931_ = lean_st_ref_get(v___y_1929_);
v_infoState_1932_ = lean_ctor_get(v___x_1931_, 7);
lean_inc_ref(v_infoState_1932_);
lean_dec(v___x_1931_);
v_enabled_1933_ = lean_ctor_get_uint8(v_infoState_1932_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1932_);
if (v_enabled_1933_ == 0)
{
lean_object* v___x_1934_; 
lean_dec_ref(v_mkInfoTree_1921_);
lean_inc(v___y_1929_);
lean_inc_ref(v___y_1928_);
lean_inc(v___y_1927_);
lean_inc_ref(v___y_1926_);
lean_inc(v___y_1925_);
lean_inc_ref(v___y_1924_);
lean_inc(v___y_1923_);
lean_inc_ref(v___y_1922_);
v___x_1934_ = lean_apply_9(v_x_1920_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, lean_box(0));
return v___x_1934_;
}
else
{
lean_object* v___x_1935_; lean_object* v_a_1936_; lean_object* v_r_1937_; 
v___x_1935_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___y_1929_);
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_a_1936_);
lean_dec_ref(v___x_1935_);
lean_inc(v___y_1929_);
lean_inc_ref(v___y_1928_);
lean_inc(v___y_1927_);
lean_inc_ref(v___y_1926_);
lean_inc(v___y_1925_);
lean_inc_ref(v___y_1924_);
lean_inc(v___y_1923_);
lean_inc_ref(v___y_1922_);
v_r_1937_ = lean_apply_9(v_x_1920_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, lean_box(0));
if (lean_obj_tag(v_r_1937_) == 0)
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1962_; 
v_a_1938_ = lean_ctor_get(v_r_1937_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v_r_1937_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1940_ = v_r_1937_;
v_isShared_1941_ = v_isSharedCheck_1962_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v_r_1937_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1962_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
lean_inc(v_a_1938_);
if (v_isShared_1941_ == 0)
{
lean_ctor_set_tag(v___x_1940_, 1);
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1938_);
v___x_1943_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
lean_object* v___x_1944_; 
v___x_1944_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0(v___y_1929_, v_mkInfoTree_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v_a_1936_, v___x_1943_);
lean_dec_ref(v___x_1943_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1951_ == 0)
{
lean_object* v_unused_1952_; 
v_unused_1952_ = lean_ctor_get(v___x_1944_, 0);
lean_dec(v_unused_1952_);
v___x_1946_ = v___x_1944_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_dec(v___x_1944_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 0, v_a_1938_);
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1938_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
else
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1960_; 
lean_dec(v_a_1938_);
v_a_1953_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1955_ = v___x_1944_;
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___x_1944_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1958_; 
if (v_isShared_1956_ == 0)
{
v___x_1958_ = v___x_1955_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_a_1953_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
}
}
else
{
lean_object* v_a_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
v_a_1963_ = lean_ctor_get(v_r_1937_, 0);
lean_inc(v_a_1963_);
lean_dec_ref_known(v_r_1937_, 1);
v___x_1964_ = lean_box(0);
v___x_1965_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0(v___y_1929_, v_mkInfoTree_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v_a_1936_, v___x_1964_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1972_; 
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1972_ == 0)
{
lean_object* v_unused_1973_; 
v_unused_1973_ = lean_ctor_get(v___x_1965_, 0);
lean_dec(v_unused_1973_);
v___x_1967_ = v___x_1965_;
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
else
{
lean_dec(v___x_1965_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1970_; 
if (v_isShared_1968_ == 0)
{
lean_ctor_set_tag(v___x_1967_, 1);
lean_ctor_set(v___x_1967_, 0, v_a_1963_);
v___x_1970_ = v___x_1967_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_a_1963_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
else
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1981_; 
lean_dec(v_a_1963_);
v_a_1974_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1976_ = v___x_1965_;
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1965_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1977_ == 0)
{
v___x_1979_ = v___x_1976_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1974_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___boxed(lean_object* v_x_1982_, lean_object* v_mkInfoTree_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v_x_1982_, v_mkInfoTree_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(lean_object* v_msg_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v_ref_2000_; lean_object* v___x_2001_; lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2010_; 
v_ref_2000_ = lean_ctor_get(v___y_1997_, 2);
v___x_2001_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__2(v_msg_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_2004_ = v___x_2001_;
v_isShared_2005_ = v_isSharedCheck_2010_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v___x_2001_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2010_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2006_; lean_object* v___x_2008_; 
lean_inc(v_ref_2000_);
v___x_2006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2006_, 0, v_ref_2000_);
lean_ctor_set(v___x_2006_, 1, v_a_2002_);
if (v_isShared_2005_ == 0)
{
lean_ctor_set_tag(v___x_2004_, 1);
lean_ctor_set(v___x_2004_, 0, v___x_2006_);
v___x_2008_ = v___x_2004_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_2006_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg___boxed(lean_object* v_msg_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_msg_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__19_spec__21___redArg(lean_object* v_x_2018_, lean_object* v_x_2019_, lean_object* v_x_2020_, lean_object* v_x_2021_){
_start:
{
lean_object* v_ks_2022_; lean_object* v_vs_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2047_; 
v_ks_2022_ = lean_ctor_get(v_x_2018_, 0);
v_vs_2023_ = lean_ctor_get(v_x_2018_, 1);
v_isSharedCheck_2047_ = !lean_is_exclusive(v_x_2018_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2025_ = v_x_2018_;
v_isShared_2026_ = v_isSharedCheck_2047_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_vs_2023_);
lean_inc(v_ks_2022_);
lean_dec(v_x_2018_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2047_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2027_; uint8_t v___x_2028_; 
v___x_2027_ = lean_array_get_size(v_ks_2022_);
v___x_2028_ = lean_nat_dec_lt(v_x_2019_, v___x_2027_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2032_; 
lean_dec(v_x_2019_);
v___x_2029_ = lean_array_push(v_ks_2022_, v_x_2020_);
v___x_2030_ = lean_array_push(v_vs_2023_, v_x_2021_);
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 1, v___x_2030_);
lean_ctor_set(v___x_2025_, 0, v___x_2029_);
v___x_2032_ = v___x_2025_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_2029_);
lean_ctor_set(v_reuseFailAlloc_2033_, 1, v___x_2030_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
else
{
lean_object* v_k_x27_2034_; uint8_t v___x_2035_; 
v_k_x27_2034_ = lean_array_fget_borrowed(v_ks_2022_, v_x_2019_);
v___x_2035_ = l_Lean_instBEqMVarId_beq(v_x_2020_, v_k_x27_2034_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2037_; 
if (v_isShared_2026_ == 0)
{
v___x_2037_ = v___x_2025_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_ks_2022_);
lean_ctor_set(v_reuseFailAlloc_2041_, 1, v_vs_2023_);
v___x_2037_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2038_ = lean_unsigned_to_nat(1u);
v___x_2039_ = lean_nat_add(v_x_2019_, v___x_2038_);
lean_dec(v_x_2019_);
v_x_2018_ = v___x_2037_;
v_x_2019_ = v___x_2039_;
goto _start;
}
}
else
{
lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2045_; 
v___x_2042_ = lean_array_fset(v_ks_2022_, v_x_2019_, v_x_2020_);
v___x_2043_ = lean_array_fset(v_vs_2023_, v_x_2019_, v_x_2021_);
lean_dec(v_x_2019_);
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 1, v___x_2043_);
lean_ctor_set(v___x_2025_, 0, v___x_2042_);
v___x_2045_ = v___x_2025_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___x_2042_);
lean_ctor_set(v_reuseFailAlloc_2046_, 1, v___x_2043_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__19___redArg(lean_object* v_n_2048_, lean_object* v_k_2049_, lean_object* v_v_2050_){
_start:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2051_ = lean_unsigned_to_nat(0u);
v___x_2052_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__19_spec__21___redArg(v_n_2048_, v___x_2051_, v_k_2049_, v_v_2050_);
return v___x_2052_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_2053_; 
v___x_2053_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___redArg(lean_object* v_x_2054_, size_t v_x_2055_, size_t v_x_2056_, lean_object* v_x_2057_, lean_object* v_x_2058_){
_start:
{
if (lean_obj_tag(v_x_2054_) == 0)
{
lean_object* v_es_2059_; size_t v___x_2060_; size_t v___x_2061_; lean_object* v_j_2062_; lean_object* v___x_2063_; uint8_t v___x_2064_; 
v_es_2059_ = lean_ctor_get(v_x_2054_, 0);
v___x_2060_ = ((size_t)31ULL);
v___x_2061_ = lean_usize_land(v_x_2055_, v___x_2060_);
v_j_2062_ = lean_usize_to_nat(v___x_2061_);
v___x_2063_ = lean_array_get_size(v_es_2059_);
v___x_2064_ = lean_nat_dec_lt(v_j_2062_, v___x_2063_);
if (v___x_2064_ == 0)
{
lean_dec(v_j_2062_);
lean_dec(v_x_2058_);
lean_dec(v_x_2057_);
return v_x_2054_;
}
else
{
lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2103_; 
lean_inc_ref(v_es_2059_);
v_isSharedCheck_2103_ = !lean_is_exclusive(v_x_2054_);
if (v_isSharedCheck_2103_ == 0)
{
lean_object* v_unused_2104_; 
v_unused_2104_ = lean_ctor_get(v_x_2054_, 0);
lean_dec(v_unused_2104_);
v___x_2066_ = v_x_2054_;
v_isShared_2067_ = v_isSharedCheck_2103_;
goto v_resetjp_2065_;
}
else
{
lean_dec(v_x_2054_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2103_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v_v_2068_; lean_object* v___x_2069_; lean_object* v_xs_x27_2070_; lean_object* v___y_2072_; 
v_v_2068_ = lean_array_fget(v_es_2059_, v_j_2062_);
v___x_2069_ = lean_box(0);
v_xs_x27_2070_ = lean_array_fset(v_es_2059_, v_j_2062_, v___x_2069_);
switch(lean_obj_tag(v_v_2068_))
{
case 0:
{
lean_object* v_key_2077_; lean_object* v_val_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2088_; 
v_key_2077_ = lean_ctor_get(v_v_2068_, 0);
v_val_2078_ = lean_ctor_get(v_v_2068_, 1);
v_isSharedCheck_2088_ = !lean_is_exclusive(v_v_2068_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2080_ = v_v_2068_;
v_isShared_2081_ = v_isSharedCheck_2088_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_val_2078_);
lean_inc(v_key_2077_);
lean_dec(v_v_2068_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2088_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
uint8_t v___x_2082_; 
v___x_2082_ = l_Lean_instBEqMVarId_beq(v_x_2057_, v_key_2077_);
if (v___x_2082_ == 0)
{
lean_object* v___x_2083_; lean_object* v___x_2084_; 
lean_del_object(v___x_2080_);
v___x_2083_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2077_, v_val_2078_, v_x_2057_, v_x_2058_);
v___x_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
v___y_2072_ = v___x_2084_;
goto v___jp_2071_;
}
else
{
lean_object* v___x_2086_; 
lean_dec(v_val_2078_);
lean_dec(v_key_2077_);
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 1, v_x_2058_);
lean_ctor_set(v___x_2080_, 0, v_x_2057_);
v___x_2086_ = v___x_2080_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_x_2057_);
lean_ctor_set(v_reuseFailAlloc_2087_, 1, v_x_2058_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
v___y_2072_ = v___x_2086_;
goto v___jp_2071_;
}
}
}
}
case 1:
{
lean_object* v_node_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2101_; 
v_node_2089_ = lean_ctor_get(v_v_2068_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v_v_2068_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2091_ = v_v_2068_;
v_isShared_2092_ = v_isSharedCheck_2101_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_node_2089_);
lean_dec(v_v_2068_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2101_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
size_t v___x_2093_; size_t v___x_2094_; size_t v___x_2095_; size_t v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2099_; 
v___x_2093_ = ((size_t)5ULL);
v___x_2094_ = lean_usize_shift_right(v_x_2055_, v___x_2093_);
v___x_2095_ = ((size_t)1ULL);
v___x_2096_ = lean_usize_add(v_x_2056_, v___x_2095_);
v___x_2097_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___redArg(v_node_2089_, v___x_2094_, v___x_2096_, v_x_2057_, v_x_2058_);
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 0, v___x_2097_);
v___x_2099_ = v___x_2091_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v___x_2097_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
v___y_2072_ = v___x_2099_;
goto v___jp_2071_;
}
}
}
default: 
{
lean_object* v___x_2102_; 
v___x_2102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2102_, 0, v_x_2057_);
lean_ctor_set(v___x_2102_, 1, v_x_2058_);
v___y_2072_ = v___x_2102_;
goto v___jp_2071_;
}
}
v___jp_2071_:
{
lean_object* v___x_2073_; lean_object* v___x_2075_; 
v___x_2073_ = lean_array_fset(v_xs_x27_2070_, v_j_2062_, v___y_2072_);
lean_dec(v_j_2062_);
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 0, v___x_2073_);
v___x_2075_ = v___x_2066_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2073_);
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
else
{
lean_object* v_ks_2105_; lean_object* v_vs_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2124_; 
v_ks_2105_ = lean_ctor_get(v_x_2054_, 0);
v_vs_2106_ = lean_ctor_get(v_x_2054_, 1);
v_isSharedCheck_2124_ = !lean_is_exclusive(v_x_2054_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2108_ = v_x_2054_;
v_isShared_2109_ = v_isSharedCheck_2124_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_vs_2106_);
lean_inc(v_ks_2105_);
lean_dec(v_x_2054_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2124_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_ks_2105_);
lean_ctor_set(v_reuseFailAlloc_2123_, 1, v_vs_2106_);
v___x_2111_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
lean_object* v_newNode_2112_; size_t v___x_2113_; uint8_t v___x_2114_; 
v_newNode_2112_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__19___redArg(v___x_2111_, v_x_2057_, v_x_2058_);
v___x_2113_ = ((size_t)7ULL);
v___x_2114_ = lean_usize_dec_le(v___x_2113_, v_x_2056_);
if (v___x_2114_ == 0)
{
lean_object* v___x_2115_; lean_object* v___x_2116_; uint8_t v___x_2117_; 
v___x_2115_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2112_);
v___x_2116_ = lean_unsigned_to_nat(4u);
v___x_2117_ = lean_nat_dec_lt(v___x_2115_, v___x_2116_);
lean_dec(v___x_2115_);
if (v___x_2117_ == 0)
{
lean_object* v_ks_2118_; lean_object* v_vs_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v_ks_2118_ = lean_ctor_get(v_newNode_2112_, 0);
lean_inc_ref(v_ks_2118_);
v_vs_2119_ = lean_ctor_get(v_newNode_2112_, 1);
lean_inc_ref(v_vs_2119_);
lean_dec_ref(v_newNode_2112_);
v___x_2120_ = lean_unsigned_to_nat(0u);
v___x_2121_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___redArg___closed__0);
v___x_2122_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__20___redArg(v_x_2056_, v_ks_2118_, v_vs_2119_, v___x_2120_, v___x_2121_);
lean_dec_ref(v_vs_2119_);
lean_dec_ref(v_ks_2118_);
return v___x_2122_;
}
else
{
return v_newNode_2112_;
}
}
else
{
return v_newNode_2112_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__20___redArg(size_t v_depth_2125_, lean_object* v_keys_2126_, lean_object* v_vals_2127_, lean_object* v_i_2128_, lean_object* v_entries_2129_){
_start:
{
lean_object* v___x_2130_; uint8_t v___x_2131_; 
v___x_2130_ = lean_array_get_size(v_keys_2126_);
v___x_2131_ = lean_nat_dec_lt(v_i_2128_, v___x_2130_);
if (v___x_2131_ == 0)
{
lean_dec(v_i_2128_);
return v_entries_2129_;
}
else
{
lean_object* v_k_2132_; lean_object* v_v_2133_; uint64_t v___x_2134_; size_t v_h_2135_; size_t v___x_2136_; lean_object* v___x_2137_; size_t v___x_2138_; size_t v___x_2139_; size_t v___x_2140_; size_t v_h_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
v_k_2132_ = lean_array_fget_borrowed(v_keys_2126_, v_i_2128_);
v_v_2133_ = lean_array_fget_borrowed(v_vals_2127_, v_i_2128_);
v___x_2134_ = l_Lean_instHashableMVarId_hash(v_k_2132_);
v_h_2135_ = lean_uint64_to_usize(v___x_2134_);
v___x_2136_ = ((size_t)5ULL);
v___x_2137_ = lean_unsigned_to_nat(1u);
v___x_2138_ = ((size_t)1ULL);
v___x_2139_ = lean_usize_sub(v_depth_2125_, v___x_2138_);
v___x_2140_ = lean_usize_mul(v___x_2136_, v___x_2139_);
v_h_2141_ = lean_usize_shift_right(v_h_2135_, v___x_2140_);
v___x_2142_ = lean_nat_add(v_i_2128_, v___x_2137_);
lean_dec(v_i_2128_);
lean_inc(v_v_2133_);
lean_inc(v_k_2132_);
v___x_2143_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___redArg(v_entries_2129_, v_h_2141_, v_depth_2125_, v_k_2132_, v_v_2133_);
v_i_2128_ = v___x_2142_;
v_entries_2129_ = v___x_2143_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__20___redArg___boxed(lean_object* v_depth_2145_, lean_object* v_keys_2146_, lean_object* v_vals_2147_, lean_object* v_i_2148_, lean_object* v_entries_2149_){
_start:
{
size_t v_depth_boxed_2150_; lean_object* v_res_2151_; 
v_depth_boxed_2150_ = lean_unbox_usize(v_depth_2145_);
lean_dec(v_depth_2145_);
v_res_2151_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__20___redArg(v_depth_boxed_2150_, v_keys_2146_, v_vals_2147_, v_i_2148_, v_entries_2149_);
lean_dec_ref(v_vals_2147_);
lean_dec_ref(v_keys_2146_);
return v_res_2151_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___redArg___boxed(lean_object* v_x_2152_, lean_object* v_x_2153_, lean_object* v_x_2154_, lean_object* v_x_2155_, lean_object* v_x_2156_){
_start:
{
size_t v_x_95167__boxed_2157_; size_t v_x_95168__boxed_2158_; lean_object* v_res_2159_; 
v_x_95167__boxed_2157_ = lean_unbox_usize(v_x_2153_);
lean_dec(v_x_2153_);
v_x_95168__boxed_2158_ = lean_unbox_usize(v_x_2154_);
lean_dec(v_x_2154_);
v_res_2159_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___redArg(v_x_2152_, v_x_95167__boxed_2157_, v_x_95168__boxed_2158_, v_x_2155_, v_x_2156_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(lean_object* v_x_2160_, lean_object* v_x_2161_, lean_object* v_x_2162_){
_start:
{
uint64_t v___x_2163_; size_t v___x_2164_; size_t v___x_2165_; lean_object* v___x_2166_; 
v___x_2163_ = l_Lean_instHashableMVarId_hash(v_x_2161_);
v___x_2164_ = lean_uint64_to_usize(v___x_2163_);
v___x_2165_ = ((size_t)1ULL);
v___x_2166_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___redArg(v_x_2160_, v___x_2164_, v___x_2165_, v_x_2161_, v_x_2162_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(lean_object* v_mvarId_2167_, lean_object* v_val_2168_, lean_object* v___y_2169_){
_start:
{
lean_object* v___x_2171_; lean_object* v_mctx_2172_; lean_object* v_cache_2173_; lean_object* v_zetaDeltaFVarIds_2174_; lean_object* v_postponed_2175_; lean_object* v_diag_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2205_; 
v___x_2171_ = lean_st_ref_take(v___y_2169_);
v_mctx_2172_ = lean_ctor_get(v___x_2171_, 0);
v_cache_2173_ = lean_ctor_get(v___x_2171_, 1);
v_zetaDeltaFVarIds_2174_ = lean_ctor_get(v___x_2171_, 2);
v_postponed_2175_ = lean_ctor_get(v___x_2171_, 3);
v_diag_2176_ = lean_ctor_get(v___x_2171_, 4);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2178_ = v___x_2171_;
v_isShared_2179_ = v_isSharedCheck_2205_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_diag_2176_);
lean_inc(v_postponed_2175_);
lean_inc(v_zetaDeltaFVarIds_2174_);
lean_inc(v_cache_2173_);
lean_inc(v_mctx_2172_);
lean_dec(v___x_2171_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2205_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v_depth_2180_; lean_object* v_levelAssignDepth_2181_; lean_object* v_lmvarCounter_2182_; lean_object* v_mvarCounter_2183_; lean_object* v_lDecls_2184_; lean_object* v_decls_2185_; lean_object* v_userNames_2186_; lean_object* v_lAssignment_2187_; lean_object* v_eAssignment_2188_; lean_object* v_dAssignment_2189_; lean_object* v_instanceTypedMVars_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2204_; 
v_depth_2180_ = lean_ctor_get(v_mctx_2172_, 0);
v_levelAssignDepth_2181_ = lean_ctor_get(v_mctx_2172_, 1);
v_lmvarCounter_2182_ = lean_ctor_get(v_mctx_2172_, 2);
v_mvarCounter_2183_ = lean_ctor_get(v_mctx_2172_, 3);
v_lDecls_2184_ = lean_ctor_get(v_mctx_2172_, 4);
v_decls_2185_ = lean_ctor_get(v_mctx_2172_, 5);
v_userNames_2186_ = lean_ctor_get(v_mctx_2172_, 6);
v_lAssignment_2187_ = lean_ctor_get(v_mctx_2172_, 7);
v_eAssignment_2188_ = lean_ctor_get(v_mctx_2172_, 8);
v_dAssignment_2189_ = lean_ctor_get(v_mctx_2172_, 9);
v_instanceTypedMVars_2190_ = lean_ctor_get(v_mctx_2172_, 10);
v_isSharedCheck_2204_ = !lean_is_exclusive(v_mctx_2172_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2192_ = v_mctx_2172_;
v_isShared_2193_ = v_isSharedCheck_2204_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_instanceTypedMVars_2190_);
lean_inc(v_dAssignment_2189_);
lean_inc(v_eAssignment_2188_);
lean_inc(v_lAssignment_2187_);
lean_inc(v_userNames_2186_);
lean_inc(v_decls_2185_);
lean_inc(v_lDecls_2184_);
lean_inc(v_mvarCounter_2183_);
lean_inc(v_lmvarCounter_2182_);
lean_inc(v_levelAssignDepth_2181_);
lean_inc(v_depth_2180_);
lean_dec(v_mctx_2172_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2204_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2194_; lean_object* v___x_2196_; 
v___x_2194_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(v_eAssignment_2188_, v_mvarId_2167_, v_val_2168_);
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 8, v___x_2194_);
v___x_2196_ = v___x_2192_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_depth_2180_);
lean_ctor_set(v_reuseFailAlloc_2203_, 1, v_levelAssignDepth_2181_);
lean_ctor_set(v_reuseFailAlloc_2203_, 2, v_lmvarCounter_2182_);
lean_ctor_set(v_reuseFailAlloc_2203_, 3, v_mvarCounter_2183_);
lean_ctor_set(v_reuseFailAlloc_2203_, 4, v_lDecls_2184_);
lean_ctor_set(v_reuseFailAlloc_2203_, 5, v_decls_2185_);
lean_ctor_set(v_reuseFailAlloc_2203_, 6, v_userNames_2186_);
lean_ctor_set(v_reuseFailAlloc_2203_, 7, v_lAssignment_2187_);
lean_ctor_set(v_reuseFailAlloc_2203_, 8, v___x_2194_);
lean_ctor_set(v_reuseFailAlloc_2203_, 9, v_dAssignment_2189_);
lean_ctor_set(v_reuseFailAlloc_2203_, 10, v_instanceTypedMVars_2190_);
v___x_2196_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
lean_object* v___x_2198_; 
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 0, v___x_2196_);
v___x_2198_ = v___x_2178_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v___x_2196_);
lean_ctor_set(v_reuseFailAlloc_2202_, 1, v_cache_2173_);
lean_ctor_set(v_reuseFailAlloc_2202_, 2, v_zetaDeltaFVarIds_2174_);
lean_ctor_set(v_reuseFailAlloc_2202_, 3, v_postponed_2175_);
lean_ctor_set(v_reuseFailAlloc_2202_, 4, v_diag_2176_);
v___x_2198_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2199_ = lean_st_ref_put(v___y_2169_, v___x_2198_);
v___x_2200_ = lean_box(0);
v___x_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2200_);
return v___x_2201_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg___boxed(lean_object* v_mvarId_2206_, lean_object* v_val_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(v_mvarId_2206_, v_val_2207_, v___y_2208_);
lean_dec(v___y_2208_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(lean_object* v_o_2211_, lean_object* v___y_2212_){
_start:
{
lean_object* v___x_2214_; lean_object* v_env_2215_; lean_object* v___x_2216_; lean_object* v_toEnvExtension_2217_; lean_object* v_asyncMode_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v_merged_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2230_; 
v___x_2214_ = lean_st_ref_get(v___y_2212_);
v_env_2215_ = lean_ctor_get(v___x_2214_, 0);
lean_inc_ref(v_env_2215_);
lean_dec(v___x_2214_);
v___x_2216_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_2217_ = lean_ctor_get(v___x_2216_, 0);
v_asyncMode_2218_ = lean_ctor_get(v_toEnvExtension_2217_, 2);
v___x_2219_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_2220_ = lean_box(0);
v___x_2221_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2219_, v___x_2216_, v_env_2215_, v_asyncMode_2218_, v___x_2220_);
v_merged_2222_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2230_ == 0)
{
lean_object* v_unused_2231_; 
v_unused_2231_ = lean_ctor_get(v___x_2221_, 1);
lean_dec(v_unused_2231_);
v___x_2224_ = v___x_2221_;
v_isShared_2225_ = v_isSharedCheck_2230_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_merged_2222_);
lean_dec(v___x_2221_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2230_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2227_; 
if (v_isShared_2225_ == 0)
{
lean_ctor_set(v___x_2224_, 1, v_merged_2222_);
lean_ctor_set(v___x_2224_, 0, v_o_2211_);
v___x_2227_ = v___x_2224_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_o_2211_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v_merged_2222_);
v___x_2227_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
lean_object* v___x_2228_; 
v___x_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
return v___x_2228_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg___boxed(lean_object* v_o_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v_res_2235_; 
v_res_2235_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(v_o_2232_, v___y_2233_);
lean_dec(v___y_2233_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_){
_start:
{
lean_object* v_toCold_2245_; lean_object* v_options_2246_; lean_object* v___x_2247_; 
v_toCold_2245_ = lean_ctor_get(v___y_2242_, 0);
v_options_2246_ = lean_ctor_get(v_toCold_2245_, 2);
lean_inc_ref(v_options_2246_);
v___x_2247_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(v_options_2246_, v___y_2243_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___boxed(lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
lean_object* v_res_2257_; 
v_res_2257_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
return v_res_2257_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__6(void){
_start:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2265_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5));
v___x_2266_ = l_Lean_stringToMessageData(v___x_2265_);
return v___x_2266_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__8(void){
_start:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2268_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__7));
v___x_2269_ = l_Lean_stringToMessageData(v___x_2268_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5(lean_object* v_usingArg_2273_, lean_object* v_snd_2274_, uint8_t v___x_2275_, uint8_t v___x_2276_, lean_object* v___x_2277_, uint8_t v_useReducible_2278_, uint8_t v___x_2279_, lean_object* v___x_2280_, lean_object* v___x_2281_, lean_object* v_simprocs_2282_, lean_object* v_discharge_x3f_2283_, lean_object* v_snd_2284_, lean_object* v___f_2285_, lean_object* v___x_2286_, lean_object* v___x_2287_, lean_object* v___x_2288_, lean_object* v___x_2289_, lean_object* v___f_2290_, lean_object* v_a_2291_, lean_object* v___x_2292_, lean_object* v___f_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
lean_object* v___y_2304_; lean_object* v___y_2305_; lean_object* v___y_2306_; lean_object* v___y_2317_; lean_object* v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___y_2322_; lean_object* v___y_2323_; lean_object* v___y_2324_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2327_; lean_object* v___y_2328_; lean_object* v___y_2329_; lean_object* v___y_2330_; lean_object* v___y_2331_; lean_object* v___y_2332_; lean_object* v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v___y_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; 
if (lean_obj_tag(v_usingArg_2273_) == 1)
{
lean_object* v_val_2517_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2521_; lean_object* v___y_2522_; lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___x_2569_; lean_object* v_infoState_2570_; uint8_t v_enabled_2571_; 
v_val_2517_ = lean_ctor_get(v_usingArg_2273_, 0);
lean_inc(v_val_2517_);
lean_dec_ref_known(v_usingArg_2273_, 1);
v___x_2569_ = lean_st_ref_get(v___y_2301_);
v_infoState_2570_ = lean_ctor_get(v___x_2569_, 7);
lean_inc_ref(v_infoState_2570_);
lean_dec(v___x_2569_);
v_enabled_2571_ = lean_ctor_get_uint8(v_infoState_2570_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2570_);
if (v_enabled_2571_ == 0)
{
lean_dec_ref(v___f_2293_);
v___y_2519_ = v___y_2294_;
v___y_2520_ = v___y_2295_;
v___y_2521_ = v___y_2296_;
v___y_2522_ = v___y_2297_;
v___y_2523_ = v___y_2298_;
v___y_2524_ = v___y_2299_;
v___y_2525_ = v___y_2300_;
v___y_2526_ = v___y_2301_;
goto v___jp_2518_;
}
else
{
lean_object* v___x_2572_; lean_object* v_a_2573_; lean_object* v___f_2574_; lean_object* v___x_2575_; 
v___x_2572_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___y_2301_);
v_a_2573_ = lean_ctor_get(v___x_2572_, 0);
lean_inc(v_a_2573_);
lean_dec_ref(v___x_2572_);
v___f_2574_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___boxed), 10, 1);
lean_closure_set(v___f_2574_, 0, v_a_2573_);
v___x_2575_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v___f_2574_, v___f_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_dec_ref_known(v___x_2575_, 1);
v___y_2519_ = v___y_2294_;
v___y_2520_ = v___y_2295_;
v___y_2521_ = v___y_2296_;
v___y_2522_ = v___y_2297_;
v___y_2523_ = v___y_2298_;
v___y_2524_ = v___y_2299_;
v___y_2525_ = v___y_2300_;
v___y_2526_ = v___y_2301_;
goto v___jp_2518_;
}
else
{
lean_object* v_a_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2583_; 
lean_dec(v_val_2517_);
lean_dec_ref(v_a_2291_);
lean_dec_ref(v___f_2290_);
lean_dec_ref(v___x_2289_);
lean_dec_ref(v___x_2288_);
lean_dec_ref(v___x_2287_);
lean_dec(v___x_2286_);
lean_dec_ref(v___f_2285_);
lean_dec_ref(v_snd_2284_);
lean_dec(v_discharge_x3f_2283_);
lean_dec_ref(v_simprocs_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2277_);
lean_dec(v_snd_2274_);
v_a_2576_ = lean_ctor_get(v___x_2575_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2578_ = v___x_2575_;
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_a_2576_);
lean_dec(v___x_2575_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2581_; 
if (v_isShared_2579_ == 0)
{
v___x_2581_ = v___x_2578_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_a_2576_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
v___jp_2518_:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2527_ = lean_st_ref_get(v___y_2524_);
v___x_2528_ = lean_box(0);
v___x_2529_ = l_Lean_Elab_Tactic_elabTerm(v_val_2517_, v___x_2528_, v___x_2275_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_a_2530_; lean_object* v___x_2531_; 
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
lean_inc_n(v_a_2530_, 2);
lean_dec_ref_known(v___x_2529_, 1);
v___x_2531_ = l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(v_snd_2274_, v_a_2530_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v_mctx_2532_; lean_object* v_a_2533_; uint8_t v___x_2534_; 
v_mctx_2532_ = lean_ctor_get(v___x_2527_, 0);
lean_inc_ref(v_mctx_2532_);
lean_dec(v___x_2527_);
v_a_2533_ = lean_ctor_get(v___x_2531_, 0);
lean_inc(v_a_2533_);
lean_dec_ref_known(v___x_2531_, 1);
v___x_2534_ = lean_unbox(v_a_2533_);
lean_dec(v_a_2533_);
if (v___x_2534_ == 0)
{
lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2551_; 
lean_dec_ref(v_mctx_2532_);
lean_dec_ref(v_a_2291_);
lean_dec_ref(v___f_2290_);
lean_dec_ref(v___x_2289_);
lean_dec_ref(v___x_2288_);
lean_dec_ref(v___x_2287_);
lean_dec(v___x_2286_);
lean_dec_ref(v___f_2285_);
lean_dec_ref(v_snd_2284_);
lean_dec(v_discharge_x3f_2283_);
lean_dec_ref(v_simprocs_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2277_);
v___x_2535_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__6);
v___x_2536_ = l_Lean_indentExpr(v_a_2530_);
v___x_2537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2535_);
lean_ctor_set(v___x_2537_, 1, v___x_2536_);
v___x_2538_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__8, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__8_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__8);
v___x_2539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2537_);
lean_ctor_set(v___x_2539_, 1, v___x_2538_);
v___x_2540_ = l_Lean_Expr_mvar___override(v_snd_2274_);
v___x_2541_ = l_Lean_MessageData_ofExpr(v___x_2540_);
v___x_2542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2539_);
lean_ctor_set(v___x_2542_, 1, v___x_2541_);
v___x_2543_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v___x_2542_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_);
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2546_ = v___x_2543_;
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2543_);
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
else
{
lean_object* v_mvarCounter_2552_; 
v_mvarCounter_2552_ = lean_ctor_get(v_mctx_2532_, 3);
lean_inc(v_mvarCounter_2552_);
lean_dec_ref(v_mctx_2532_);
lean_inc(v_a_2530_);
v___y_2368_ = v___x_2528_;
v___y_2369_ = v_mvarCounter_2552_;
v___y_2370_ = v_a_2530_;
v___y_2371_ = v_a_2530_;
v___y_2372_ = v___x_2528_;
v___y_2373_ = v___y_2519_;
v___y_2374_ = v___y_2520_;
v___y_2375_ = v___y_2521_;
v___y_2376_ = v___y_2522_;
v___y_2377_ = v___y_2523_;
v___y_2378_ = v___y_2524_;
v___y_2379_ = v___y_2525_;
v___y_2380_ = v___y_2526_;
goto v___jp_2367_;
}
}
else
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2560_; 
lean_dec(v_a_2530_);
lean_dec(v___x_2527_);
lean_dec_ref(v_a_2291_);
lean_dec_ref(v___f_2290_);
lean_dec_ref(v___x_2289_);
lean_dec_ref(v___x_2288_);
lean_dec_ref(v___x_2287_);
lean_dec(v___x_2286_);
lean_dec_ref(v___f_2285_);
lean_dec_ref(v_snd_2284_);
lean_dec(v_discharge_x3f_2283_);
lean_dec_ref(v_simprocs_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2277_);
lean_dec(v_snd_2274_);
v_a_2553_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2555_ = v___x_2531_;
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2531_);
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
else
{
lean_object* v_a_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2568_; 
lean_dec(v___x_2527_);
lean_dec_ref(v_a_2291_);
lean_dec_ref(v___f_2290_);
lean_dec_ref(v___x_2289_);
lean_dec_ref(v___x_2288_);
lean_dec_ref(v___x_2287_);
lean_dec(v___x_2286_);
lean_dec_ref(v___f_2285_);
lean_dec_ref(v_snd_2284_);
lean_dec(v_discharge_x3f_2283_);
lean_dec_ref(v_simprocs_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2277_);
lean_dec(v_snd_2274_);
v_a_2561_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2563_ = v___x_2529_;
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_a_2561_);
lean_dec(v___x_2529_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2566_; 
if (v_isShared_2564_ == 0)
{
v___x_2566_ = v___x_2563_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2561_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
}
}
else
{
lean_object* v_lctx_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
lean_dec_ref(v___f_2293_);
lean_dec_ref(v_a_2291_);
lean_dec_ref(v___f_2290_);
lean_dec_ref(v___x_2289_);
lean_dec_ref(v___x_2288_);
lean_dec_ref(v___x_2287_);
lean_dec(v___x_2286_);
lean_dec_ref(v___f_2285_);
lean_dec_ref(v___x_2277_);
lean_dec(v_usingArg_2273_);
v_lctx_2584_ = lean_ctor_get(v___y_2298_, 2);
v___x_2585_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__10));
v___x_2586_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2584_, v___x_2585_);
if (lean_obj_tag(v___x_2586_) == 1)
{
lean_object* v_val_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v_val_2587_ = lean_ctor_get(v___x_2586_, 0);
lean_inc(v_val_2587_);
lean_dec_ref_known(v___x_2586_, 1);
v___x_2588_ = l_Lean_LocalDecl_fvarId(v_val_2587_);
lean_dec(v_val_2587_);
v___x_2589_ = lean_mk_empty_array_with_capacity(v___x_2280_);
v___x_2590_ = lean_array_push(v___x_2589_, v___x_2588_);
lean_inc_ref(v_snd_2284_);
v___x_2591_ = l_Lean_Meta_simpGoal(v_snd_2274_, v___x_2281_, v_simprocs_2282_, v_discharge_x3f_2283_, v___x_2276_, v___x_2590_, v_snd_2284_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2620_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2594_ = v___x_2591_;
v_isShared_2595_ = v_isSharedCheck_2620_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2591_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2620_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v_fst_2596_; 
v_fst_2596_ = lean_ctor_get(v_a_2592_, 0);
if (lean_obj_tag(v_fst_2596_) == 1)
{
lean_object* v_val_2597_; lean_object* v_snd_2598_; lean_object* v_snd_2599_; lean_object* v___x_2600_; 
lean_del_object(v___x_2594_);
lean_dec_ref(v_snd_2284_);
v_val_2597_ = lean_ctor_get(v_fst_2596_, 0);
lean_inc(v_val_2597_);
v_snd_2598_ = lean_ctor_get(v_a_2592_, 1);
lean_inc(v_snd_2598_);
lean_dec(v_a_2592_);
v_snd_2599_ = lean_ctor_get(v_val_2597_, 1);
lean_inc(v_snd_2599_);
lean_dec(v_val_2597_);
v___x_2600_ = l_Lean_MVarId_assumption(v_snd_2599_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2607_; 
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2607_ == 0)
{
lean_object* v_unused_2608_; 
v_unused_2608_ = lean_ctor_get(v___x_2600_, 0);
lean_dec(v_unused_2608_);
v___x_2602_ = v___x_2600_;
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
else
{
lean_dec(v___x_2600_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2605_; 
if (v_isShared_2603_ == 0)
{
lean_ctor_set(v___x_2602_, 0, v_snd_2598_);
v___x_2605_ = v___x_2602_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_snd_2598_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
else
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
lean_dec(v_snd_2598_);
v_a_2609_ = lean_ctor_get(v___x_2600_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2611_ = v___x_2600_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2600_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2614_; 
if (v_isShared_2612_ == 0)
{
v___x_2614_ = v___x_2611_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_a_2609_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
else
{
lean_object* v___x_2618_; 
lean_dec(v_a_2592_);
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 0, v_snd_2284_);
v___x_2618_ = v___x_2594_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_snd_2284_);
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
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
lean_dec_ref(v_snd_2284_);
v_a_2621_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2623_ = v___x_2591_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2591_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2626_; 
if (v_isShared_2624_ == 0)
{
v___x_2626_ = v___x_2623_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_a_2621_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
else
{
lean_object* v___x_2629_; 
lean_dec(v___x_2586_);
lean_dec(v_discharge_x3f_2283_);
lean_dec_ref(v_simprocs_2282_);
lean_dec_ref(v___x_2281_);
v___x_2629_ = l_Lean_MVarId_assumption(v_snd_2274_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2636_; 
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2636_ == 0)
{
lean_object* v_unused_2637_; 
v_unused_2637_ = lean_ctor_get(v___x_2629_, 0);
lean_dec(v_unused_2637_);
v___x_2631_ = v___x_2629_;
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
else
{
lean_dec(v___x_2629_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2634_; 
if (v_isShared_2632_ == 0)
{
lean_ctor_set(v___x_2631_, 0, v_snd_2284_);
v___x_2634_ = v___x_2631_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_snd_2284_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
else
{
lean_object* v_a_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2645_; 
lean_dec_ref(v_snd_2284_);
v_a_2638_ = lean_ctor_get(v___x_2629_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2640_ = v___x_2629_;
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_a_2638_);
lean_dec(v___x_2629_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2643_; 
if (v_isShared_2641_ == 0)
{
v___x_2643_ = v___x_2640_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_a_2638_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
}
}
v___jp_2303_:
{
lean_object* v___x_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
v___x_2307_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(v_snd_2274_, v___y_2305_, v___y_2306_);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2314_ == 0)
{
lean_object* v_unused_2315_; 
v_unused_2315_ = lean_ctor_get(v___x_2307_, 0);
lean_dec(v_unused_2315_);
v___x_2309_ = v___x_2307_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_dec(v___x_2307_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2312_; 
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 0, v___y_2304_);
v___x_2312_ = v___x_2309_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v___y_2304_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
v___jp_2316_:
{
lean_object* v___x_2333_; 
v___x_2333_ = l_Lean_Core_mkFreshUserName(v___y_2321_, v___y_2328_, v___y_2322_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v_a_2334_; lean_object* v___x_2335_; 
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
lean_inc_n(v_a_2334_, 2);
lean_dec_ref_known(v___x_2333_, 1);
v___x_2335_ = l_Lean_MVarId_rename(v___y_2327_, v___y_2332_, v_a_2334_, v___y_2324_, v___y_2320_, v___y_2328_, v___y_2322_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_a_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___f_2341_; lean_object* v___x_2342_; 
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
lean_inc_n(v_a_2336_, 2);
lean_dec_ref_known(v___x_2335_, 1);
v___x_2337_ = lean_box(v___x_2275_);
v___x_2338_ = lean_box(v___x_2276_);
v___x_2339_ = lean_box(v_useReducible_2278_);
v___x_2340_ = lean_box(v___x_2279_);
v___f_2341_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___boxed), 19, 10);
lean_closure_set(v___f_2341_, 0, v_a_2336_);
lean_closure_set(v___f_2341_, 1, v_a_2334_);
lean_closure_set(v___f_2341_, 2, v___x_2337_);
lean_closure_set(v___f_2341_, 3, v___x_2338_);
lean_closure_set(v___f_2341_, 4, v___y_2319_);
lean_closure_set(v___f_2341_, 5, v___y_2318_);
lean_closure_set(v___f_2341_, 6, v___x_2277_);
lean_closure_set(v___f_2341_, 7, v___y_2317_);
lean_closure_set(v___f_2341_, 8, v___x_2339_);
lean_closure_set(v___f_2341_, 9, v___x_2340_);
v___x_2342_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___redArg(v_a_2336_, v___f_2341_, v___y_2326_, v___y_2323_, v___y_2329_, v___y_2325_, v___y_2324_, v___y_2320_, v___y_2328_, v___y_2322_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_dec_ref_known(v___x_2342_, 1);
v___y_2304_ = v___y_2330_;
v___y_2305_ = v___y_2331_;
v___y_2306_ = v___y_2320_;
goto v___jp_2303_;
}
else
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2350_; 
lean_dec_ref(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v_snd_2274_);
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2345_ = v___x_2342_;
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2342_);
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
lean_dec(v_a_2334_);
lean_dec_ref(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec_ref(v___y_2319_);
lean_dec(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec_ref(v___x_2277_);
lean_dec(v_snd_2274_);
v_a_2351_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2353_ = v___x_2335_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2335_);
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
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2319_);
lean_dec(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec_ref(v___x_2277_);
lean_dec(v_snd_2274_);
v_a_2359_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2361_ = v___x_2333_;
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_a_2359_);
lean_dec(v___x_2333_);
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
v___jp_2367_:
{
lean_object* v___x_2381_; 
lean_inc(v_snd_2274_);
v___x_2381_ = l_Lean_MVarId_getType(v_snd_2274_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
if (lean_obj_tag(v___x_2381_) == 0)
{
lean_object* v_a_2382_; lean_object* v___x_2383_; 
v_a_2382_ = lean_ctor_get(v___x_2381_, 0);
lean_inc(v_a_2382_);
lean_dec_ref_known(v___x_2381_, 1);
lean_inc(v_snd_2274_);
v___x_2383_ = l_Lean_MVarId_getTag(v_snd_2274_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_object* v_a_2384_; lean_object* v___x_2385_; 
v_a_2384_ = lean_ctor_get(v___x_2383_, 0);
lean_inc(v_a_2384_);
lean_dec_ref_known(v___x_2383_, 1);
v___x_2385_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2382_, v_a_2384_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_object* v_a_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v_a_2386_ = lean_ctor_get(v___x_2385_, 0);
lean_inc(v_a_2386_);
lean_dec_ref_known(v___x_2385_, 1);
v___x_2387_ = l_Lean_Expr_mvarId_x21(v_a_2386_);
v___x_2388_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1));
lean_inc_ref(v___y_2371_);
v___x_2389_ = l_Lean_MVarId_note(v___x_2387_, v___x_2388_, v___y_2371_, v___y_2372_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
if (lean_obj_tag(v___x_2389_) == 0)
{
lean_object* v_a_2390_; lean_object* v_fst_2391_; lean_object* v_snd_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v_a_2390_ = lean_ctor_get(v___x_2389_, 0);
lean_inc(v_a_2390_);
lean_dec_ref_known(v___x_2389_, 1);
v_fst_2391_ = lean_ctor_get(v_a_2390_, 0);
lean_inc_n(v_fst_2391_, 2);
v_snd_2392_ = lean_ctor_get(v_a_2390_, 1);
lean_inc(v_snd_2392_);
lean_dec(v_a_2390_);
v___x_2393_ = lean_mk_empty_array_with_capacity(v___x_2280_);
v___x_2394_ = lean_array_push(v___x_2393_, v_fst_2391_);
v___x_2395_ = l_Lean_Meta_simpGoal(v_snd_2392_, v___x_2281_, v_simprocs_2282_, v_discharge_x3f_2283_, v___x_2276_, v___x_2394_, v_snd_2284_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_object* v_a_2396_; lean_object* v_fst_2397_; 
v_a_2396_ = lean_ctor_get(v___x_2395_, 0);
lean_inc(v_a_2396_);
lean_dec_ref_known(v___x_2395_, 1);
v_fst_2397_ = lean_ctor_get(v_a_2396_, 0);
if (lean_obj_tag(v_fst_2397_) == 0)
{
lean_object* v_snd_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2468_; 
lean_dec(v_fst_2391_);
lean_dec_ref(v___y_2370_);
lean_dec(v___y_2369_);
lean_dec(v___y_2368_);
lean_dec_ref(v___x_2277_);
v_snd_2398_ = lean_ctor_get(v_a_2396_, 1);
v_isSharedCheck_2468_ = !lean_is_exclusive(v_a_2396_);
if (v_isSharedCheck_2468_ == 0)
{
lean_object* v_unused_2469_; 
v_unused_2469_ = lean_ctor_get(v_a_2396_, 0);
lean_dec(v_unused_2469_);
v___x_2400_ = v_a_2396_;
v_isShared_2401_ = v_isSharedCheck_2468_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_snd_2398_);
lean_dec(v_a_2396_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2468_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2402_; lean_object* v_a_2403_; uint8_t v___x_2404_; 
v___x_2402_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
lean_inc(v_a_2403_);
lean_dec_ref(v___x_2402_);
v___x_2404_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_a_2403_);
lean_dec(v_a_2403_);
if (v___x_2404_ == 0)
{
lean_del_object(v___x_2400_);
lean_dec_ref(v___y_2371_);
lean_dec_ref(v_a_2291_);
lean_dec_ref(v___f_2290_);
lean_dec_ref(v___x_2289_);
lean_dec_ref(v___x_2288_);
lean_dec_ref(v___x_2287_);
lean_dec(v___x_2286_);
lean_dec_ref(v___f_2285_);
v___y_2304_ = v_snd_2398_;
v___y_2305_ = v_a_2386_;
v___y_2306_ = v___y_2378_;
goto v___jp_2303_;
}
else
{
if (lean_obj_tag(v___y_2371_) == 1)
{
lean_object* v_fvarId_2405_; lean_object* v_lctx_2406_; lean_object* v___x_2407_; 
v_fvarId_2405_ = lean_ctor_get(v___y_2371_, 0);
lean_inc(v_fvarId_2405_);
lean_dec_ref_known(v___y_2371_, 1);
v_lctx_2406_ = lean_ctor_get(v___y_2377_, 2);
lean_inc_ref(v_lctx_2406_);
v___x_2407_ = l_Lean_LocalContext_getRoundtrippingUserName_x3f(v_lctx_2406_, v_fvarId_2405_);
if (lean_obj_tag(v___x_2407_) == 1)
{
lean_object* v_val_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2467_; 
v_val_2408_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2410_ = v___x_2407_;
v_isShared_2411_ = v_isSharedCheck_2467_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_val_2408_);
lean_dec(v___x_2407_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2467_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2412_; 
lean_inc_ref(v___f_2285_);
lean_inc(v___y_2380_);
lean_inc_ref(v___y_2379_);
lean_inc(v___y_2378_);
lean_inc_ref(v___y_2377_);
lean_inc(v___y_2376_);
lean_inc_ref(v___y_2375_);
lean_inc(v___y_2374_);
lean_inc_ref(v___y_2373_);
v___x_2412_ = lean_apply_9(v___f_2285_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, lean_box(0));
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v_a_2413_; lean_object* v___x_2414_; 
v_a_2413_ = lean_ctor_get(v___x_2412_, 0);
lean_inc(v_a_2413_);
lean_dec_ref_known(v___x_2412_, 1);
lean_inc(v___y_2380_);
lean_inc_ref(v___y_2379_);
lean_inc(v___y_2378_);
lean_inc_ref(v___y_2377_);
lean_inc(v___y_2376_);
lean_inc_ref(v___y_2375_);
lean_inc(v___y_2374_);
lean_inc_ref(v___y_2373_);
v___x_2414_ = lean_apply_9(v___f_2285_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, lean_box(0));
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v_a_2415_; lean_object* v_ref_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2423_; 
v_a_2415_ = lean_ctor_get(v___x_2414_, 0);
lean_inc_n(v_a_2415_, 2);
lean_dec_ref_known(v___x_2414_, 1);
v_ref_2416_ = lean_ctor_get(v___y_2379_, 2);
v___x_2417_ = l_Lean_mkIdent(v_val_2408_);
lean_inc(v_a_2413_);
v___x_2418_ = l_Lean_Syntax_node1(v_a_2413_, v___x_2286_, v___x_2417_);
v___x_2419_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2));
lean_inc_ref(v___x_2289_);
lean_inc_ref(v___x_2288_);
lean_inc_ref(v___x_2287_);
v___x_2420_ = l_Lean_Name_mkStr4(v___x_2287_, v___x_2288_, v___x_2289_, v___x_2419_);
v___x_2421_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__3));
if (v_isShared_2401_ == 0)
{
lean_ctor_set_tag(v___x_2400_, 2);
lean_ctor_set(v___x_2400_, 1, v___x_2421_);
lean_ctor_set(v___x_2400_, 0, v_a_2415_);
v___x_2423_ = v___x_2400_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_a_2415_);
lean_ctor_set(v_reuseFailAlloc_2450_, 1, v___x_2421_);
v___x_2423_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2429_; 
v___x_2424_ = l_Lean_Syntax_node1(v_a_2413_, v___x_2420_, v___x_2418_);
v___x_2425_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__4));
v___x_2426_ = l_Lean_Name_mkStr4(v___x_2287_, v___x_2288_, v___x_2289_, v___x_2425_);
v___x_2427_ = l_Lean_Syntax_node2(v_a_2415_, v___x_2426_, v___x_2423_, v___x_2424_);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 0, v___x_2427_);
v___x_2429_ = v___x_2410_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v___x_2427_);
v___x_2429_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
lean_object* v___x_2430_; 
lean_inc(v___y_2380_);
lean_inc_ref(v___y_2379_);
lean_inc(v___y_2378_);
lean_inc_ref(v___y_2377_);
lean_inc(v___y_2376_);
lean_inc_ref(v___y_2375_);
lean_inc(v___y_2374_);
lean_inc_ref(v___y_2373_);
v___x_2430_ = lean_apply_10(v___f_2290_, v___x_2429_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, lean_box(0));
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_object* v_a_2431_; lean_object* v___x_2432_; 
v_a_2431_ = lean_ctor_get(v___x_2430_, 0);
lean_inc(v_a_2431_);
lean_dec_ref_known(v___x_2430_, 1);
lean_inc(v_ref_2416_);
v___x_2432_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa(v_a_2291_, v_ref_2416_, v_a_2431_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_dec_ref_known(v___x_2432_, 1);
v___y_2304_ = v_snd_2398_;
v___y_2305_ = v_a_2386_;
v___y_2306_ = v___y_2378_;
goto v___jp_2303_;
}
else
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2440_; 
lean_dec(v_snd_2398_);
lean_dec(v_a_2386_);
lean_dec(v_snd_2274_);
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2435_ = v___x_2432_;
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2432_);
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
else
{
lean_object* v_a_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2448_; 
lean_dec(v_snd_2398_);
lean_dec(v_a_2386_);
lean_dec_ref(v_a_2291_);
lean_dec(v_snd_2274_);
v_a_2441_ = lean_ctor_get(v___x_2430_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2443_ = v___x_2430_;
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_a_2441_);
lean_dec(v___x_2430_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2446_; 
if (v_isShared_2444_ == 0)
{
v___x_2446_ = v___x_2443_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_a_2441_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
}
}
}
}
else
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2458_; 
lean_dec(v_a_2413_);
lean_del_object(v___x_2410_);
lean_dec(v_val_2408_);
lean_del_object(v___x_2400_);
lean_dec(v_snd_2398_);
lean_dec(v_a_2386_);
lean_dec_ref(v_a_2291_);
lean_dec_ref(v___f_2290_);
lean_dec_ref(v___x_2289_);
lean_dec_ref(v___x_2288_);
lean_dec_ref(v___x_2287_);
lean_dec(v___x_2286_);
lean_dec(v_snd_2274_);
v_a_2451_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2453_ = v___x_2414_;
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2414_);
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
else
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2466_; 
lean_del_object(v___x_2410_);
lean_dec(v_val_2408_);
lean_del_object(v___x_2400_);
lean_dec(v_snd_2398_);
lean_dec(v_a_2386_);
lean_dec_ref(v_a_2291_);
lean_dec_ref(v___f_2290_);
lean_dec_ref(v___x_2289_);
lean_dec_ref(v___x_2288_);
lean_dec_ref(v___x_2287_);
lean_dec(v___x_2286_);
lean_dec_ref(v___f_2285_);
lean_dec(v_snd_2274_);
v_a_2459_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2461_ = v___x_2412_;
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2412_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2464_; 
if (v_isShared_2462_ == 0)
{
v___x_2464_ = v___x_2461_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_a_2459_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
}
else
{
lean_dec(v___x_2407_);
lean_del_object(v___x_2400_);
lean_dec_ref(v_a_2291_);
lean_dec_ref(v___f_2290_);
lean_dec_ref(v___x_2289_);
lean_dec_ref(v___x_2288_);
lean_dec_ref(v___x_2287_);
lean_dec(v___x_2286_);
lean_dec_ref(v___f_2285_);
v___y_2304_ = v_snd_2398_;
v___y_2305_ = v_a_2386_;
v___y_2306_ = v___y_2378_;
goto v___jp_2303_;
}
}
else
{
lean_del_object(v___x_2400_);
lean_dec_ref(v___y_2371_);
lean_dec_ref(v_a_2291_);
lean_dec_ref(v___f_2290_);
lean_dec_ref(v___x_2289_);
lean_dec_ref(v___x_2288_);
lean_dec_ref(v___x_2287_);
lean_dec(v___x_2286_);
lean_dec_ref(v___f_2285_);
v___y_2304_ = v_snd_2398_;
v___y_2305_ = v_a_2386_;
v___y_2306_ = v___y_2378_;
goto v___jp_2303_;
}
}
}
}
else
{
lean_object* v_val_2470_; lean_object* v_snd_2471_; lean_object* v_fst_2472_; lean_object* v_snd_2473_; lean_object* v___x_2474_; uint8_t v___x_2475_; 
lean_dec_ref(v___y_2371_);
lean_dec_ref(v_a_2291_);
lean_dec_ref(v___f_2290_);
lean_dec_ref(v___x_2289_);
lean_dec_ref(v___x_2288_);
lean_dec_ref(v___x_2287_);
lean_dec(v___x_2286_);
lean_dec_ref(v___f_2285_);
v_val_2470_ = lean_ctor_get(v_fst_2397_, 0);
lean_inc(v_val_2470_);
v_snd_2471_ = lean_ctor_get(v_a_2396_, 1);
lean_inc(v_snd_2471_);
lean_dec(v_a_2396_);
v_fst_2472_ = lean_ctor_get(v_val_2470_, 0);
lean_inc(v_fst_2472_);
v_snd_2473_ = lean_ctor_get(v_val_2470_, 1);
lean_inc(v_snd_2473_);
lean_dec(v_val_2470_);
v___x_2474_ = lean_array_get_size(v_fst_2472_);
v___x_2475_ = lean_nat_dec_lt(v___x_2292_, v___x_2474_);
if (v___x_2475_ == 0)
{
lean_dec(v_fst_2472_);
v___y_2317_ = v___y_2368_;
v___y_2318_ = v___y_2369_;
v___y_2319_ = v___y_2370_;
v___y_2320_ = v___y_2378_;
v___y_2321_ = v___x_2388_;
v___y_2322_ = v___y_2380_;
v___y_2323_ = v___y_2374_;
v___y_2324_ = v___y_2377_;
v___y_2325_ = v___y_2376_;
v___y_2326_ = v___y_2373_;
v___y_2327_ = v_snd_2473_;
v___y_2328_ = v___y_2379_;
v___y_2329_ = v___y_2375_;
v___y_2330_ = v_snd_2471_;
v___y_2331_ = v_a_2386_;
v___y_2332_ = v_fst_2391_;
goto v___jp_2316_;
}
else
{
lean_object* v___x_2476_; 
lean_dec(v_fst_2391_);
v___x_2476_ = lean_array_fget(v_fst_2472_, v___x_2292_);
lean_dec(v_fst_2472_);
v___y_2317_ = v___y_2368_;
v___y_2318_ = v___y_2369_;
v___y_2319_ = v___y_2370_;
v___y_2320_ = v___y_2378_;
v___y_2321_ = v___x_2388_;
v___y_2322_ = v___y_2380_;
v___y_2323_ = v___y_2374_;
v___y_2324_ = v___y_2377_;
v___y_2325_ = v___y_2376_;
v___y_2326_ = v___y_2373_;
v___y_2327_ = v_snd_2473_;
v___y_2328_ = v___y_2379_;
v___y_2329_ = v___y_2375_;
v___y_2330_ = v_snd_2471_;
v___y_2331_ = v_a_2386_;
v___y_2332_ = v___x_2476_;
goto v___jp_2316_;
}
}
}
else
{
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2484_; 
lean_dec(v_fst_2391_);
lean_dec(v_a_2386_);
lean_dec_ref(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v___y_2369_);
lean_dec(v___y_2368_);
lean_dec_ref(v_a_2291_);
lean_dec_ref(v___f_2290_);
lean_dec_ref(v___x_2289_);
lean_dec_ref(v___x_2288_);
lean_dec_ref(v___x_2287_);
lean_dec(v___x_2286_);
lean_dec_ref(v___f_2285_);
lean_dec_ref(v___x_2277_);
lean_dec(v_snd_2274_);
v_a_2477_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2479_ = v___x_2395_;
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v___x_2395_);
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
lean_dec(v_a_2386_);
lean_dec_ref(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v___y_2369_);
lean_dec(v___y_2368_);
lean_dec_ref(v_a_2291_);
lean_dec_ref(v___f_2290_);
lean_dec_ref(v___x_2289_);
lean_dec_ref(v___x_2288_);
lean_dec_ref(v___x_2287_);
lean_dec(v___x_2286_);
lean_dec_ref(v___f_2285_);
lean_dec_ref(v_snd_2284_);
lean_dec(v_discharge_x3f_2283_);
lean_dec_ref(v_simprocs_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2277_);
lean_dec(v_snd_2274_);
v_a_2485_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2487_ = v___x_2389_;
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2389_);
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
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v___y_2369_);
lean_dec(v___y_2368_);
lean_dec_ref(v_a_2291_);
lean_dec_ref(v___f_2290_);
lean_dec_ref(v___x_2289_);
lean_dec_ref(v___x_2288_);
lean_dec_ref(v___x_2287_);
lean_dec(v___x_2286_);
lean_dec_ref(v___f_2285_);
lean_dec_ref(v_snd_2284_);
lean_dec(v_discharge_x3f_2283_);
lean_dec_ref(v_simprocs_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2277_);
lean_dec(v_snd_2274_);
v_a_2493_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2495_ = v___x_2385_;
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2385_);
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
lean_dec(v_a_2382_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v___y_2369_);
lean_dec(v___y_2368_);
lean_dec_ref(v_a_2291_);
lean_dec_ref(v___f_2290_);
lean_dec_ref(v___x_2289_);
lean_dec_ref(v___x_2288_);
lean_dec_ref(v___x_2287_);
lean_dec(v___x_2286_);
lean_dec_ref(v___f_2285_);
lean_dec_ref(v_snd_2284_);
lean_dec(v_discharge_x3f_2283_);
lean_dec_ref(v_simprocs_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2277_);
lean_dec(v_snd_2274_);
v_a_2501_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2508_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2503_ = v___x_2383_;
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_a_2501_);
lean_dec(v___x_2383_);
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
else
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2516_; 
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v___y_2369_);
lean_dec(v___y_2368_);
lean_dec_ref(v_a_2291_);
lean_dec_ref(v___f_2290_);
lean_dec_ref(v___x_2289_);
lean_dec_ref(v___x_2288_);
lean_dec_ref(v___x_2287_);
lean_dec(v___x_2286_);
lean_dec_ref(v___f_2285_);
lean_dec_ref(v_snd_2284_);
lean_dec(v_discharge_x3f_2283_);
lean_dec_ref(v_simprocs_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2277_);
lean_dec(v_snd_2274_);
v_a_2509_ = lean_ctor_get(v___x_2381_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2511_ = v___x_2381_;
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2381_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2514_; 
if (v_isShared_2512_ == 0)
{
v___x_2514_ = v___x_2511_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_a_2509_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___boxed(lean_object** _args){
lean_object* v_usingArg_2646_ = _args[0];
lean_object* v_snd_2647_ = _args[1];
lean_object* v___x_2648_ = _args[2];
lean_object* v___x_2649_ = _args[3];
lean_object* v___x_2650_ = _args[4];
lean_object* v_useReducible_2651_ = _args[5];
lean_object* v___x_2652_ = _args[6];
lean_object* v___x_2653_ = _args[7];
lean_object* v___x_2654_ = _args[8];
lean_object* v_simprocs_2655_ = _args[9];
lean_object* v_discharge_x3f_2656_ = _args[10];
lean_object* v_snd_2657_ = _args[11];
lean_object* v___f_2658_ = _args[12];
lean_object* v___x_2659_ = _args[13];
lean_object* v___x_2660_ = _args[14];
lean_object* v___x_2661_ = _args[15];
lean_object* v___x_2662_ = _args[16];
lean_object* v___f_2663_ = _args[17];
lean_object* v_a_2664_ = _args[18];
lean_object* v___x_2665_ = _args[19];
lean_object* v___f_2666_ = _args[20];
lean_object* v___y_2667_ = _args[21];
lean_object* v___y_2668_ = _args[22];
lean_object* v___y_2669_ = _args[23];
lean_object* v___y_2670_ = _args[24];
lean_object* v___y_2671_ = _args[25];
lean_object* v___y_2672_ = _args[26];
lean_object* v___y_2673_ = _args[27];
lean_object* v___y_2674_ = _args[28];
lean_object* v___y_2675_ = _args[29];
_start:
{
uint8_t v___x_95476__boxed_2676_; uint8_t v___x_95477__boxed_2677_; uint8_t v_useReducible_boxed_2678_; uint8_t v___x_95479__boxed_2679_; lean_object* v_res_2680_; 
v___x_95476__boxed_2676_ = lean_unbox(v___x_2648_);
v___x_95477__boxed_2677_ = lean_unbox(v___x_2649_);
v_useReducible_boxed_2678_ = lean_unbox(v_useReducible_2651_);
v___x_95479__boxed_2679_ = lean_unbox(v___x_2652_);
v_res_2680_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5(v_usingArg_2646_, v_snd_2647_, v___x_95476__boxed_2676_, v___x_95477__boxed_2677_, v___x_2650_, v_useReducible_boxed_2678_, v___x_95479__boxed_2679_, v___x_2653_, v___x_2654_, v_simprocs_2655_, v_discharge_x3f_2656_, v_snd_2657_, v___f_2658_, v___x_2659_, v___x_2660_, v___x_2661_, v___x_2662_, v___f_2663_, v_a_2664_, v___x_2665_, v___f_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec(v___x_2665_);
lean_dec(v___x_2653_);
return v_res_2680_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0(void){
_start:
{
lean_object* v___x_2681_; 
v___x_2681_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2681_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1(void){
_start:
{
lean_object* v___x_2682_; lean_object* v___x_2683_; 
v___x_2682_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0);
v___x_2683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2683_, 0, v___x_2682_);
return v___x_2683_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2(void){
_start:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2684_ = lean_unsigned_to_nat(32u);
v___x_2685_ = lean_mk_empty_array_with_capacity(v___x_2684_);
v___x_2686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2685_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6(lean_object* v___x_2687_, lean_object* v_tk_2688_, lean_object* v___x_2689_, lean_object* v___x_2690_, lean_object* v___x_2691_, lean_object* v_simprocs_2692_, uint8_t v___x_2693_, lean_object* v_usingArg_2694_, uint8_t v___x_2695_, lean_object* v___x_2696_, uint8_t v_useReducible_2697_, uint8_t v___x_2698_, lean_object* v___x_2699_, lean_object* v___f_2700_, lean_object* v___x_2701_, lean_object* v___x_2702_, lean_object* v___x_2703_, lean_object* v___f_2704_, lean_object* v_a_2705_, lean_object* v_usingTk_x3f_2706_, lean_object* v_discharge_x3f_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v___y_2718_; 
if (lean_obj_tag(v_usingTk_x3f_2706_) == 0)
{
lean_object* v___x_2832_; 
v___x_2832_ = lean_box(0);
v___y_2718_ = v___x_2832_;
goto v___jp_2717_;
}
else
{
lean_object* v_val_2833_; 
v_val_2833_ = lean_ctor_get(v_usingTk_x3f_2706_, 0);
lean_inc(v_val_2833_);
lean_dec_ref_known(v_usingTk_x3f_2706_, 1);
v___y_2718_ = v_val_2833_;
goto v___jp_2717_;
}
v___jp_2717_:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2719_ = lean_mk_empty_array_with_capacity(v___x_2687_);
v___x_2720_ = lean_array_push(v___x_2719_, v_tk_2688_);
v___x_2721_ = lean_array_push(v___x_2720_, v___y_2718_);
v___x_2722_ = lean_box(2);
lean_inc(v___x_2689_);
v___x_2723_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2722_);
lean_ctor_set(v___x_2723_, 1, v___x_2689_);
lean_ctor_set(v___x_2723_, 2, v___x_2721_);
v___x_2724_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_2723_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
if (lean_obj_tag(v___x_2724_) == 0)
{
lean_object* v_a_2725_; lean_object* v___x_2726_; 
v_a_2725_ = lean_ctor_get(v___x_2724_, 0);
lean_inc(v_a_2725_);
lean_dec_ref_known(v___x_2724_, 1);
v___x_2726_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2709_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
if (lean_obj_tag(v___x_2726_) == 0)
{
lean_object* v_a_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; size_t v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
v_a_2727_ = lean_ctor_get(v___x_2726_, 0);
lean_inc(v_a_2727_);
lean_dec_ref_known(v___x_2726_, 1);
v___x_2728_ = lean_mk_empty_array_with_capacity(v___x_2690_);
v___x_2729_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1);
lean_inc_n(v___x_2690_, 3);
v___x_2730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2730_, 0, v___x_2729_);
lean_ctor_set(v___x_2730_, 1, v___x_2690_);
v___x_2731_ = lean_unsigned_to_nat(32u);
v___x_2732_ = lean_mk_empty_array_with_capacity(v___x_2731_);
v___x_2733_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2);
v___x_2734_ = ((size_t)5ULL);
v___x_2735_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2735_, 0, v___x_2733_);
lean_ctor_set(v___x_2735_, 1, v___x_2732_);
lean_ctor_set(v___x_2735_, 2, v___x_2690_);
lean_ctor_set(v___x_2735_, 3, v___x_2690_);
lean_ctor_set_usize(v___x_2735_, 4, v___x_2734_);
v___x_2736_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2729_);
lean_ctor_set(v___x_2736_, 1, v___x_2729_);
lean_ctor_set(v___x_2736_, 2, v___x_2729_);
lean_ctor_set(v___x_2736_, 3, v___x_2735_);
v___x_2737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2737_, 0, v___x_2730_);
lean_ctor_set(v___x_2737_, 1, v___x_2736_);
lean_inc_ref(v___x_2737_);
lean_inc(v_discharge_x3f_2707_);
lean_inc_ref(v_simprocs_2692_);
lean_inc_ref(v___x_2691_);
v___x_2738_ = l_Lean_Meta_simpGoal(v_a_2727_, v___x_2691_, v_simprocs_2692_, v_discharge_x3f_2707_, v___x_2693_, v___x_2728_, v___x_2737_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
if (lean_obj_tag(v___x_2738_) == 0)
{
lean_object* v_a_2739_; lean_object* v_fst_2740_; 
v_a_2739_ = lean_ctor_get(v___x_2738_, 0);
lean_inc(v_a_2739_);
lean_dec_ref_known(v___x_2738_, 1);
v_fst_2740_ = lean_ctor_get(v_a_2739_, 0);
if (lean_obj_tag(v_fst_2740_) == 1)
{
lean_object* v_val_2741_; lean_object* v_snd_2742_; lean_object* v_snd_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2767_; 
lean_dec_ref_known(v___x_2737_, 2);
v_val_2741_ = lean_ctor_get(v_fst_2740_, 0);
lean_inc(v_val_2741_);
v_snd_2742_ = lean_ctor_get(v_a_2739_, 1);
lean_inc(v_snd_2742_);
lean_dec(v_a_2739_);
v_snd_2743_ = lean_ctor_get(v_val_2741_, 1);
v_isSharedCheck_2767_ = !lean_is_exclusive(v_val_2741_);
if (v_isSharedCheck_2767_ == 0)
{
lean_object* v_unused_2768_; 
v_unused_2768_ = lean_ctor_get(v_val_2741_, 0);
lean_dec(v_unused_2768_);
v___x_2745_ = v_val_2741_;
v_isShared_2746_ = v_isSharedCheck_2767_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_snd_2743_);
lean_dec(v_val_2741_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2767_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2747_; lean_object* v___x_2749_; 
v___x_2747_ = lean_box(0);
lean_inc(v_snd_2743_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set_tag(v___x_2745_, 1);
lean_ctor_set(v___x_2745_, 1, v___x_2747_);
lean_ctor_set(v___x_2745_, 0, v_snd_2743_);
v___x_2749_ = v___x_2745_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_snd_2743_);
lean_ctor_set(v_reuseFailAlloc_2766_, 1, v___x_2747_);
v___x_2749_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
lean_object* v___x_2750_; 
v___x_2750_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2749_, v___y_2709_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v___f_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___y_2756_; lean_object* v___x_2757_; 
lean_dec_ref_known(v___x_2750_, 1);
v___f_2751_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___boxed), 11, 1);
lean_closure_set(v___f_2751_, 0, v_a_2725_);
v___x_2752_ = lean_box(v___x_2693_);
v___x_2753_ = lean_box(v___x_2695_);
v___x_2754_ = lean_box(v_useReducible_2697_);
v___x_2755_ = lean_box(v___x_2698_);
lean_inc(v_snd_2743_);
v___y_2756_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___boxed), 30, 21);
lean_closure_set(v___y_2756_, 0, v_usingArg_2694_);
lean_closure_set(v___y_2756_, 1, v_snd_2743_);
lean_closure_set(v___y_2756_, 2, v___x_2752_);
lean_closure_set(v___y_2756_, 3, v___x_2753_);
lean_closure_set(v___y_2756_, 4, v___x_2696_);
lean_closure_set(v___y_2756_, 5, v___x_2754_);
lean_closure_set(v___y_2756_, 6, v___x_2755_);
lean_closure_set(v___y_2756_, 7, v___x_2699_);
lean_closure_set(v___y_2756_, 8, v___x_2691_);
lean_closure_set(v___y_2756_, 9, v_simprocs_2692_);
lean_closure_set(v___y_2756_, 10, v_discharge_x3f_2707_);
lean_closure_set(v___y_2756_, 11, v_snd_2742_);
lean_closure_set(v___y_2756_, 12, v___f_2700_);
lean_closure_set(v___y_2756_, 13, v___x_2689_);
lean_closure_set(v___y_2756_, 14, v___x_2701_);
lean_closure_set(v___y_2756_, 15, v___x_2702_);
lean_closure_set(v___y_2756_, 16, v___x_2703_);
lean_closure_set(v___y_2756_, 17, v___f_2704_);
lean_closure_set(v___y_2756_, 18, v_a_2705_);
lean_closure_set(v___y_2756_, 19, v___x_2690_);
lean_closure_set(v___y_2756_, 20, v___f_2751_);
v___x_2757_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___redArg(v_snd_2743_, v___y_2756_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
return v___x_2757_;
}
else
{
lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2765_; 
lean_dec(v_snd_2743_);
lean_dec(v_snd_2742_);
lean_dec(v_a_2725_);
lean_dec(v_discharge_x3f_2707_);
lean_dec_ref(v_a_2705_);
lean_dec_ref(v___f_2704_);
lean_dec_ref(v___x_2703_);
lean_dec_ref(v___x_2702_);
lean_dec_ref(v___x_2701_);
lean_dec_ref(v___f_2700_);
lean_dec(v___x_2699_);
lean_dec_ref(v___x_2696_);
lean_dec(v_usingArg_2694_);
lean_dec_ref(v_simprocs_2692_);
lean_dec_ref(v___x_2691_);
lean_dec(v___x_2690_);
lean_dec(v___x_2689_);
v_a_2758_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2760_ = v___x_2750_;
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2750_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2763_; 
if (v_isShared_2761_ == 0)
{
v___x_2763_ = v___x_2760_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_a_2758_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
}
}
}
else
{
lean_object* v___x_2769_; lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2807_; 
lean_dec(v_a_2739_);
lean_dec(v_a_2725_);
lean_dec(v_discharge_x3f_2707_);
lean_dec_ref(v___x_2703_);
lean_dec_ref(v___x_2702_);
lean_dec_ref(v___x_2701_);
lean_dec_ref(v___f_2700_);
lean_dec(v___x_2699_);
lean_dec_ref(v___x_2696_);
lean_dec(v_usingArg_2694_);
lean_dec_ref(v_simprocs_2692_);
lean_dec_ref(v___x_2691_);
lean_dec(v___x_2690_);
lean_dec(v___x_2689_);
v___x_2769_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
v_a_2770_ = lean_ctor_get(v___x_2769_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2772_ = v___x_2769_;
v_isShared_2773_ = v_isSharedCheck_2807_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v___x_2769_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2807_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
uint8_t v___x_2774_; 
v___x_2774_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_a_2770_);
lean_dec(v_a_2770_);
if (v___x_2774_ == 0)
{
lean_object* v___x_2776_; 
lean_dec_ref(v_a_2705_);
lean_dec_ref(v___f_2704_);
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 0, v___x_2737_);
v___x_2776_ = v___x_2772_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v___x_2737_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
else
{
lean_object* v_ref_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
lean_del_object(v___x_2772_);
v_ref_2778_ = lean_ctor_get(v___y_2714_, 2);
v___x_2779_ = lean_box(0);
lean_inc(v___y_2715_);
lean_inc_ref(v___y_2714_);
lean_inc(v___y_2713_);
lean_inc_ref(v___y_2712_);
lean_inc(v___y_2711_);
lean_inc_ref(v___y_2710_);
lean_inc(v___y_2709_);
lean_inc_ref(v___y_2708_);
v___x_2780_ = lean_apply_10(v___f_2704_, v___x_2779_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, lean_box(0));
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2781_; lean_object* v___x_2782_; 
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_a_2781_);
lean_dec_ref_known(v___x_2780_, 1);
lean_inc(v_ref_2778_);
v___x_2782_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa(v_a_2705_, v_ref_2778_, v_a_2781_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2789_ == 0)
{
lean_object* v_unused_2790_; 
v_unused_2790_ = lean_ctor_get(v___x_2782_, 0);
lean_dec(v_unused_2790_);
v___x_2784_ = v___x_2782_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_dec(v___x_2782_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
lean_ctor_set(v___x_2784_, 0, v___x_2737_);
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v___x_2737_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
else
{
lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2798_; 
lean_dec_ref_known(v___x_2737_, 2);
v_a_2791_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2793_ = v___x_2782_;
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v___x_2782_);
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
else
{
lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2806_; 
lean_dec_ref_known(v___x_2737_, 2);
lean_dec_ref(v_a_2705_);
v_a_2799_ = lean_ctor_get(v___x_2780_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2801_ = v___x_2780_;
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v___x_2780_);
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
}
}
else
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2815_; 
lean_dec_ref_known(v___x_2737_, 2);
lean_dec(v_a_2725_);
lean_dec(v_discharge_x3f_2707_);
lean_dec_ref(v_a_2705_);
lean_dec_ref(v___f_2704_);
lean_dec_ref(v___x_2703_);
lean_dec_ref(v___x_2702_);
lean_dec_ref(v___x_2701_);
lean_dec_ref(v___f_2700_);
lean_dec(v___x_2699_);
lean_dec_ref(v___x_2696_);
lean_dec(v_usingArg_2694_);
lean_dec_ref(v_simprocs_2692_);
lean_dec_ref(v___x_2691_);
lean_dec(v___x_2690_);
lean_dec(v___x_2689_);
v_a_2808_ = lean_ctor_get(v___x_2738_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2810_ = v___x_2738_;
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2738_);
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
lean_dec(v_a_2725_);
lean_dec(v_discharge_x3f_2707_);
lean_dec_ref(v_a_2705_);
lean_dec_ref(v___f_2704_);
lean_dec_ref(v___x_2703_);
lean_dec_ref(v___x_2702_);
lean_dec_ref(v___x_2701_);
lean_dec_ref(v___f_2700_);
lean_dec(v___x_2699_);
lean_dec_ref(v___x_2696_);
lean_dec(v_usingArg_2694_);
lean_dec_ref(v_simprocs_2692_);
lean_dec_ref(v___x_2691_);
lean_dec(v___x_2690_);
lean_dec(v___x_2689_);
v_a_2816_ = lean_ctor_get(v___x_2726_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2726_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2818_ = v___x_2726_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2726_);
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
else
{
lean_object* v_a_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2831_; 
lean_dec(v_discharge_x3f_2707_);
lean_dec_ref(v_a_2705_);
lean_dec_ref(v___f_2704_);
lean_dec_ref(v___x_2703_);
lean_dec_ref(v___x_2702_);
lean_dec_ref(v___x_2701_);
lean_dec_ref(v___f_2700_);
lean_dec(v___x_2699_);
lean_dec_ref(v___x_2696_);
lean_dec(v_usingArg_2694_);
lean_dec_ref(v_simprocs_2692_);
lean_dec_ref(v___x_2691_);
lean_dec(v___x_2690_);
lean_dec(v___x_2689_);
v_a_2824_ = lean_ctor_get(v___x_2724_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2724_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2826_ = v___x_2724_;
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_a_2824_);
lean_dec(v___x_2724_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v___x_2829_; 
if (v_isShared_2827_ == 0)
{
v___x_2829_ = v___x_2826_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_a_2824_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
return v___x_2829_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___boxed(lean_object** _args){
lean_object* v___x_2834_ = _args[0];
lean_object* v_tk_2835_ = _args[1];
lean_object* v___x_2836_ = _args[2];
lean_object* v___x_2837_ = _args[3];
lean_object* v___x_2838_ = _args[4];
lean_object* v_simprocs_2839_ = _args[5];
lean_object* v___x_2840_ = _args[6];
lean_object* v_usingArg_2841_ = _args[7];
lean_object* v___x_2842_ = _args[8];
lean_object* v___x_2843_ = _args[9];
lean_object* v_useReducible_2844_ = _args[10];
lean_object* v___x_2845_ = _args[11];
lean_object* v___x_2846_ = _args[12];
lean_object* v___f_2847_ = _args[13];
lean_object* v___x_2848_ = _args[14];
lean_object* v___x_2849_ = _args[15];
lean_object* v___x_2850_ = _args[16];
lean_object* v___f_2851_ = _args[17];
lean_object* v_a_2852_ = _args[18];
lean_object* v_usingTk_x3f_2853_ = _args[19];
lean_object* v_discharge_x3f_2854_ = _args[20];
lean_object* v___y_2855_ = _args[21];
lean_object* v___y_2856_ = _args[22];
lean_object* v___y_2857_ = _args[23];
lean_object* v___y_2858_ = _args[24];
lean_object* v___y_2859_ = _args[25];
lean_object* v___y_2860_ = _args[26];
lean_object* v___y_2861_ = _args[27];
lean_object* v___y_2862_ = _args[28];
lean_object* v___y_2863_ = _args[29];
_start:
{
uint8_t v___x_96271__boxed_2864_; uint8_t v___x_96272__boxed_2865_; uint8_t v_useReducible_boxed_2866_; uint8_t v___x_96274__boxed_2867_; lean_object* v_res_2868_; 
v___x_96271__boxed_2864_ = lean_unbox(v___x_2840_);
v___x_96272__boxed_2865_ = lean_unbox(v___x_2842_);
v_useReducible_boxed_2866_ = lean_unbox(v_useReducible_2844_);
v___x_96274__boxed_2867_ = lean_unbox(v___x_2845_);
v_res_2868_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6(v___x_2834_, v_tk_2835_, v___x_2836_, v___x_2837_, v___x_2838_, v_simprocs_2839_, v___x_96271__boxed_2864_, v_usingArg_2841_, v___x_96272__boxed_2865_, v___x_2843_, v_useReducible_boxed_2866_, v___x_96274__boxed_2867_, v___x_2846_, v___f_2847_, v___x_2848_, v___x_2849_, v___x_2850_, v___f_2851_, v_a_2852_, v_usingTk_x3f_2853_, v_discharge_x3f_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2861_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
lean_dec(v___y_2858_);
lean_dec_ref(v___y_2857_);
lean_dec(v___y_2856_);
lean_dec_ref(v___y_2855_);
lean_dec(v___x_2834_);
return v_res_2868_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__4(void){
_start:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2873_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__3));
v___x_2874_ = lean_unsigned_to_nat(38u);
v___x_2875_ = lean_unsigned_to_nat(159u);
v___x_2876_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__2));
v___x_2877_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__1));
v___x_2878_ = l_mkPanicMessageWithDecl(v___x_2877_, v___x_2876_, v___x_2875_, v___x_2874_, v___x_2873_);
return v___x_2878_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12(void){
_start:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
v___x_2886_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__3));
v___x_2887_ = lean_unsigned_to_nat(15u);
v___x_2888_ = lean_unsigned_to_nat(160u);
v___x_2889_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__2));
v___x_2890_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__1));
v___x_2891_ = l_mkPanicMessageWithDecl(v___x_2890_, v___x_2889_, v___x_2888_, v___x_2887_, v___x_2886_);
return v___x_2891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7(lean_object* v_tk_2893_, lean_object* v___x_2894_, lean_object* v___x_2895_, lean_object* v___x_2896_, lean_object* v___x_2897_, uint8_t v___x_2898_, lean_object* v___x_2899_, lean_object* v___x_2900_, uint8_t v_useReducible_2901_, lean_object* v___f_2902_, lean_object* v___x_2903_, lean_object* v___x_2904_, lean_object* v___x_2905_, lean_object* v___x_2906_, lean_object* v___x_2907_, lean_object* v___x_2908_, lean_object* v_usingArg_2909_, lean_object* v___x_2910_, uint8_t v___x_2911_, lean_object* v___f_2912_, lean_object* v_usingTk_x3f_2913_, lean_object* v_squeeze_2914_, lean_object* v_unfold_2915_, lean_object* v_args_2916_, lean_object* v_only_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_){
_start:
{
lean_object* v___y_2929_; lean_object* v___y_2933_; lean_object* v_stx_2934_; lean_object* v___y_2935_; lean_object* v_ref_2936_; lean_object* v___y_2937_; lean_object* v___y_2956_; lean_object* v_stx_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v___y_2966_; lean_object* v___y_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___x_2982_; 
v___x_2982_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_2920_, v___y_2922_, v___y_2924_, v___y_2926_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_a_2983_; lean_object* v_toCold_2984_; lean_object* v_ref_2985_; uint8_t v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; uint8_t v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; uint8_t v___y_3399_; lean_object* v___y_3400_; lean_object* v_args_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3435_; lean_object* v___y_3436_; lean_object* v___y_3437_; lean_object* v___y_3438_; uint8_t v___y_3439_; lean_object* v___y_3440_; lean_object* v_only_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3469_; uint8_t v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3529_; lean_object* v___y_3530_; uint8_t v___y_3531_; lean_object* v___y_3542_; uint8_t v___y_3543_; lean_object* v___y_3544_; uint8_t v___y_3545_; lean_object* v___y_3547_; lean_object* v___y_3548_; lean_object* v___y_3549_; uint8_t v___y_3550_; lean_object* v___y_3551_; lean_object* v___y_3572_; lean_object* v___y_3573_; lean_object* v___y_3574_; lean_object* v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3620_; 
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
lean_inc(v_a_2983_);
lean_dec_ref_known(v___x_2982_, 1);
v_toCold_2984_ = lean_ctor_get(v___y_2925_, 0);
v_ref_2985_ = lean_ctor_get(v___y_2925_, 2);
v___x_2986_ = 0;
v___x_2987_ = l_Lean_SourceInfo_fromRef(v_ref_2985_, v___x_2986_);
v___x_2988_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__3));
lean_inc_ref(v___x_2896_);
lean_inc_ref(v___x_2895_);
lean_inc_ref(v___x_2894_);
v___x_2989_ = l_Lean_Name_mkStr4(v___x_2894_, v___x_2895_, v___x_2896_, v___x_2988_);
lean_inc(v___x_2987_);
v___x_2990_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2990_, 0, v___x_2987_);
lean_ctor_set(v___x_2990_, 1, v___x_2988_);
v___x_2991_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_2992_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6);
if (lean_obj_tag(v___y_2918_) == 0)
{
lean_object* v___x_3629_; 
v___x_3629_ = lean_mk_empty_array_with_capacity(v___x_2897_);
v___y_3620_ = v___x_3629_;
goto v___jp_3619_;
}
else
{
lean_object* v_val_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; 
v_val_3630_ = lean_ctor_get(v___y_2918_, 0);
lean_inc(v_val_3630_);
lean_dec_ref_known(v___y_2918_, 1);
v___x_3631_ = lean_mk_empty_array_with_capacity(v___x_2897_);
v___x_3632_ = lean_array_push(v___x_3631_, v_val_3630_);
v___y_3620_ = v___x_3632_;
goto v___jp_3619_;
}
v___jp_2993_:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3005_ = l_Array_append___redArg(v___x_2992_, v___y_3004_);
lean_dec_ref(v___y_3004_);
lean_inc_n(v___y_2995_, 2);
v___x_3006_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3006_, 0, v___y_2995_);
lean_ctor_set(v___x_3006_, 1, v___x_2991_);
lean_ctor_set(v___x_3006_, 2, v___x_3005_);
v___x_3007_ = l_Lean_Syntax_node5(v___y_2995_, v___x_2899_, v___y_3000_, v___y_2998_, v___y_3002_, v___y_2999_, v___x_3006_);
v___x_3008_ = l_Lean_Syntax_node2(v___y_2995_, v___y_2994_, v___y_3001_, v___x_3007_);
v___y_2956_ = v___y_2996_;
v_stx_2957_ = v___x_3008_;
v___y_2958_ = v___y_2997_;
v___y_2959_ = v___y_3003_;
goto v___jp_2955_;
}
v___jp_3009_:
{
lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___x_3021_ = l_Array_append___redArg(v___x_2992_, v___y_3020_);
lean_dec_ref(v___y_3020_);
lean_inc(v___y_3011_);
v___x_3022_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3022_, 0, v___y_3011_);
lean_ctor_set(v___x_3022_, 1, v___x_2991_);
lean_ctor_set(v___x_3022_, 2, v___x_3021_);
if (lean_obj_tag(v___y_3013_) == 1)
{
lean_object* v_val_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; 
lean_dec(v___x_2897_);
v_val_3023_ = lean_ctor_get(v___y_3013_, 0);
lean_inc(v_val_3023_);
lean_dec_ref_known(v___y_3013_, 1);
v___x_3024_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__5));
lean_inc(v___y_3011_);
v___x_3025_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3025_, 0, v___y_3011_);
lean_ctor_set(v___x_3025_, 1, v___x_3024_);
v___x_3026_ = l_Array_mkArray2___redArg(v___x_3025_, v_val_3023_);
v___y_2994_ = v___y_3010_;
v___y_2995_ = v___y_3011_;
v___y_2996_ = v___y_3012_;
v___y_2997_ = v___y_3014_;
v___y_2998_ = v___y_3015_;
v___y_2999_ = v___x_3022_;
v___y_3000_ = v___y_3016_;
v___y_3001_ = v___y_3017_;
v___y_3002_ = v___y_3018_;
v___y_3003_ = v___y_3019_;
v___y_3004_ = v___x_3026_;
goto v___jp_2993_;
}
else
{
lean_object* v___x_3027_; 
lean_dec(v___y_3013_);
v___x_3027_ = lean_mk_empty_array_with_capacity(v___x_2897_);
lean_dec(v___x_2897_);
v___y_2994_ = v___y_3010_;
v___y_2995_ = v___y_3011_;
v___y_2996_ = v___y_3012_;
v___y_2997_ = v___y_3014_;
v___y_2998_ = v___y_3015_;
v___y_2999_ = v___x_3022_;
v___y_3000_ = v___y_3016_;
v___y_3001_ = v___y_3017_;
v___y_3002_ = v___y_3018_;
v___y_3003_ = v___y_3019_;
v___y_3004_ = v___x_3027_;
goto v___jp_2993_;
}
}
v___jp_3028_:
{
lean_object* v___x_3040_; lean_object* v___x_3041_; 
v___x_3040_ = l_Array_append___redArg(v___x_2992_, v___y_3039_);
lean_dec_ref(v___y_3039_);
lean_inc(v___y_3030_);
v___x_3041_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3041_, 0, v___y_3030_);
lean_ctor_set(v___x_3041_, 1, v___x_2991_);
lean_ctor_set(v___x_3041_, 2, v___x_3040_);
if (lean_obj_tag(v___y_3032_) == 1)
{
lean_object* v_val_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; 
v_val_3042_ = lean_ctor_get(v___y_3032_, 0);
lean_inc(v_val_3042_);
lean_dec_ref_known(v___y_3032_, 1);
v___x_3043_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_3044_ = l_Lean_Name_mkStr4(v___x_2894_, v___x_2895_, v___x_2896_, v___x_3043_);
v___x_3045_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_3030_, 4);
v___x_3046_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3046_, 0, v___y_3030_);
lean_ctor_set(v___x_3046_, 1, v___x_3045_);
v___x_3047_ = l_Array_append___redArg(v___x_2992_, v_val_3042_);
lean_dec(v_val_3042_);
v___x_3048_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3048_, 0, v___y_3030_);
lean_ctor_set(v___x_3048_, 1, v___x_2991_);
lean_ctor_set(v___x_3048_, 2, v___x_3047_);
v___x_3049_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_3050_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3050_, 0, v___y_3030_);
lean_ctor_set(v___x_3050_, 1, v___x_3049_);
v___x_3051_ = l_Lean_Syntax_node3(v___y_3030_, v___x_3044_, v___x_3046_, v___x_3048_, v___x_3050_);
v___x_3052_ = l_Array_mkArray1___redArg(v___x_3051_);
v___y_3010_ = v___y_3029_;
v___y_3011_ = v___y_3030_;
v___y_3012_ = v___y_3031_;
v___y_3013_ = v___y_3034_;
v___y_3014_ = v___y_3033_;
v___y_3015_ = v___y_3035_;
v___y_3016_ = v___y_3036_;
v___y_3017_ = v___y_3037_;
v___y_3018_ = v___x_3041_;
v___y_3019_ = v___y_3038_;
v___y_3020_ = v___x_3052_;
goto v___jp_3009_;
}
else
{
lean_object* v___x_3053_; 
lean_dec(v___y_3032_);
lean_dec_ref(v___x_2896_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___x_2894_);
v___x_3053_ = lean_mk_empty_array_with_capacity(v___x_2897_);
v___y_3010_ = v___y_3029_;
v___y_3011_ = v___y_3030_;
v___y_3012_ = v___y_3031_;
v___y_3013_ = v___y_3034_;
v___y_3014_ = v___y_3033_;
v___y_3015_ = v___y_3035_;
v___y_3016_ = v___y_3036_;
v___y_3017_ = v___y_3037_;
v___y_3018_ = v___x_3041_;
v___y_3019_ = v___y_3038_;
v___y_3020_ = v___x_3053_;
goto v___jp_3009_;
}
}
v___jp_3054_:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3066_ = l_Array_append___redArg(v___x_2992_, v___y_3065_);
lean_dec_ref(v___y_3065_);
lean_inc(v___y_3056_);
v___x_3067_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3067_, 0, v___y_3056_);
lean_ctor_set(v___x_3067_, 1, v___x_2991_);
lean_ctor_set(v___x_3067_, 2, v___x_3066_);
if (lean_obj_tag(v___y_3063_) == 1)
{
lean_object* v_val_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v_val_3068_ = lean_ctor_get(v___y_3063_, 0);
lean_inc(v_val_3068_);
lean_dec_ref_known(v___y_3063_, 1);
v___x_3069_ = l_Lean_SourceInfo_fromRef(v_val_3068_, v___x_2898_);
lean_dec(v_val_3068_);
v___x_3070_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_3071_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3069_);
lean_ctor_set(v___x_3071_, 1, v___x_3070_);
v___x_3072_ = l_Array_mkArray1___redArg(v___x_3071_);
v___y_3029_ = v___y_3055_;
v___y_3030_ = v___y_3056_;
v___y_3031_ = v___y_3057_;
v___y_3032_ = v___y_3058_;
v___y_3033_ = v___y_3060_;
v___y_3034_ = v___y_3059_;
v___y_3035_ = v___x_3067_;
v___y_3036_ = v___y_3061_;
v___y_3037_ = v___y_3062_;
v___y_3038_ = v___y_3064_;
v___y_3039_ = v___x_3072_;
goto v___jp_3028_;
}
else
{
lean_object* v___x_3073_; 
lean_dec(v___y_3063_);
v___x_3073_ = lean_mk_empty_array_with_capacity(v___x_2897_);
v___y_3029_ = v___y_3055_;
v___y_3030_ = v___y_3056_;
v___y_3031_ = v___y_3057_;
v___y_3032_ = v___y_3058_;
v___y_3033_ = v___y_3060_;
v___y_3034_ = v___y_3059_;
v___y_3035_ = v___x_3067_;
v___y_3036_ = v___y_3061_;
v___y_3037_ = v___y_3062_;
v___y_3038_ = v___y_3064_;
v___y_3039_ = v___x_3073_;
goto v___jp_3028_;
}
}
v___jp_3074_:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3089_ = l_Array_append___redArg(v___x_2992_, v___y_3088_);
lean_dec_ref(v___y_3088_);
lean_inc_n(v___y_3081_, 3);
v___x_3090_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3090_, 0, v___y_3081_);
lean_ctor_set(v___x_3090_, 1, v___x_2991_);
lean_ctor_set(v___x_3090_, 2, v___x_3089_);
v___x_3091_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__6));
v___x_3092_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3092_, 0, v___y_3081_);
lean_ctor_set(v___x_3092_, 1, v___x_3091_);
v___x_3093_ = l_Lean_Syntax_node6(v___y_3081_, v___y_3082_, v___y_3084_, v___y_3075_, v___y_3078_, v___x_3090_, v___x_3092_, v___y_3086_);
v___x_3094_ = l_Lean_Syntax_node4(v___y_3081_, v___y_3085_, v___y_3077_, v___y_3076_, v___y_3079_, v___x_3093_);
v___y_2956_ = v___y_3080_;
v_stx_2957_ = v___x_3094_;
v___y_2958_ = v___y_3083_;
v___y_2959_ = v___y_3087_;
goto v___jp_2955_;
}
v___jp_3095_:
{
lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3110_ = l_Array_append___redArg(v___x_2992_, v___y_3109_);
lean_dec_ref(v___y_3109_);
lean_inc(v___y_3101_);
v___x_3111_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3111_, 0, v___y_3101_);
lean_ctor_set(v___x_3111_, 1, v___x_2991_);
lean_ctor_set(v___x_3111_, 2, v___x_3110_);
if (lean_obj_tag(v___y_3097_) == 1)
{
lean_object* v_val_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; 
lean_dec(v___x_2897_);
v_val_3112_ = lean_ctor_get(v___y_3097_, 0);
lean_inc(v_val_3112_);
lean_dec_ref_known(v___y_3097_, 1);
v___x_3113_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_3114_ = l_Lean_Name_mkStr4(v___x_2894_, v___x_2895_, v___x_2896_, v___x_3113_);
v___x_3115_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_3101_, 4);
v___x_3116_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3116_, 0, v___y_3101_);
lean_ctor_set(v___x_3116_, 1, v___x_3115_);
v___x_3117_ = l_Array_append___redArg(v___x_2992_, v_val_3112_);
lean_dec(v_val_3112_);
v___x_3118_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3118_, 0, v___y_3101_);
lean_ctor_set(v___x_3118_, 1, v___x_2991_);
lean_ctor_set(v___x_3118_, 2, v___x_3117_);
v___x_3119_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_3120_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3120_, 0, v___y_3101_);
lean_ctor_set(v___x_3120_, 1, v___x_3119_);
v___x_3121_ = l_Lean_Syntax_node3(v___y_3101_, v___x_3114_, v___x_3116_, v___x_3118_, v___x_3120_);
v___x_3122_ = l_Array_mkArray1___redArg(v___x_3121_);
v___y_3075_ = v___y_3096_;
v___y_3076_ = v___y_3098_;
v___y_3077_ = v___y_3099_;
v___y_3078_ = v___x_3111_;
v___y_3079_ = v___y_3100_;
v___y_3080_ = v___y_3102_;
v___y_3081_ = v___y_3101_;
v___y_3082_ = v___y_3103_;
v___y_3083_ = v___y_3104_;
v___y_3084_ = v___y_3105_;
v___y_3085_ = v___y_3106_;
v___y_3086_ = v___y_3107_;
v___y_3087_ = v___y_3108_;
v___y_3088_ = v___x_3122_;
goto v___jp_3074_;
}
else
{
lean_object* v___x_3123_; 
lean_dec(v___y_3097_);
lean_dec_ref(v___x_2896_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___x_2894_);
v___x_3123_ = lean_mk_empty_array_with_capacity(v___x_2897_);
lean_dec(v___x_2897_);
v___y_3075_ = v___y_3096_;
v___y_3076_ = v___y_3098_;
v___y_3077_ = v___y_3099_;
v___y_3078_ = v___x_3111_;
v___y_3079_ = v___y_3100_;
v___y_3080_ = v___y_3102_;
v___y_3081_ = v___y_3101_;
v___y_3082_ = v___y_3103_;
v___y_3083_ = v___y_3104_;
v___y_3084_ = v___y_3105_;
v___y_3085_ = v___y_3106_;
v___y_3086_ = v___y_3107_;
v___y_3087_ = v___y_3108_;
v___y_3088_ = v___x_3123_;
goto v___jp_3074_;
}
}
v___jp_3124_:
{
lean_object* v___x_3139_; lean_object* v___x_3140_; 
v___x_3139_ = l_Array_append___redArg(v___x_2992_, v___y_3138_);
lean_dec_ref(v___y_3138_);
lean_inc(v___y_3130_);
v___x_3140_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3140_, 0, v___y_3130_);
lean_ctor_set(v___x_3140_, 1, v___x_2991_);
lean_ctor_set(v___x_3140_, 2, v___x_3139_);
if (lean_obj_tag(v___y_3128_) == 1)
{
lean_object* v_val_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; 
v_val_3141_ = lean_ctor_get(v___y_3128_, 0);
lean_inc(v_val_3141_);
lean_dec_ref_known(v___y_3128_, 1);
v___x_3142_ = l_Lean_SourceInfo_fromRef(v_val_3141_, v___x_2898_);
lean_dec(v_val_3141_);
v___x_3143_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_3144_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3142_);
lean_ctor_set(v___x_3144_, 1, v___x_3143_);
v___x_3145_ = l_Array_mkArray1___redArg(v___x_3144_);
v___y_3096_ = v___x_3140_;
v___y_3097_ = v___y_3125_;
v___y_3098_ = v___y_3126_;
v___y_3099_ = v___y_3127_;
v___y_3100_ = v___y_3129_;
v___y_3101_ = v___y_3130_;
v___y_3102_ = v___y_3131_;
v___y_3103_ = v___y_3132_;
v___y_3104_ = v___y_3133_;
v___y_3105_ = v___y_3134_;
v___y_3106_ = v___y_3135_;
v___y_3107_ = v___y_3136_;
v___y_3108_ = v___y_3137_;
v___y_3109_ = v___x_3145_;
goto v___jp_3095_;
}
else
{
lean_object* v___x_3146_; 
lean_dec(v___y_3128_);
v___x_3146_ = lean_mk_empty_array_with_capacity(v___x_2897_);
v___y_3096_ = v___x_3140_;
v___y_3097_ = v___y_3125_;
v___y_3098_ = v___y_3126_;
v___y_3099_ = v___y_3127_;
v___y_3100_ = v___y_3129_;
v___y_3101_ = v___y_3130_;
v___y_3102_ = v___y_3131_;
v___y_3103_ = v___y_3132_;
v___y_3104_ = v___y_3133_;
v___y_3105_ = v___y_3134_;
v___y_3106_ = v___y_3135_;
v___y_3107_ = v___y_3136_;
v___y_3108_ = v___y_3137_;
v___y_3109_ = v___x_3146_;
goto v___jp_3095_;
}
}
v___jp_3147_:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; 
v___x_3159_ = l_Array_append___redArg(v___x_2992_, v___y_3158_);
lean_dec_ref(v___y_3158_);
lean_inc_n(v___y_3156_, 2);
v___x_3160_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3160_, 0, v___y_3156_);
lean_ctor_set(v___x_3160_, 1, v___x_2991_);
lean_ctor_set(v___x_3160_, 2, v___x_3159_);
v___x_3161_ = l_Lean_Syntax_node5(v___y_3156_, v___x_2899_, v___y_3154_, v___y_3150_, v___y_3148_, v___y_3153_, v___x_3160_);
lean_inc(v___y_3152_);
v___x_3162_ = l_Lean_Syntax_node4(v___y_3156_, v___x_2900_, v___y_3155_, v___y_3152_, v___y_3152_, v___x_3161_);
v___y_2956_ = v___y_3149_;
v_stx_2957_ = v___x_3162_;
v___y_2958_ = v___y_3151_;
v___y_2959_ = v___y_3157_;
goto v___jp_2955_;
}
v___jp_3163_:
{
lean_object* v___x_3175_; lean_object* v___x_3176_; 
v___x_3175_ = l_Array_append___redArg(v___x_2992_, v___y_3174_);
lean_dec_ref(v___y_3174_);
lean_inc(v___y_3172_);
v___x_3176_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3176_, 0, v___y_3172_);
lean_ctor_set(v___x_3176_, 1, v___x_2991_);
lean_ctor_set(v___x_3176_, 2, v___x_3175_);
if (lean_obj_tag(v___y_3167_) == 1)
{
lean_object* v_val_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; 
lean_dec(v___x_2897_);
v_val_3177_ = lean_ctor_get(v___y_3167_, 0);
lean_inc(v_val_3177_);
lean_dec_ref_known(v___y_3167_, 1);
v___x_3178_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__5));
lean_inc(v___y_3172_);
v___x_3179_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3179_, 0, v___y_3172_);
lean_ctor_set(v___x_3179_, 1, v___x_3178_);
v___x_3180_ = l_Array_mkArray2___redArg(v___x_3179_, v_val_3177_);
v___y_3148_ = v___y_3164_;
v___y_3149_ = v___y_3166_;
v___y_3150_ = v___y_3165_;
v___y_3151_ = v___y_3168_;
v___y_3152_ = v___y_3169_;
v___y_3153_ = v___x_3176_;
v___y_3154_ = v___y_3170_;
v___y_3155_ = v___y_3171_;
v___y_3156_ = v___y_3172_;
v___y_3157_ = v___y_3173_;
v___y_3158_ = v___x_3180_;
goto v___jp_3147_;
}
else
{
lean_object* v___x_3181_; 
lean_dec(v___y_3167_);
v___x_3181_ = lean_mk_empty_array_with_capacity(v___x_2897_);
lean_dec(v___x_2897_);
v___y_3148_ = v___y_3164_;
v___y_3149_ = v___y_3166_;
v___y_3150_ = v___y_3165_;
v___y_3151_ = v___y_3168_;
v___y_3152_ = v___y_3169_;
v___y_3153_ = v___x_3176_;
v___y_3154_ = v___y_3170_;
v___y_3155_ = v___y_3171_;
v___y_3156_ = v___y_3172_;
v___y_3157_ = v___y_3173_;
v___y_3158_ = v___x_3181_;
goto v___jp_3147_;
}
}
v___jp_3182_:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; 
v___x_3194_ = l_Array_append___redArg(v___x_2992_, v___y_3193_);
lean_dec_ref(v___y_3193_);
lean_inc(v___y_3191_);
v___x_3195_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3195_, 0, v___y_3191_);
lean_ctor_set(v___x_3195_, 1, v___x_2991_);
lean_ctor_set(v___x_3195_, 2, v___x_3194_);
if (lean_obj_tag(v___y_3185_) == 1)
{
lean_object* v_val_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; 
v_val_3196_ = lean_ctor_get(v___y_3185_, 0);
lean_inc(v_val_3196_);
lean_dec_ref_known(v___y_3185_, 1);
v___x_3197_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_3198_ = l_Lean_Name_mkStr4(v___x_2894_, v___x_2895_, v___x_2896_, v___x_3197_);
v___x_3199_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_3191_, 4);
v___x_3200_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3200_, 0, v___y_3191_);
lean_ctor_set(v___x_3200_, 1, v___x_3199_);
v___x_3201_ = l_Array_append___redArg(v___x_2992_, v_val_3196_);
lean_dec(v_val_3196_);
v___x_3202_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3202_, 0, v___y_3191_);
lean_ctor_set(v___x_3202_, 1, v___x_2991_);
lean_ctor_set(v___x_3202_, 2, v___x_3201_);
v___x_3203_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_3204_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3204_, 0, v___y_3191_);
lean_ctor_set(v___x_3204_, 1, v___x_3203_);
v___x_3205_ = l_Lean_Syntax_node3(v___y_3191_, v___x_3198_, v___x_3200_, v___x_3202_, v___x_3204_);
v___x_3206_ = l_Array_mkArray1___redArg(v___x_3205_);
v___y_3164_ = v___x_3195_;
v___y_3165_ = v___y_3184_;
v___y_3166_ = v___y_3183_;
v___y_3167_ = v___y_3187_;
v___y_3168_ = v___y_3186_;
v___y_3169_ = v___y_3188_;
v___y_3170_ = v___y_3189_;
v___y_3171_ = v___y_3190_;
v___y_3172_ = v___y_3191_;
v___y_3173_ = v___y_3192_;
v___y_3174_ = v___x_3206_;
goto v___jp_3163_;
}
else
{
lean_object* v___x_3207_; 
lean_dec(v___y_3185_);
lean_dec_ref(v___x_2896_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___x_2894_);
v___x_3207_ = lean_mk_empty_array_with_capacity(v___x_2897_);
v___y_3164_ = v___x_3195_;
v___y_3165_ = v___y_3184_;
v___y_3166_ = v___y_3183_;
v___y_3167_ = v___y_3187_;
v___y_3168_ = v___y_3186_;
v___y_3169_ = v___y_3188_;
v___y_3170_ = v___y_3189_;
v___y_3171_ = v___y_3190_;
v___y_3172_ = v___y_3191_;
v___y_3173_ = v___y_3192_;
v___y_3174_ = v___x_3207_;
goto v___jp_3163_;
}
}
v___jp_3208_:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; 
v___x_3220_ = l_Array_append___redArg(v___x_2992_, v___y_3219_);
lean_dec_ref(v___y_3219_);
lean_inc(v___y_3217_);
v___x_3221_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3221_, 0, v___y_3217_);
lean_ctor_set(v___x_3221_, 1, v___x_2991_);
lean_ctor_set(v___x_3221_, 2, v___x_3220_);
if (lean_obj_tag(v___y_3215_) == 1)
{
lean_object* v_val_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; 
v_val_3222_ = lean_ctor_get(v___y_3215_, 0);
lean_inc(v_val_3222_);
lean_dec_ref_known(v___y_3215_, 1);
v___x_3223_ = l_Lean_SourceInfo_fromRef(v_val_3222_, v___x_2898_);
lean_dec(v_val_3222_);
v___x_3224_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_3225_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3225_, 0, v___x_3223_);
lean_ctor_set(v___x_3225_, 1, v___x_3224_);
v___x_3226_ = l_Array_mkArray1___redArg(v___x_3225_);
v___y_3183_ = v___y_3209_;
v___y_3184_ = v___x_3221_;
v___y_3185_ = v___y_3210_;
v___y_3186_ = v___y_3212_;
v___y_3187_ = v___y_3211_;
v___y_3188_ = v___y_3213_;
v___y_3189_ = v___y_3214_;
v___y_3190_ = v___y_3216_;
v___y_3191_ = v___y_3217_;
v___y_3192_ = v___y_3218_;
v___y_3193_ = v___x_3226_;
goto v___jp_3182_;
}
else
{
lean_object* v___x_3227_; 
lean_dec(v___y_3215_);
v___x_3227_ = lean_mk_empty_array_with_capacity(v___x_2897_);
v___y_3183_ = v___y_3209_;
v___y_3184_ = v___x_3221_;
v___y_3185_ = v___y_3210_;
v___y_3186_ = v___y_3212_;
v___y_3187_ = v___y_3211_;
v___y_3188_ = v___y_3213_;
v___y_3189_ = v___y_3214_;
v___y_3190_ = v___y_3216_;
v___y_3191_ = v___y_3217_;
v___y_3192_ = v___y_3218_;
v___y_3193_ = v___x_3227_;
goto v___jp_3182_;
}
}
v___jp_3228_:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; 
v___x_3242_ = l_Array_append___redArg(v___x_2992_, v___y_3241_);
lean_dec_ref(v___y_3241_);
lean_inc_n(v___y_3229_, 3);
v___x_3243_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3243_, 0, v___y_3229_);
lean_ctor_set(v___x_3243_, 1, v___x_2991_);
lean_ctor_set(v___x_3243_, 2, v___x_3242_);
v___x_3244_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__6));
v___x_3245_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3245_, 0, v___y_3229_);
lean_ctor_set(v___x_3245_, 1, v___x_3244_);
v___x_3246_ = l_Lean_Syntax_node6(v___y_3229_, v___y_3231_, v___y_3237_, v___y_3238_, v___y_3235_, v___x_3243_, v___x_3245_, v___y_3239_);
lean_inc(v___y_3230_);
v___x_3247_ = l_Lean_Syntax_node4(v___y_3229_, v___y_3232_, v___y_3233_, v___y_3230_, v___y_3230_, v___x_3246_);
v___y_2956_ = v___y_3234_;
v_stx_2957_ = v___x_3247_;
v___y_2958_ = v___y_3236_;
v___y_2959_ = v___y_3240_;
goto v___jp_2955_;
}
v___jp_3248_:
{
lean_object* v___x_3262_; lean_object* v___x_3263_; 
v___x_3262_ = l_Array_append___redArg(v___x_2992_, v___y_3261_);
lean_dec_ref(v___y_3261_);
lean_inc(v___y_3249_);
v___x_3263_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3263_, 0, v___y_3249_);
lean_ctor_set(v___x_3263_, 1, v___x_2991_);
lean_ctor_set(v___x_3263_, 2, v___x_3262_);
if (lean_obj_tag(v___y_3250_) == 1)
{
lean_object* v_val_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; 
lean_dec(v___x_2897_);
v_val_3264_ = lean_ctor_get(v___y_3250_, 0);
lean_inc(v_val_3264_);
lean_dec_ref_known(v___y_3250_, 1);
v___x_3265_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_3266_ = l_Lean_Name_mkStr4(v___x_2894_, v___x_2895_, v___x_2896_, v___x_3265_);
v___x_3267_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_3249_, 4);
v___x_3268_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3268_, 0, v___y_3249_);
lean_ctor_set(v___x_3268_, 1, v___x_3267_);
v___x_3269_ = l_Array_append___redArg(v___x_2992_, v_val_3264_);
lean_dec(v_val_3264_);
v___x_3270_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3270_, 0, v___y_3249_);
lean_ctor_set(v___x_3270_, 1, v___x_2991_);
lean_ctor_set(v___x_3270_, 2, v___x_3269_);
v___x_3271_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_3272_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3272_, 0, v___y_3249_);
lean_ctor_set(v___x_3272_, 1, v___x_3271_);
v___x_3273_ = l_Lean_Syntax_node3(v___y_3249_, v___x_3266_, v___x_3268_, v___x_3270_, v___x_3272_);
v___x_3274_ = l_Array_mkArray1___redArg(v___x_3273_);
v___y_3229_ = v___y_3249_;
v___y_3230_ = v___y_3251_;
v___y_3231_ = v___y_3252_;
v___y_3232_ = v___y_3253_;
v___y_3233_ = v___y_3254_;
v___y_3234_ = v___y_3255_;
v___y_3235_ = v___x_3263_;
v___y_3236_ = v___y_3256_;
v___y_3237_ = v___y_3257_;
v___y_3238_ = v___y_3258_;
v___y_3239_ = v___y_3259_;
v___y_3240_ = v___y_3260_;
v___y_3241_ = v___x_3274_;
goto v___jp_3228_;
}
else
{
lean_object* v___x_3275_; 
lean_dec(v___y_3250_);
lean_dec_ref(v___x_2896_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___x_2894_);
v___x_3275_ = lean_mk_empty_array_with_capacity(v___x_2897_);
lean_dec(v___x_2897_);
v___y_3229_ = v___y_3249_;
v___y_3230_ = v___y_3251_;
v___y_3231_ = v___y_3252_;
v___y_3232_ = v___y_3253_;
v___y_3233_ = v___y_3254_;
v___y_3234_ = v___y_3255_;
v___y_3235_ = v___x_3263_;
v___y_3236_ = v___y_3256_;
v___y_3237_ = v___y_3257_;
v___y_3238_ = v___y_3258_;
v___y_3239_ = v___y_3259_;
v___y_3240_ = v___y_3260_;
v___y_3241_ = v___x_3275_;
goto v___jp_3228_;
}
}
v___jp_3276_:
{
lean_object* v___x_3290_; lean_object* v___x_3291_; 
v___x_3290_ = l_Array_append___redArg(v___x_2992_, v___y_3289_);
lean_dec_ref(v___y_3289_);
lean_inc(v___y_3277_);
v___x_3291_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3291_, 0, v___y_3277_);
lean_ctor_set(v___x_3291_, 1, v___x_2991_);
lean_ctor_set(v___x_3291_, 2, v___x_3290_);
if (lean_obj_tag(v___y_3281_) == 1)
{
lean_object* v_val_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v_val_3292_ = lean_ctor_get(v___y_3281_, 0);
lean_inc(v_val_3292_);
lean_dec_ref_known(v___y_3281_, 1);
v___x_3293_ = l_Lean_SourceInfo_fromRef(v_val_3292_, v___x_2898_);
lean_dec(v_val_3292_);
v___x_3294_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_3295_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3293_);
lean_ctor_set(v___x_3295_, 1, v___x_3294_);
v___x_3296_ = l_Array_mkArray1___redArg(v___x_3295_);
v___y_3249_ = v___y_3277_;
v___y_3250_ = v___y_3278_;
v___y_3251_ = v___y_3279_;
v___y_3252_ = v___y_3280_;
v___y_3253_ = v___y_3282_;
v___y_3254_ = v___y_3283_;
v___y_3255_ = v___y_3284_;
v___y_3256_ = v___y_3285_;
v___y_3257_ = v___y_3286_;
v___y_3258_ = v___x_3291_;
v___y_3259_ = v___y_3287_;
v___y_3260_ = v___y_3288_;
v___y_3261_ = v___x_3296_;
goto v___jp_3248_;
}
else
{
lean_object* v___x_3297_; 
lean_dec(v___y_3281_);
v___x_3297_ = lean_mk_empty_array_with_capacity(v___x_2897_);
v___y_3249_ = v___y_3277_;
v___y_3250_ = v___y_3278_;
v___y_3251_ = v___y_3279_;
v___y_3252_ = v___y_3280_;
v___y_3253_ = v___y_3282_;
v___y_3254_ = v___y_3283_;
v___y_3255_ = v___y_3284_;
v___y_3256_ = v___y_3285_;
v___y_3257_ = v___y_3286_;
v___y_3258_ = v___x_3291_;
v___y_3259_ = v___y_3287_;
v___y_3260_ = v___y_3288_;
v___y_3261_ = v___x_3297_;
goto v___jp_3248_;
}
}
v___jp_3298_:
{
if (v___y_3306_ == 0)
{
if (v_useReducible_2901_ == 0)
{
lean_dec(v___x_2900_);
lean_dec(v___x_2899_);
if (lean_obj_tag(v___y_3303_) == 0)
{
lean_dec(v___y_3313_);
lean_dec(v___y_3310_);
lean_dec(v___y_3305_);
lean_dec(v___y_3300_);
lean_dec_ref(v___x_2903_);
lean_dec_ref(v___f_2902_);
lean_dec(v___x_2897_);
lean_dec_ref(v___x_2896_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___x_2894_);
v___y_2962_ = v___y_3307_;
v___y_2963_ = v___y_3299_;
v___y_2964_ = v___y_3304_;
v___y_2965_ = v___y_3311_;
v___y_2966_ = v___y_3309_;
v___y_2967_ = v___y_3302_;
v___y_2968_ = v___y_3301_;
v___y_2969_ = v___y_3308_;
v___y_2970_ = v___y_3312_;
goto v___jp_2961_;
}
else
{
lean_object* v_val_3314_; lean_object* v___x_3315_; 
v_val_3314_ = lean_ctor_get(v___y_3303_, 0);
lean_inc(v_val_3314_);
lean_dec_ref_known(v___y_3303_, 1);
lean_inc(v___y_3312_);
lean_inc_ref(v___y_3308_);
v___x_3315_ = lean_apply_9(v___f_2902_, v___y_3299_, v___y_3304_, v___y_3311_, v___y_3309_, v___y_3302_, v___y_3301_, v___y_3308_, v___y_3312_, lean_box(0));
if (lean_obj_tag(v___x_3315_) == 0)
{
lean_object* v_a_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v_a_3316_ = lean_ctor_get(v___x_3315_, 0);
lean_inc_n(v_a_3316_, 3);
lean_dec_ref_known(v___x_3315_, 1);
v___x_3317_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__7));
lean_inc_ref_n(v___x_2896_, 2);
lean_inc_ref_n(v___x_2895_, 2);
lean_inc_ref_n(v___x_2894_, 2);
v___x_3318_ = l_Lean_Name_mkStr4(v___x_2894_, v___x_2895_, v___x_2896_, v___x_3317_);
v___x_3319_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3319_, 0, v_a_3316_);
lean_ctor_set(v___x_3319_, 1, v___x_2903_);
v___x_3320_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3320_, 0, v_a_3316_);
lean_ctor_set(v___x_3320_, 1, v___x_2991_);
lean_ctor_set(v___x_3320_, 2, v___x_2992_);
v___x_3321_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__8));
v___x_3322_ = l_Lean_Name_mkStr4(v___x_2894_, v___x_2895_, v___x_2896_, v___x_3321_);
if (lean_obj_tag(v___y_3313_) == 0)
{
lean_object* v___x_3323_; 
v___x_3323_ = lean_mk_empty_array_with_capacity(v___x_2897_);
v___y_3277_ = v_a_3316_;
v___y_3278_ = v___y_3300_;
v___y_3279_ = v___x_3320_;
v___y_3280_ = v___x_3322_;
v___y_3281_ = v___y_3305_;
v___y_3282_ = v___x_3318_;
v___y_3283_ = v___x_3319_;
v___y_3284_ = v___y_3307_;
v___y_3285_ = v___y_3308_;
v___y_3286_ = v___y_3310_;
v___y_3287_ = v_val_3314_;
v___y_3288_ = v___y_3312_;
v___y_3289_ = v___x_3323_;
goto v___jp_3276_;
}
else
{
lean_object* v_val_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
v_val_3324_ = lean_ctor_get(v___y_3313_, 0);
lean_inc(v_val_3324_);
lean_dec_ref_known(v___y_3313_, 1);
v___x_3325_ = lean_mk_empty_array_with_capacity(v___x_2897_);
v___x_3326_ = lean_array_push(v___x_3325_, v_val_3324_);
v___y_3277_ = v_a_3316_;
v___y_3278_ = v___y_3300_;
v___y_3279_ = v___x_3320_;
v___y_3280_ = v___x_3322_;
v___y_3281_ = v___y_3305_;
v___y_3282_ = v___x_3318_;
v___y_3283_ = v___x_3319_;
v___y_3284_ = v___y_3307_;
v___y_3285_ = v___y_3308_;
v___y_3286_ = v___y_3310_;
v___y_3287_ = v_val_3314_;
v___y_3288_ = v___y_3312_;
v___y_3289_ = v___x_3326_;
goto v___jp_3276_;
}
}
else
{
lean_object* v_a_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3334_; 
lean_dec(v_val_3314_);
lean_dec(v___y_3313_);
lean_dec(v___y_3312_);
lean_dec(v___y_3310_);
lean_dec_ref(v___y_3308_);
lean_dec_ref(v___y_3307_);
lean_dec(v___y_3305_);
lean_dec(v___y_3300_);
lean_dec_ref(v___x_2903_);
lean_dec(v___x_2897_);
lean_dec_ref(v___x_2896_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___x_2894_);
lean_dec(v_tk_2893_);
v_a_3327_ = lean_ctor_get(v___x_3315_, 0);
v_isSharedCheck_3334_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3329_ = v___x_3315_;
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_a_3327_);
lean_dec(v___x_3315_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v___x_3332_; 
if (v_isShared_3330_ == 0)
{
v___x_3332_ = v___x_3329_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v_a_3327_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
return v___x_3332_;
}
}
}
}
}
else
{
lean_object* v___x_3335_; 
lean_inc(v___y_3312_);
lean_inc_ref(v___y_3308_);
v___x_3335_ = lean_apply_9(v___f_2902_, v___y_3299_, v___y_3304_, v___y_3311_, v___y_3309_, v___y_3302_, v___y_3301_, v___y_3308_, v___y_3312_, lean_box(0));
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v_a_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
lean_inc_n(v_a_3336_, 3);
lean_dec_ref_known(v___x_3335_, 1);
v___x_3337_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3337_, 0, v_a_3336_);
lean_ctor_set(v___x_3337_, 1, v___x_2903_);
v___x_3338_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3338_, 0, v_a_3336_);
lean_ctor_set(v___x_3338_, 1, v___x_2991_);
lean_ctor_set(v___x_3338_, 2, v___x_2992_);
if (lean_obj_tag(v___y_3313_) == 0)
{
lean_object* v___x_3339_; 
v___x_3339_ = lean_mk_empty_array_with_capacity(v___x_2897_);
v___y_3209_ = v___y_3307_;
v___y_3210_ = v___y_3300_;
v___y_3211_ = v___y_3303_;
v___y_3212_ = v___y_3308_;
v___y_3213_ = v___x_3338_;
v___y_3214_ = v___y_3310_;
v___y_3215_ = v___y_3305_;
v___y_3216_ = v___x_3337_;
v___y_3217_ = v_a_3336_;
v___y_3218_ = v___y_3312_;
v___y_3219_ = v___x_3339_;
goto v___jp_3208_;
}
else
{
lean_object* v_val_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; 
v_val_3340_ = lean_ctor_get(v___y_3313_, 0);
lean_inc(v_val_3340_);
lean_dec_ref_known(v___y_3313_, 1);
v___x_3341_ = lean_mk_empty_array_with_capacity(v___x_2897_);
v___x_3342_ = lean_array_push(v___x_3341_, v_val_3340_);
v___y_3209_ = v___y_3307_;
v___y_3210_ = v___y_3300_;
v___y_3211_ = v___y_3303_;
v___y_3212_ = v___y_3308_;
v___y_3213_ = v___x_3338_;
v___y_3214_ = v___y_3310_;
v___y_3215_ = v___y_3305_;
v___y_3216_ = v___x_3337_;
v___y_3217_ = v_a_3336_;
v___y_3218_ = v___y_3312_;
v___y_3219_ = v___x_3342_;
goto v___jp_3208_;
}
}
else
{
lean_object* v_a_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3350_; 
lean_dec(v___y_3313_);
lean_dec(v___y_3312_);
lean_dec(v___y_3310_);
lean_dec_ref(v___y_3308_);
lean_dec_ref(v___y_3307_);
lean_dec(v___y_3305_);
lean_dec(v___y_3303_);
lean_dec(v___y_3300_);
lean_dec_ref(v___x_2903_);
lean_dec(v___x_2900_);
lean_dec(v___x_2899_);
lean_dec(v___x_2897_);
lean_dec_ref(v___x_2896_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___x_2894_);
lean_dec(v_tk_2893_);
v_a_3343_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3350_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3345_ = v___x_3335_;
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_a_3343_);
lean_dec(v___x_3335_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3348_; 
if (v_isShared_3346_ == 0)
{
v___x_3348_ = v___x_3345_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_a_3343_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
}
}
}
else
{
lean_dec(v___x_2900_);
if (v_useReducible_2901_ == 0)
{
lean_dec(v___x_2899_);
if (lean_obj_tag(v___y_3303_) == 0)
{
lean_dec(v___y_3313_);
lean_dec(v___y_3310_);
lean_dec(v___y_3305_);
lean_dec(v___y_3300_);
lean_dec_ref(v___x_2903_);
lean_dec_ref(v___f_2902_);
lean_dec(v___x_2897_);
lean_dec_ref(v___x_2896_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___x_2894_);
v___y_2962_ = v___y_3307_;
v___y_2963_ = v___y_3299_;
v___y_2964_ = v___y_3304_;
v___y_2965_ = v___y_3311_;
v___y_2966_ = v___y_3309_;
v___y_2967_ = v___y_3302_;
v___y_2968_ = v___y_3301_;
v___y_2969_ = v___y_3308_;
v___y_2970_ = v___y_3312_;
goto v___jp_2961_;
}
else
{
lean_object* v_val_3351_; lean_object* v___x_3352_; 
v_val_3351_ = lean_ctor_get(v___y_3303_, 0);
lean_inc(v_val_3351_);
lean_dec_ref_known(v___y_3303_, 1);
lean_inc(v___y_3312_);
lean_inc_ref(v___y_3308_);
v___x_3352_ = lean_apply_9(v___f_2902_, v___y_3299_, v___y_3304_, v___y_3311_, v___y_3309_, v___y_3302_, v___y_3301_, v___y_3308_, v___y_3312_, lean_box(0));
if (lean_obj_tag(v___x_3352_) == 0)
{
lean_object* v_a_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; 
v_a_3353_ = lean_ctor_get(v___x_3352_, 0);
lean_inc_n(v_a_3353_, 5);
lean_dec_ref_known(v___x_3352_, 1);
v___x_3354_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__7));
lean_inc_ref_n(v___x_2896_, 2);
lean_inc_ref_n(v___x_2895_, 2);
lean_inc_ref_n(v___x_2894_, 2);
v___x_3355_ = l_Lean_Name_mkStr4(v___x_2894_, v___x_2895_, v___x_2896_, v___x_3354_);
v___x_3356_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3356_, 0, v_a_3353_);
lean_ctor_set(v___x_3356_, 1, v___x_2903_);
v___x_3357_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3357_, 0, v_a_3353_);
lean_ctor_set(v___x_3357_, 1, v___x_2991_);
lean_ctor_set(v___x_3357_, 2, v___x_2992_);
v___x_3358_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__9));
v___x_3359_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3359_, 0, v_a_3353_);
lean_ctor_set(v___x_3359_, 1, v___x_3358_);
v___x_3360_ = l_Lean_Syntax_node1(v_a_3353_, v___x_2991_, v___x_3359_);
v___x_3361_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__8));
v___x_3362_ = l_Lean_Name_mkStr4(v___x_2894_, v___x_2895_, v___x_2896_, v___x_3361_);
if (lean_obj_tag(v___y_3313_) == 0)
{
lean_object* v___x_3363_; 
v___x_3363_ = lean_mk_empty_array_with_capacity(v___x_2897_);
v___y_3125_ = v___y_3300_;
v___y_3126_ = v___x_3357_;
v___y_3127_ = v___x_3356_;
v___y_3128_ = v___y_3305_;
v___y_3129_ = v___x_3360_;
v___y_3130_ = v_a_3353_;
v___y_3131_ = v___y_3307_;
v___y_3132_ = v___x_3362_;
v___y_3133_ = v___y_3308_;
v___y_3134_ = v___y_3310_;
v___y_3135_ = v___x_3355_;
v___y_3136_ = v_val_3351_;
v___y_3137_ = v___y_3312_;
v___y_3138_ = v___x_3363_;
goto v___jp_3124_;
}
else
{
lean_object* v_val_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; 
v_val_3364_ = lean_ctor_get(v___y_3313_, 0);
lean_inc(v_val_3364_);
lean_dec_ref_known(v___y_3313_, 1);
v___x_3365_ = lean_mk_empty_array_with_capacity(v___x_2897_);
v___x_3366_ = lean_array_push(v___x_3365_, v_val_3364_);
v___y_3125_ = v___y_3300_;
v___y_3126_ = v___x_3357_;
v___y_3127_ = v___x_3356_;
v___y_3128_ = v___y_3305_;
v___y_3129_ = v___x_3360_;
v___y_3130_ = v_a_3353_;
v___y_3131_ = v___y_3307_;
v___y_3132_ = v___x_3362_;
v___y_3133_ = v___y_3308_;
v___y_3134_ = v___y_3310_;
v___y_3135_ = v___x_3355_;
v___y_3136_ = v_val_3351_;
v___y_3137_ = v___y_3312_;
v___y_3138_ = v___x_3366_;
goto v___jp_3124_;
}
}
else
{
lean_object* v_a_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3374_; 
lean_dec(v_val_3351_);
lean_dec(v___y_3313_);
lean_dec(v___y_3312_);
lean_dec(v___y_3310_);
lean_dec_ref(v___y_3308_);
lean_dec_ref(v___y_3307_);
lean_dec(v___y_3305_);
lean_dec(v___y_3300_);
lean_dec_ref(v___x_2903_);
lean_dec(v___x_2897_);
lean_dec_ref(v___x_2896_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___x_2894_);
lean_dec(v_tk_2893_);
v_a_3367_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3369_ = v___x_3352_;
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_a_3367_);
lean_dec(v___x_3352_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v___x_3372_; 
if (v_isShared_3370_ == 0)
{
v___x_3372_ = v___x_3369_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_a_3367_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
}
}
}
else
{
lean_object* v___x_3375_; 
lean_dec_ref(v___x_2903_);
lean_inc(v___y_3312_);
lean_inc_ref(v___y_3308_);
v___x_3375_ = lean_apply_9(v___f_2902_, v___y_3299_, v___y_3304_, v___y_3311_, v___y_3309_, v___y_3302_, v___y_3301_, v___y_3308_, v___y_3312_, lean_box(0));
if (lean_obj_tag(v___x_3375_) == 0)
{
lean_object* v_a_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; 
v_a_3376_ = lean_ctor_get(v___x_3375_, 0);
lean_inc_n(v_a_3376_, 2);
lean_dec_ref_known(v___x_3375_, 1);
v___x_3377_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__10));
lean_inc_ref(v___x_2896_);
lean_inc_ref(v___x_2895_);
lean_inc_ref(v___x_2894_);
v___x_3378_ = l_Lean_Name_mkStr4(v___x_2894_, v___x_2895_, v___x_2896_, v___x_3377_);
v___x_3379_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__11));
v___x_3380_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3380_, 0, v_a_3376_);
lean_ctor_set(v___x_3380_, 1, v___x_3379_);
if (lean_obj_tag(v___y_3313_) == 0)
{
lean_object* v___x_3381_; 
v___x_3381_ = lean_mk_empty_array_with_capacity(v___x_2897_);
v___y_3055_ = v___x_3378_;
v___y_3056_ = v_a_3376_;
v___y_3057_ = v___y_3307_;
v___y_3058_ = v___y_3300_;
v___y_3059_ = v___y_3303_;
v___y_3060_ = v___y_3308_;
v___y_3061_ = v___y_3310_;
v___y_3062_ = v___x_3380_;
v___y_3063_ = v___y_3305_;
v___y_3064_ = v___y_3312_;
v___y_3065_ = v___x_3381_;
goto v___jp_3054_;
}
else
{
lean_object* v_val_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; 
v_val_3382_ = lean_ctor_get(v___y_3313_, 0);
lean_inc(v_val_3382_);
lean_dec_ref_known(v___y_3313_, 1);
v___x_3383_ = lean_mk_empty_array_with_capacity(v___x_2897_);
v___x_3384_ = lean_array_push(v___x_3383_, v_val_3382_);
v___y_3055_ = v___x_3378_;
v___y_3056_ = v_a_3376_;
v___y_3057_ = v___y_3307_;
v___y_3058_ = v___y_3300_;
v___y_3059_ = v___y_3303_;
v___y_3060_ = v___y_3308_;
v___y_3061_ = v___y_3310_;
v___y_3062_ = v___x_3380_;
v___y_3063_ = v___y_3305_;
v___y_3064_ = v___y_3312_;
v___y_3065_ = v___x_3384_;
goto v___jp_3054_;
}
}
else
{
lean_object* v_a_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3392_; 
lean_dec(v___y_3313_);
lean_dec(v___y_3312_);
lean_dec(v___y_3310_);
lean_dec_ref(v___y_3308_);
lean_dec_ref(v___y_3307_);
lean_dec(v___y_3305_);
lean_dec(v___y_3303_);
lean_dec(v___y_3300_);
lean_dec(v___x_2899_);
lean_dec(v___x_2897_);
lean_dec_ref(v___x_2896_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___x_2894_);
lean_dec(v_tk_2893_);
v_a_3385_ = lean_ctor_get(v___x_3375_, 0);
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3375_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3387_ = v___x_3375_;
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_a_3385_);
lean_dec(v___x_3375_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v___x_3390_; 
if (v_isShared_3388_ == 0)
{
v___x_3390_ = v___x_3387_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v_a_3385_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
return v___x_3390_;
}
}
}
}
}
}
v___jp_3393_:
{
lean_object* v___x_3410_; lean_object* v___x_3411_; uint8_t v___x_3412_; 
v___x_3410_ = lean_unsigned_to_nat(5u);
v___x_3411_ = l_Lean_Syntax_getArg(v___y_3400_, v___x_3410_);
lean_dec(v___y_3400_);
v___x_3412_ = l_Lean_Syntax_matchesNull(v___x_3411_, v___x_2897_);
if (v___x_3412_ == 0)
{
lean_object* v___x_3413_; lean_object* v___x_3414_; 
lean_dec(v_args_3401_);
lean_dec(v___y_3398_);
lean_dec(v___y_3397_);
lean_dec(v___y_3396_);
lean_dec(v___y_3395_);
lean_dec_ref(v___x_2903_);
lean_dec_ref(v___f_2902_);
lean_dec(v___x_2900_);
lean_dec(v___x_2899_);
lean_dec(v___x_2897_);
lean_dec_ref(v___x_2896_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___x_2894_);
v___x_3413_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3414_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3413_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_);
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
lean_dec(v___y_3405_);
lean_dec_ref(v___y_3404_);
lean_dec(v___y_3403_);
lean_dec_ref(v___y_3402_);
if (lean_obj_tag(v___x_3414_) == 0)
{
lean_object* v_a_3415_; 
v_a_3415_ = lean_ctor_get(v___x_3414_, 0);
lean_inc(v_a_3415_);
lean_dec_ref_known(v___x_3414_, 1);
v___y_2956_ = v___y_3394_;
v_stx_2957_ = v_a_3415_;
v___y_2958_ = v___y_3408_;
v___y_2959_ = v___y_3409_;
goto v___jp_2955_;
}
else
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3423_; 
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec_ref(v___y_3394_);
lean_dec(v_tk_2893_);
v_a_3416_ = lean_ctor_get(v___x_3414_, 0);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3418_ = v___x_3414_;
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3414_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3421_; 
if (v_isShared_3419_ == 0)
{
v___x_3421_ = v___x_3418_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_a_3416_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
}
}
else
{
lean_object* v___x_3424_; 
v___x_3424_ = l_Lean_Syntax_getOptional_x3f(v___y_3395_);
lean_dec(v___y_3395_);
if (lean_obj_tag(v___x_3424_) == 0)
{
lean_object* v___x_3425_; 
v___x_3425_ = lean_box(0);
v___y_3299_ = v___y_3402_;
v___y_3300_ = v_args_3401_;
v___y_3301_ = v___y_3407_;
v___y_3302_ = v___y_3406_;
v___y_3303_ = v___y_3396_;
v___y_3304_ = v___y_3403_;
v___y_3305_ = v___y_3398_;
v___y_3306_ = v___y_3399_;
v___y_3307_ = v___y_3394_;
v___y_3308_ = v___y_3408_;
v___y_3309_ = v___y_3405_;
v___y_3310_ = v___y_3397_;
v___y_3311_ = v___y_3404_;
v___y_3312_ = v___y_3409_;
v___y_3313_ = v___x_3425_;
goto v___jp_3298_;
}
else
{
lean_object* v_val_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3433_; 
v_val_3426_ = lean_ctor_get(v___x_3424_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3428_ = v___x_3424_;
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_val_3426_);
lean_dec(v___x_3424_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v___x_3431_; 
if (v_isShared_3429_ == 0)
{
v___x_3431_ = v___x_3428_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_val_3426_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
v___y_3299_ = v___y_3402_;
v___y_3300_ = v_args_3401_;
v___y_3301_ = v___y_3407_;
v___y_3302_ = v___y_3406_;
v___y_3303_ = v___y_3396_;
v___y_3304_ = v___y_3403_;
v___y_3305_ = v___y_3398_;
v___y_3306_ = v___y_3399_;
v___y_3307_ = v___y_3394_;
v___y_3308_ = v___y_3408_;
v___y_3309_ = v___y_3405_;
v___y_3310_ = v___y_3397_;
v___y_3311_ = v___y_3404_;
v___y_3312_ = v___y_3409_;
v___y_3313_ = v___x_3431_;
goto v___jp_3298_;
}
}
}
}
}
v___jp_3434_:
{
lean_object* v___x_3450_; uint8_t v___x_3451_; 
v___x_3450_ = l_Lean_Syntax_getArg(v___y_3440_, v___x_2904_);
v___x_3451_ = l_Lean_Syntax_isNone(v___x_3450_);
if (v___x_3451_ == 0)
{
uint8_t v___x_3452_; 
lean_inc(v___x_3450_);
v___x_3452_ = l_Lean_Syntax_matchesNull(v___x_3450_, v___x_2905_);
if (v___x_3452_ == 0)
{
lean_object* v___x_3453_; lean_object* v___x_3454_; 
lean_dec(v___x_3450_);
lean_dec(v_only_3441_);
lean_dec(v___y_3440_);
lean_dec(v___y_3438_);
lean_dec(v___y_3437_);
lean_dec(v___y_3436_);
lean_dec(v___x_2906_);
lean_dec_ref(v___x_2903_);
lean_dec_ref(v___f_2902_);
lean_dec(v___x_2900_);
lean_dec(v___x_2899_);
lean_dec(v___x_2897_);
lean_dec_ref(v___x_2896_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___x_2894_);
v___x_3453_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3454_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3453_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_);
lean_dec(v___y_3447_);
lean_dec_ref(v___y_3446_);
lean_dec(v___y_3445_);
lean_dec_ref(v___y_3444_);
lean_dec(v___y_3443_);
lean_dec_ref(v___y_3442_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v_a_3455_; 
v_a_3455_ = lean_ctor_get(v___x_3454_, 0);
lean_inc(v_a_3455_);
lean_dec_ref_known(v___x_3454_, 1);
v___y_2956_ = v___y_3435_;
v_stx_2957_ = v_a_3455_;
v___y_2958_ = v___y_3448_;
v___y_2959_ = v___y_3449_;
goto v___jp_2955_;
}
else
{
lean_object* v_a_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3463_; 
lean_dec(v___y_3449_);
lean_dec_ref(v___y_3448_);
lean_dec_ref(v___y_3435_);
lean_dec(v_tk_2893_);
v_a_3456_ = lean_ctor_get(v___x_3454_, 0);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3458_ = v___x_3454_;
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_a_3456_);
lean_dec(v___x_3454_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3461_; 
if (v_isShared_3459_ == 0)
{
v___x_3461_ = v___x_3458_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_a_3456_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
return v___x_3461_;
}
}
}
}
else
{
lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; 
v___x_3464_ = l_Lean_Syntax_getArg(v___x_3450_, v___x_2906_);
lean_dec(v___x_2906_);
lean_dec(v___x_3450_);
v___x_3465_ = l_Lean_Syntax_getArgs(v___x_3464_);
lean_dec(v___x_3464_);
v___x_3466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3465_);
v___y_3394_ = v___y_3435_;
v___y_3395_ = v___y_3436_;
v___y_3396_ = v___y_3437_;
v___y_3397_ = v___y_3438_;
v___y_3398_ = v_only_3441_;
v___y_3399_ = v___y_3439_;
v___y_3400_ = v___y_3440_;
v_args_3401_ = v___x_3466_;
v___y_3402_ = v___y_3442_;
v___y_3403_ = v___y_3443_;
v___y_3404_ = v___y_3444_;
v___y_3405_ = v___y_3445_;
v___y_3406_ = v___y_3446_;
v___y_3407_ = v___y_3447_;
v___y_3408_ = v___y_3448_;
v___y_3409_ = v___y_3449_;
goto v___jp_3393_;
}
}
else
{
lean_object* v___x_3467_; 
lean_dec(v___x_3450_);
lean_dec(v___x_2906_);
v___x_3467_ = lean_box(0);
v___y_3394_ = v___y_3435_;
v___y_3395_ = v___y_3436_;
v___y_3396_ = v___y_3437_;
v___y_3397_ = v___y_3438_;
v___y_3398_ = v_only_3441_;
v___y_3399_ = v___y_3439_;
v___y_3400_ = v___y_3440_;
v_args_3401_ = v___x_3467_;
v___y_3402_ = v___y_3442_;
v___y_3403_ = v___y_3443_;
v___y_3404_ = v___y_3444_;
v___y_3405_ = v___y_3445_;
v___y_3406_ = v___y_3446_;
v___y_3407_ = v___y_3447_;
v___y_3408_ = v___y_3448_;
v___y_3409_ = v___y_3449_;
goto v___jp_3393_;
}
}
v___jp_3468_:
{
lean_object* v_usedTheorems_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; 
v_usedTheorems_3473_ = lean_ctor_get(v___y_3469_, 0);
v___x_3474_ = l_Lean_Syntax_unsetTrailing(v___y_3471_);
v___x_3475_ = l_Lean_Elab_Tactic_mkSimpOnly(v___x_3474_, v_usedTheorems_3473_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
if (lean_obj_tag(v___x_3475_) == 0)
{
lean_object* v_a_3476_; uint8_t v___x_3477_; 
v_a_3476_ = lean_ctor_get(v___x_3475_, 0);
lean_inc_n(v_a_3476_, 2);
lean_dec_ref_known(v___x_3475_, 1);
v___x_3477_ = l_Lean_Syntax_isOfKind(v_a_3476_, v___x_2989_);
lean_dec(v___x_2989_);
if (v___x_3477_ == 0)
{
lean_object* v___x_3478_; lean_object* v___x_3479_; 
lean_inc(v_ref_2985_);
lean_dec(v_a_3476_);
lean_dec(v___y_3472_);
lean_dec(v___x_2908_);
lean_dec(v___x_2906_);
lean_dec_ref(v___x_2903_);
lean_dec_ref(v___f_2902_);
lean_dec(v___x_2900_);
lean_dec(v___x_2899_);
lean_dec(v___x_2897_);
lean_dec_ref(v___x_2896_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___x_2894_);
v___x_3478_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3479_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3478_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec(v___y_2920_);
lean_dec_ref(v___y_2919_);
if (lean_obj_tag(v___x_3479_) == 0)
{
lean_object* v_a_3480_; 
v_a_3480_ = lean_ctor_get(v___x_3479_, 0);
lean_inc(v_a_3480_);
lean_dec_ref_known(v___x_3479_, 1);
v___y_2933_ = v___y_3469_;
v_stx_2934_ = v_a_3480_;
v___y_2935_ = v___y_2925_;
v_ref_2936_ = v_ref_2985_;
v___y_2937_ = v___y_2926_;
goto v___jp_2932_;
}
else
{
lean_object* v_a_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3488_; 
lean_dec_ref(v___y_3469_);
lean_dec(v_ref_2985_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v_tk_2893_);
v_a_3481_ = lean_ctor_get(v___x_3479_, 0);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3479_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3483_ = v___x_3479_;
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_a_3481_);
lean_dec(v___x_3479_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v___x_3486_; 
if (v_isShared_3484_ == 0)
{
v___x_3486_ = v___x_3483_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_a_3481_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
return v___x_3486_;
}
}
}
}
else
{
lean_object* v___x_3489_; uint8_t v___x_3490_; 
v___x_3489_ = l_Lean_Syntax_getArg(v_a_3476_, v___x_2906_);
lean_inc(v___x_3489_);
v___x_3490_ = l_Lean_Syntax_isOfKind(v___x_3489_, v___x_2907_);
if (v___x_3490_ == 0)
{
lean_object* v___x_3491_; lean_object* v___x_3492_; 
lean_inc(v_ref_2985_);
lean_dec(v___x_3489_);
lean_dec(v_a_3476_);
lean_dec(v___y_3472_);
lean_dec(v___x_2908_);
lean_dec(v___x_2906_);
lean_dec_ref(v___x_2903_);
lean_dec_ref(v___f_2902_);
lean_dec(v___x_2900_);
lean_dec(v___x_2899_);
lean_dec(v___x_2897_);
lean_dec_ref(v___x_2896_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___x_2894_);
v___x_3491_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3492_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3491_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec(v___y_2920_);
lean_dec_ref(v___y_2919_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v_a_3493_; 
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
lean_inc(v_a_3493_);
lean_dec_ref_known(v___x_3492_, 1);
v___y_2933_ = v___y_3469_;
v_stx_2934_ = v_a_3493_;
v___y_2935_ = v___y_2925_;
v_ref_2936_ = v_ref_2985_;
v___y_2937_ = v___y_2926_;
goto v___jp_2932_;
}
else
{
lean_object* v_a_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3501_; 
lean_dec_ref(v___y_3469_);
lean_dec(v_ref_2985_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v_tk_2893_);
v_a_3494_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3501_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3496_ = v___x_3492_;
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_a_3494_);
lean_dec(v___x_3492_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3499_; 
if (v_isShared_3497_ == 0)
{
v___x_3499_ = v___x_3496_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v_a_3494_);
v___x_3499_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
return v___x_3499_;
}
}
}
}
else
{
lean_object* v___x_3502_; lean_object* v___x_3503_; uint8_t v___x_3504_; 
v___x_3502_ = l_Lean_Syntax_getArg(v_a_3476_, v___x_2908_);
lean_dec(v___x_2908_);
v___x_3503_ = l_Lean_Syntax_getArg(v_a_3476_, v___x_2905_);
v___x_3504_ = l_Lean_Syntax_isNone(v___x_3503_);
if (v___x_3504_ == 0)
{
uint8_t v___x_3505_; 
lean_inc(v___x_3503_);
v___x_3505_ = l_Lean_Syntax_matchesNull(v___x_3503_, v___x_2906_);
if (v___x_3505_ == 0)
{
lean_object* v___x_3506_; lean_object* v___x_3507_; 
lean_inc(v_ref_2985_);
lean_dec(v___x_3503_);
lean_dec(v___x_3502_);
lean_dec(v___x_3489_);
lean_dec(v_a_3476_);
lean_dec(v___y_3472_);
lean_dec(v___x_2906_);
lean_dec_ref(v___x_2903_);
lean_dec_ref(v___f_2902_);
lean_dec(v___x_2900_);
lean_dec(v___x_2899_);
lean_dec(v___x_2897_);
lean_dec_ref(v___x_2896_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___x_2894_);
v___x_3506_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3507_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3506_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec(v___y_2920_);
lean_dec_ref(v___y_2919_);
if (lean_obj_tag(v___x_3507_) == 0)
{
lean_object* v_a_3508_; 
v_a_3508_ = lean_ctor_get(v___x_3507_, 0);
lean_inc(v_a_3508_);
lean_dec_ref_known(v___x_3507_, 1);
v___y_2933_ = v___y_3469_;
v_stx_2934_ = v_a_3508_;
v___y_2935_ = v___y_2925_;
v_ref_2936_ = v_ref_2985_;
v___y_2937_ = v___y_2926_;
goto v___jp_2932_;
}
else
{
lean_object* v_a_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3516_; 
lean_dec_ref(v___y_3469_);
lean_dec(v_ref_2985_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v_tk_2893_);
v_a_3509_ = lean_ctor_get(v___x_3507_, 0);
v_isSharedCheck_3516_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3516_ == 0)
{
v___x_3511_ = v___x_3507_;
v_isShared_3512_ = v_isSharedCheck_3516_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_a_3509_);
lean_dec(v___x_3507_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3516_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v___x_3514_; 
if (v_isShared_3512_ == 0)
{
v___x_3514_ = v___x_3511_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v_a_3509_);
v___x_3514_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
return v___x_3514_;
}
}
}
}
else
{
lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3517_ = l_Lean_Syntax_getArg(v___x_3503_, v___x_2897_);
lean_dec(v___x_3503_);
v___x_3518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3517_);
v___y_3435_ = v___y_3469_;
v___y_3436_ = v___x_3502_;
v___y_3437_ = v___y_3472_;
v___y_3438_ = v___x_3489_;
v___y_3439_ = v___y_3470_;
v___y_3440_ = v_a_3476_;
v_only_3441_ = v___x_3518_;
v___y_3442_ = v___y_2919_;
v___y_3443_ = v___y_2920_;
v___y_3444_ = v___y_2921_;
v___y_3445_ = v___y_2922_;
v___y_3446_ = v___y_2923_;
v___y_3447_ = v___y_2924_;
v___y_3448_ = v___y_2925_;
v___y_3449_ = v___y_2926_;
goto v___jp_3434_;
}
}
else
{
lean_object* v___x_3519_; 
lean_dec(v___x_3503_);
v___x_3519_ = lean_box(0);
v___y_3435_ = v___y_3469_;
v___y_3436_ = v___x_3502_;
v___y_3437_ = v___y_3472_;
v___y_3438_ = v___x_3489_;
v___y_3439_ = v___y_3470_;
v___y_3440_ = v_a_3476_;
v_only_3441_ = v___x_3519_;
v___y_3442_ = v___y_2919_;
v___y_3443_ = v___y_2920_;
v___y_3444_ = v___y_2921_;
v___y_3445_ = v___y_2922_;
v___y_3446_ = v___y_2923_;
v___y_3447_ = v___y_2924_;
v___y_3448_ = v___y_2925_;
v___y_3449_ = v___y_2926_;
goto v___jp_3434_;
}
}
}
}
else
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3527_; 
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3469_);
lean_dec(v___x_2989_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec(v___y_2920_);
lean_dec_ref(v___y_2919_);
lean_dec(v___x_2908_);
lean_dec(v___x_2906_);
lean_dec_ref(v___x_2903_);
lean_dec_ref(v___f_2902_);
lean_dec(v___x_2900_);
lean_dec(v___x_2899_);
lean_dec(v___x_2897_);
lean_dec_ref(v___x_2896_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___x_2894_);
lean_dec(v_tk_2893_);
v_a_3520_ = lean_ctor_get(v___x_3475_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3475_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3522_ = v___x_3475_;
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3475_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3525_; 
if (v_isShared_3523_ == 0)
{
v___x_3525_ = v___x_3522_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_a_3520_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
}
v___jp_3528_:
{
if (lean_obj_tag(v_usingArg_2909_) == 0)
{
v___y_3469_ = v___y_3529_;
v___y_3470_ = v___y_3531_;
v___y_3471_ = v___y_3530_;
v___y_3472_ = v_usingArg_2909_;
goto v___jp_3468_;
}
else
{
lean_object* v_val_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3540_; 
v_val_3532_ = lean_ctor_get(v_usingArg_2909_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v_usingArg_2909_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3534_ = v_usingArg_2909_;
v_isShared_3535_ = v_isSharedCheck_3540_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_val_3532_);
lean_dec(v_usingArg_2909_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3540_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v___x_3536_; lean_object* v___x_3538_; 
v___x_3536_ = l_Lean_Syntax_unsetTrailing(v_val_3532_);
if (v_isShared_3535_ == 0)
{
lean_ctor_set(v___x_3534_, 0, v___x_3536_);
v___x_3538_ = v___x_3534_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v___x_3536_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
v___y_3469_ = v___y_3529_;
v___y_3470_ = v___y_3531_;
v___y_3471_ = v___y_3530_;
v___y_3472_ = v___x_3538_;
goto v___jp_3468_;
}
}
}
}
v___jp_3541_:
{
if (v___y_3545_ == 0)
{
lean_dec(v___y_3544_);
lean_dec(v___x_2989_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec(v___y_2920_);
lean_dec_ref(v___y_2919_);
lean_dec(v_usingArg_2909_);
lean_dec(v___x_2908_);
lean_dec(v___x_2906_);
lean_dec_ref(v___x_2903_);
lean_dec_ref(v___f_2902_);
lean_dec(v___x_2900_);
lean_dec(v___x_2899_);
lean_dec(v___x_2897_);
lean_dec_ref(v___x_2896_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___x_2894_);
lean_dec(v_tk_2893_);
v___y_2929_ = v___y_3542_;
goto v___jp_2928_;
}
else
{
v___y_3529_ = v___y_3542_;
v___y_3530_ = v___y_3544_;
v___y_3531_ = v___y_3543_;
goto v___jp_3528_;
}
}
v___jp_3546_:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___f_3557_; lean_object* v___x_3558_; 
v___x_3552_ = l_Lean_Meta_Simp_Context_setFailIfUnchanged(v___y_3551_, v___x_2986_);
v___x_3553_ = lean_box(v___x_2898_);
v___x_3554_ = lean_box(v___x_2986_);
v___x_3555_ = lean_box(v_useReducible_2901_);
v___x_3556_ = lean_box(v___x_2911_);
lean_inc_ref(v___x_2896_);
lean_inc_ref(v___x_2895_);
lean_inc_ref(v___x_2894_);
lean_inc_ref(v___f_2902_);
lean_inc(v___x_2906_);
lean_inc_ref(v___x_2903_);
lean_inc(v_usingArg_2909_);
lean_inc(v___x_2897_);
lean_inc(v_tk_2893_);
lean_inc(v___x_2908_);
v___f_3557_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___boxed), 30, 20);
lean_closure_set(v___f_3557_, 0, v___x_2908_);
lean_closure_set(v___f_3557_, 1, v_tk_2893_);
lean_closure_set(v___f_3557_, 2, v___x_2991_);
lean_closure_set(v___f_3557_, 3, v___x_2897_);
lean_closure_set(v___f_3557_, 4, v___x_3552_);
lean_closure_set(v___f_3557_, 5, v___y_3547_);
lean_closure_set(v___f_3557_, 6, v___x_3553_);
lean_closure_set(v___f_3557_, 7, v_usingArg_2909_);
lean_closure_set(v___f_3557_, 8, v___x_3554_);
lean_closure_set(v___f_3557_, 9, v___x_2903_);
lean_closure_set(v___f_3557_, 10, v___x_3555_);
lean_closure_set(v___f_3557_, 11, v___x_3556_);
lean_closure_set(v___f_3557_, 12, v___x_2906_);
lean_closure_set(v___f_3557_, 13, v___f_2902_);
lean_closure_set(v___f_3557_, 14, v___x_2894_);
lean_closure_set(v___f_3557_, 15, v___x_2895_);
lean_closure_set(v___f_3557_, 16, v___x_2896_);
lean_closure_set(v___f_3557_, 17, v___f_2912_);
lean_closure_set(v___f_3557_, 18, v_a_2983_);
lean_closure_set(v___f_3557_, 19, v_usingTk_x3f_2913_);
v___x_3558_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v___y_3548_, v___f_3557_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
lean_dec(v___y_3548_);
if (lean_obj_tag(v___x_3558_) == 0)
{
lean_object* v_a_3559_; lean_object* v_options_3560_; lean_object* v___x_3561_; uint8_t v___x_3562_; 
v_a_3559_ = lean_ctor_get(v___x_3558_, 0);
lean_inc(v_a_3559_);
lean_dec_ref_known(v___x_3558_, 1);
v_options_3560_ = lean_ctor_get(v_toCold_2984_, 2);
v___x_3561_ = l_Lean_Elab_Tactic_tactic_simp_trace;
v___x_3562_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__3(v_options_3560_, v___x_3561_);
if (v___x_3562_ == 0)
{
if (lean_obj_tag(v_squeeze_2914_) == 0)
{
v___y_3542_ = v_a_3559_;
v___y_3543_ = v___y_3550_;
v___y_3544_ = v___y_3549_;
v___y_3545_ = v___x_3562_;
goto v___jp_3541_;
}
else
{
v___y_3542_ = v_a_3559_;
v___y_3543_ = v___y_3550_;
v___y_3544_ = v___y_3549_;
v___y_3545_ = v___x_2911_;
goto v___jp_3541_;
}
}
else
{
v___y_3529_ = v_a_3559_;
v___y_3530_ = v___y_3549_;
v___y_3531_ = v___y_3550_;
goto v___jp_3528_;
}
}
else
{
lean_object* v_a_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3570_; 
lean_dec(v___y_3549_);
lean_dec(v___x_2989_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec(v___y_2920_);
lean_dec_ref(v___y_2919_);
lean_dec(v_usingArg_2909_);
lean_dec(v___x_2908_);
lean_dec(v___x_2906_);
lean_dec_ref(v___x_2903_);
lean_dec_ref(v___f_2902_);
lean_dec(v___x_2900_);
lean_dec(v___x_2899_);
lean_dec(v___x_2897_);
lean_dec_ref(v___x_2896_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___x_2894_);
lean_dec(v_tk_2893_);
v_a_3563_ = lean_ctor_get(v___x_3558_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3565_ = v___x_3558_;
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_a_3563_);
lean_dec(v___x_3558_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3568_; 
if (v_isShared_3566_ == 0)
{
v___x_3568_ = v___x_3565_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_a_3563_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
}
}
v___jp_3571_:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; uint8_t v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; 
v___x_3575_ = l_Array_append___redArg(v___x_2992_, v___y_3574_);
lean_dec_ref(v___y_3574_);
lean_inc_n(v___x_2987_, 2);
v___x_3576_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3576_, 0, v___x_2987_);
lean_ctor_set(v___x_3576_, 1, v___x_2991_);
lean_ctor_set(v___x_3576_, 2, v___x_3575_);
v___x_3577_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3577_, 0, v___x_2987_);
lean_ctor_set(v___x_3577_, 1, v___x_2991_);
lean_ctor_set(v___x_3577_, 2, v___x_2992_);
lean_inc(v___x_2989_);
v___x_3578_ = l_Lean_Syntax_node6(v___x_2987_, v___x_2989_, v___x_2990_, v___x_2910_, v___y_3573_, v___y_3572_, v___x_3576_, v___x_3577_);
v___x_3579_ = 0;
v___x_3580_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__13));
v___x_3581_ = lean_box(v___x_2986_);
v___x_3582_ = lean_box(v___x_3579_);
v___x_3583_ = lean_box(v___x_2986_);
lean_inc(v___x_3578_);
v___x_3584_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_3584_, 0, v___x_3578_);
lean_closure_set(v___x_3584_, 1, v___x_3581_);
lean_closure_set(v___x_3584_, 2, v___x_3582_);
lean_closure_set(v___x_3584_, 3, v___x_3583_);
lean_closure_set(v___x_3584_, 4, v___x_3580_);
v___x_3585_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_3584_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
if (lean_obj_tag(v___x_3585_) == 0)
{
lean_object* v_a_3586_; 
v_a_3586_ = lean_ctor_get(v___x_3585_, 0);
lean_inc(v_a_3586_);
lean_dec_ref_known(v___x_3585_, 1);
if (lean_obj_tag(v_unfold_2915_) == 0)
{
lean_object* v_ctx_3587_; lean_object* v_simprocs_3588_; lean_object* v_dischargeWrapper_3589_; 
v_ctx_3587_ = lean_ctor_get(v_a_3586_, 0);
lean_inc_ref(v_ctx_3587_);
v_simprocs_3588_ = lean_ctor_get(v_a_3586_, 1);
lean_inc_ref(v_simprocs_3588_);
v_dischargeWrapper_3589_ = lean_ctor_get(v_a_3586_, 2);
lean_inc(v_dischargeWrapper_3589_);
lean_dec(v_a_3586_);
v___y_3547_ = v_simprocs_3588_;
v___y_3548_ = v_dischargeWrapper_3589_;
v___y_3549_ = v___x_3578_;
v___y_3550_ = v___x_2986_;
v___y_3551_ = v_ctx_3587_;
goto v___jp_3546_;
}
else
{
if (v___x_2911_ == 0)
{
lean_object* v_ctx_3590_; lean_object* v_simprocs_3591_; lean_object* v_dischargeWrapper_3592_; 
v_ctx_3590_ = lean_ctor_get(v_a_3586_, 0);
lean_inc_ref(v_ctx_3590_);
v_simprocs_3591_ = lean_ctor_get(v_a_3586_, 1);
lean_inc_ref(v_simprocs_3591_);
v_dischargeWrapper_3592_ = lean_ctor_get(v_a_3586_, 2);
lean_inc(v_dischargeWrapper_3592_);
lean_dec(v_a_3586_);
v___y_3547_ = v_simprocs_3591_;
v___y_3548_ = v_dischargeWrapper_3592_;
v___y_3549_ = v___x_3578_;
v___y_3550_ = v___x_2911_;
v___y_3551_ = v_ctx_3590_;
goto v___jp_3546_;
}
else
{
lean_object* v_ctx_3593_; lean_object* v_simprocs_3594_; lean_object* v_dischargeWrapper_3595_; lean_object* v___x_3596_; 
v_ctx_3593_ = lean_ctor_get(v_a_3586_, 0);
lean_inc_ref(v_ctx_3593_);
v_simprocs_3594_ = lean_ctor_get(v_a_3586_, 1);
lean_inc_ref(v_simprocs_3594_);
v_dischargeWrapper_3595_ = lean_ctor_get(v_a_3586_, 2);
lean_inc(v_dischargeWrapper_3595_);
lean_dec(v_a_3586_);
v___x_3596_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_3593_);
v___y_3547_ = v_simprocs_3594_;
v___y_3548_ = v_dischargeWrapper_3595_;
v___y_3549_ = v___x_3578_;
v___y_3550_ = v___x_2911_;
v___y_3551_ = v___x_3596_;
goto v___jp_3546_;
}
}
}
else
{
lean_object* v_a_3597_; lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3604_; 
lean_dec(v___x_3578_);
lean_dec(v___x_2989_);
lean_dec(v_a_2983_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec(v___y_2920_);
lean_dec_ref(v___y_2919_);
lean_dec(v_usingTk_x3f_2913_);
lean_dec_ref(v___f_2912_);
lean_dec(v_usingArg_2909_);
lean_dec(v___x_2908_);
lean_dec(v___x_2906_);
lean_dec_ref(v___x_2903_);
lean_dec_ref(v___f_2902_);
lean_dec(v___x_2900_);
lean_dec(v___x_2899_);
lean_dec(v___x_2897_);
lean_dec_ref(v___x_2896_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___x_2894_);
lean_dec(v_tk_2893_);
v_a_3597_ = lean_ctor_get(v___x_3585_, 0);
v_isSharedCheck_3604_ = !lean_is_exclusive(v___x_3585_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3599_ = v___x_3585_;
v_isShared_3600_ = v_isSharedCheck_3604_;
goto v_resetjp_3598_;
}
else
{
lean_inc(v_a_3597_);
lean_dec(v___x_3585_);
v___x_3599_ = lean_box(0);
v_isShared_3600_ = v_isSharedCheck_3604_;
goto v_resetjp_3598_;
}
v_resetjp_3598_:
{
lean_object* v___x_3602_; 
if (v_isShared_3600_ == 0)
{
v___x_3602_ = v___x_3599_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v_a_3597_);
v___x_3602_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
return v___x_3602_;
}
}
}
}
v___jp_3605_:
{
lean_object* v___x_3608_; lean_object* v___x_3609_; 
v___x_3608_ = l_Array_append___redArg(v___x_2992_, v___y_3607_);
lean_dec_ref(v___y_3607_);
lean_inc(v___x_2987_);
v___x_3609_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3609_, 0, v___x_2987_);
lean_ctor_set(v___x_3609_, 1, v___x_2991_);
lean_ctor_set(v___x_3609_, 2, v___x_3608_);
if (lean_obj_tag(v_args_2916_) == 1)
{
lean_object* v_val_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; 
v_val_3610_ = lean_ctor_get(v_args_2916_, 0);
v___x_3611_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___x_2987_, 3);
v___x_3612_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3612_, 0, v___x_2987_);
lean_ctor_set(v___x_3612_, 1, v___x_3611_);
v___x_3613_ = l_Array_append___redArg(v___x_2992_, v_val_3610_);
v___x_3614_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3614_, 0, v___x_2987_);
lean_ctor_set(v___x_3614_, 1, v___x_2991_);
lean_ctor_set(v___x_3614_, 2, v___x_3613_);
v___x_3615_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_3616_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3616_, 0, v___x_2987_);
lean_ctor_set(v___x_3616_, 1, v___x_3615_);
v___x_3617_ = l_Array_mkArray3___redArg(v___x_3612_, v___x_3614_, v___x_3616_);
v___y_3572_ = v___x_3609_;
v___y_3573_ = v___y_3606_;
v___y_3574_ = v___x_3617_;
goto v___jp_3571_;
}
else
{
lean_object* v___x_3618_; 
v___x_3618_ = lean_mk_empty_array_with_capacity(v___x_2897_);
v___y_3572_ = v___x_3609_;
v___y_3573_ = v___y_3606_;
v___y_3574_ = v___x_3618_;
goto v___jp_3571_;
}
}
v___jp_3619_:
{
lean_object* v___x_3621_; lean_object* v___x_3622_; 
v___x_3621_ = l_Array_append___redArg(v___x_2992_, v___y_3620_);
lean_dec_ref(v___y_3620_);
lean_inc(v___x_2987_);
v___x_3622_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3622_, 0, v___x_2987_);
lean_ctor_set(v___x_3622_, 1, v___x_2991_);
lean_ctor_set(v___x_3622_, 2, v___x_3621_);
if (lean_obj_tag(v_only_2917_) == 1)
{
lean_object* v_val_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; 
v_val_3623_ = lean_ctor_get(v_only_2917_, 0);
v___x_3624_ = l_Lean_SourceInfo_fromRef(v_val_3623_, v___x_2898_);
v___x_3625_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_3626_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3626_, 0, v___x_3624_);
lean_ctor_set(v___x_3626_, 1, v___x_3625_);
v___x_3627_ = l_Array_mkArray1___redArg(v___x_3626_);
v___y_3606_ = v___x_3622_;
v___y_3607_ = v___x_3627_;
goto v___jp_3605_;
}
else
{
lean_object* v___x_3628_; 
v___x_3628_ = lean_mk_empty_array_with_capacity(v___x_2897_);
v___y_3606_ = v___x_3622_;
v___y_3607_ = v___x_3628_;
goto v___jp_3605_;
}
}
}
else
{
lean_object* v_a_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3640_; 
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec(v___y_2920_);
lean_dec_ref(v___y_2919_);
lean_dec(v___y_2918_);
lean_dec(v_usingTk_x3f_2913_);
lean_dec_ref(v___f_2912_);
lean_dec(v___x_2910_);
lean_dec(v_usingArg_2909_);
lean_dec(v___x_2908_);
lean_dec(v___x_2906_);
lean_dec_ref(v___x_2903_);
lean_dec_ref(v___f_2902_);
lean_dec(v___x_2900_);
lean_dec(v___x_2899_);
lean_dec(v___x_2897_);
lean_dec_ref(v___x_2896_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___x_2894_);
lean_dec(v_tk_2893_);
v_a_3633_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3635_ = v___x_2982_;
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_a_3633_);
lean_dec(v___x_2982_);
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
v___jp_2928_:
{
lean_object* v_diag_2930_; lean_object* v___x_2931_; 
v_diag_2930_ = lean_ctor_get(v___y_2929_, 1);
lean_inc_ref(v_diag_2930_);
lean_dec_ref(v___y_2929_);
v___x_2931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2931_, 0, v_diag_2930_);
return v___x_2931_;
}
v___jp_2932_:
{
lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; uint8_t v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2938_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__3));
v___x_2939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2939_, 0, v___x_2938_);
lean_ctor_set(v___x_2939_, 1, v_stx_2934_);
v___x_2940_ = lean_box(0);
v___x_2941_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2939_);
lean_ctor_set(v___x_2941_, 1, v___x_2940_);
lean_ctor_set(v___x_2941_, 2, v___x_2940_);
lean_ctor_set(v___x_2941_, 3, v___x_2940_);
lean_ctor_set(v___x_2941_, 4, v___x_2940_);
lean_ctor_set(v___x_2941_, 5, v___x_2940_);
v___x_2942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2942_, 0, v_ref_2936_);
v___x_2943_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__0));
v___x_2944_ = 4;
v___x_2945_ = l_Lean_MessageData_nil;
v___x_2946_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_2893_, v___x_2941_, v___x_2942_, v___x_2943_, v___x_2940_, v___x_2944_, v___x_2945_, v___y_2935_, v___y_2937_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2935_);
if (lean_obj_tag(v___x_2946_) == 0)
{
lean_dec_ref_known(v___x_2946_, 1);
v___y_2929_ = v___y_2933_;
goto v___jp_2928_;
}
else
{
lean_object* v_a_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2954_; 
lean_dec_ref(v___y_2933_);
v_a_2947_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2949_ = v___x_2946_;
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_a_2947_);
lean_dec(v___x_2946_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2952_; 
if (v_isShared_2950_ == 0)
{
v___x_2952_ = v___x_2949_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_a_2947_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
return v___x_2952_;
}
}
}
}
v___jp_2955_:
{
lean_object* v_ref_2960_; 
v_ref_2960_ = lean_ctor_get(v___y_2958_, 2);
lean_inc(v_ref_2960_);
v___y_2933_ = v___y_2956_;
v_stx_2934_ = v_stx_2957_;
v___y_2935_ = v___y_2958_;
v_ref_2936_ = v_ref_2960_;
v___y_2937_ = v___y_2959_;
goto v___jp_2932_;
}
v___jp_2961_:
{
lean_object* v___x_2971_; lean_object* v___x_2972_; 
v___x_2971_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__4, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__4_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__4);
v___x_2972_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_2971_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v___y_2964_);
lean_dec_ref(v___y_2963_);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_object* v_a_2973_; 
v_a_2973_ = lean_ctor_get(v___x_2972_, 0);
lean_inc(v_a_2973_);
lean_dec_ref_known(v___x_2972_, 1);
v___y_2956_ = v___y_2962_;
v_stx_2957_ = v_a_2973_;
v___y_2958_ = v___y_2969_;
v___y_2959_ = v___y_2970_;
goto v___jp_2955_;
}
else
{
lean_object* v_a_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2981_; 
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec_ref(v___y_2962_);
lean_dec(v_tk_2893_);
v_a_2974_ = lean_ctor_get(v___x_2972_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2976_ = v___x_2972_;
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_a_2974_);
lean_dec(v___x_2972_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2979_; 
if (v_isShared_2977_ == 0)
{
v___x_2979_ = v___x_2976_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_a_2974_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
return v___x_2979_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___boxed(lean_object** _args){
lean_object* v_tk_3641_ = _args[0];
lean_object* v___x_3642_ = _args[1];
lean_object* v___x_3643_ = _args[2];
lean_object* v___x_3644_ = _args[3];
lean_object* v___x_3645_ = _args[4];
lean_object* v___x_3646_ = _args[5];
lean_object* v___x_3647_ = _args[6];
lean_object* v___x_3648_ = _args[7];
lean_object* v_useReducible_3649_ = _args[8];
lean_object* v___f_3650_ = _args[9];
lean_object* v___x_3651_ = _args[10];
lean_object* v___x_3652_ = _args[11];
lean_object* v___x_3653_ = _args[12];
lean_object* v___x_3654_ = _args[13];
lean_object* v___x_3655_ = _args[14];
lean_object* v___x_3656_ = _args[15];
lean_object* v_usingArg_3657_ = _args[16];
lean_object* v___x_3658_ = _args[17];
lean_object* v___x_3659_ = _args[18];
lean_object* v___f_3660_ = _args[19];
lean_object* v_usingTk_x3f_3661_ = _args[20];
lean_object* v_squeeze_3662_ = _args[21];
lean_object* v_unfold_3663_ = _args[22];
lean_object* v_args_3664_ = _args[23];
lean_object* v_only_3665_ = _args[24];
lean_object* v___y_3666_ = _args[25];
lean_object* v___y_3667_ = _args[26];
lean_object* v___y_3668_ = _args[27];
lean_object* v___y_3669_ = _args[28];
lean_object* v___y_3670_ = _args[29];
lean_object* v___y_3671_ = _args[30];
lean_object* v___y_3672_ = _args[31];
lean_object* v___y_3673_ = _args[32];
lean_object* v___y_3674_ = _args[33];
lean_object* v___y_3675_ = _args[34];
_start:
{
uint8_t v___x_96706__boxed_3676_; uint8_t v_useReducible_boxed_3677_; uint8_t v___x_96717__boxed_3678_; lean_object* v_res_3679_; 
v___x_96706__boxed_3676_ = lean_unbox(v___x_3646_);
v_useReducible_boxed_3677_ = lean_unbox(v_useReducible_3649_);
v___x_96717__boxed_3678_ = lean_unbox(v___x_3659_);
v_res_3679_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7(v_tk_3641_, v___x_3642_, v___x_3643_, v___x_3644_, v___x_3645_, v___x_96706__boxed_3676_, v___x_3647_, v___x_3648_, v_useReducible_boxed_3677_, v___f_3650_, v___x_3651_, v___x_3652_, v___x_3653_, v___x_3654_, v___x_3655_, v___x_3656_, v_usingArg_3657_, v___x_3658_, v___x_96717__boxed_3678_, v___f_3660_, v_usingTk_x3f_3661_, v_squeeze_3662_, v_unfold_3663_, v_args_3664_, v_only_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_);
lean_dec(v_only_3665_);
lean_dec(v_args_3664_);
lean_dec(v_unfold_3663_);
lean_dec(v_squeeze_3662_);
lean_dec(v___x_3655_);
lean_dec(v___x_3653_);
lean_dec(v___x_3652_);
return v_res_3679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(uint8_t v_useReducible_3705_, lean_object* v_stx_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_, lean_object* v_a_3714_){
_start:
{
lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; uint8_t v___x_3721_; 
v___x_3716_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4_));
v___x_3717_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0));
v___x_3718_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__1));
v___x_3719_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1));
v___x_3720_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
lean_inc(v_stx_3706_);
v___x_3721_ = l_Lean_Syntax_isOfKind(v_stx_3706_, v___x_3720_);
if (v___x_3721_ == 0)
{
lean_object* v___x_3722_; 
lean_dec(v_stx_3706_);
v___x_3722_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3722_;
}
else
{
lean_object* v___f_3723_; lean_object* v___x_3724_; lean_object* v_tk_3725_; lean_object* v___x_3726_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v___y_3732_; lean_object* v___y_3733_; lean_object* v___y_3734_; lean_object* v___y_3735_; uint8_t v___y_3736_; lean_object* v___y_3737_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v___y_3746_; lean_object* v___y_3747_; lean_object* v___y_3748_; lean_object* v___y_3749_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3767_; uint8_t v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v___y_3779_; lean_object* v_usingTk_x3f_3780_; lean_object* v_usingArg_3781_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3795_; lean_object* v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; uint8_t v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v_args_3813_; lean_object* v___y_3825_; uint8_t v___y_3826_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3829_; lean_object* v___y_3830_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v_only_3837_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3864_; lean_object* v___y_3865_; lean_object* v___y_3866_; lean_object* v___y_3867_; lean_object* v___y_3868_; lean_object* v_unfold_3869_; lean_object* v_squeeze_3888_; lean_object* v___y_3889_; lean_object* v___y_3890_; lean_object* v___y_3891_; lean_object* v___y_3892_; lean_object* v___y_3893_; lean_object* v___y_3894_; lean_object* v___y_3895_; lean_object* v___y_3896_; lean_object* v___x_3905_; uint8_t v___x_3906_; 
v___f_3723_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3));
v___x_3724_ = lean_unsigned_to_nat(0u);
v_tk_3725_ = l_Lean_Syntax_getArg(v_stx_3706_, v___x_3724_);
v___x_3726_ = lean_unsigned_to_nat(1u);
v___x_3905_ = l_Lean_Syntax_getArg(v_stx_3706_, v___x_3726_);
v___x_3906_ = l_Lean_Syntax_isNone(v___x_3905_);
if (v___x_3906_ == 0)
{
uint8_t v___x_3907_; 
lean_inc(v___x_3905_);
v___x_3907_ = l_Lean_Syntax_matchesNull(v___x_3905_, v___x_3726_);
if (v___x_3907_ == 0)
{
lean_object* v___x_3908_; 
lean_dec(v___x_3905_);
lean_dec(v_tk_3725_);
lean_dec(v_stx_3706_);
v___x_3908_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3908_;
}
else
{
lean_object* v_squeeze_3909_; lean_object* v___x_3910_; 
v_squeeze_3909_ = l_Lean_Syntax_getArg(v___x_3905_, v___x_3724_);
lean_dec(v___x_3905_);
v___x_3910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3910_, 0, v_squeeze_3909_);
v_squeeze_3888_ = v___x_3910_;
v___y_3889_ = v_a_3707_;
v___y_3890_ = v_a_3708_;
v___y_3891_ = v_a_3709_;
v___y_3892_ = v_a_3710_;
v___y_3893_ = v_a_3711_;
v___y_3894_ = v_a_3712_;
v___y_3895_ = v_a_3713_;
v___y_3896_ = v_a_3714_;
goto v___jp_3887_;
}
}
else
{
lean_object* v___x_3911_; 
lean_dec(v___x_3905_);
v___x_3911_ = lean_box(0);
v_squeeze_3888_ = v___x_3911_;
v___y_3889_ = v_a_3707_;
v___y_3890_ = v_a_3708_;
v___y_3891_ = v_a_3709_;
v___y_3892_ = v_a_3710_;
v___y_3893_ = v_a_3711_;
v___y_3894_ = v_a_3712_;
v___y_3895_ = v_a_3713_;
v___y_3896_ = v_a_3714_;
goto v___jp_3887_;
}
v___jp_3727_:
{
lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___f_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___f_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; 
v___x_3750_ = lean_box(v___x_3721_);
v___x_3751_ = lean_box(v___y_3736_);
lean_inc(v___y_3744_);
lean_inc(v___y_3746_);
lean_inc(v___y_3749_);
lean_inc(v___y_3748_);
lean_inc(v___y_3731_);
lean_inc(v___y_3735_);
v___f_3752_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___boxed), 22, 12);
lean_closure_set(v___f_3752_, 0, v___y_3735_);
lean_closure_set(v___f_3752_, 1, v___x_3724_);
lean_closure_set(v___f_3752_, 2, v___y_3731_);
lean_closure_set(v___f_3752_, 3, v___y_3748_);
lean_closure_set(v___f_3752_, 4, v___x_3750_);
lean_closure_set(v___f_3752_, 5, v___x_3716_);
lean_closure_set(v___f_3752_, 6, v___x_3717_);
lean_closure_set(v___f_3752_, 7, v___x_3718_);
lean_closure_set(v___f_3752_, 8, v___y_3749_);
lean_closure_set(v___f_3752_, 9, v___y_3746_);
lean_closure_set(v___f_3752_, 10, v___x_3751_);
lean_closure_set(v___f_3752_, 11, v___y_3744_);
v___x_3753_ = lean_box(v___x_3721_);
v___x_3754_ = lean_box(v_useReducible_3705_);
v___x_3755_ = lean_box(v___y_3736_);
lean_inc(v___y_3732_);
lean_inc(v___y_3740_);
v___f_3756_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___boxed), 35, 26);
lean_closure_set(v___f_3756_, 0, v_tk_3725_);
lean_closure_set(v___f_3756_, 1, v___x_3716_);
lean_closure_set(v___f_3756_, 2, v___x_3717_);
lean_closure_set(v___f_3756_, 3, v___x_3718_);
lean_closure_set(v___f_3756_, 4, v___x_3724_);
lean_closure_set(v___f_3756_, 5, v___x_3753_);
lean_closure_set(v___f_3756_, 6, v___y_3740_);
lean_closure_set(v___f_3756_, 7, v___x_3720_);
lean_closure_set(v___f_3756_, 8, v___x_3754_);
lean_closure_set(v___f_3756_, 9, v___f_3723_);
lean_closure_set(v___f_3756_, 10, v___x_3719_);
lean_closure_set(v___f_3756_, 11, v___y_3745_);
lean_closure_set(v___f_3756_, 12, v___y_3743_);
lean_closure_set(v___f_3756_, 13, v___x_3726_);
lean_closure_set(v___f_3756_, 14, v___y_3732_);
lean_closure_set(v___f_3756_, 15, v___y_3729_);
lean_closure_set(v___f_3756_, 16, v___y_3733_);
lean_closure_set(v___f_3756_, 17, v___y_3735_);
lean_closure_set(v___f_3756_, 18, v___x_3755_);
lean_closure_set(v___f_3756_, 19, v___f_3752_);
lean_closure_set(v___f_3756_, 20, v___y_3737_);
lean_closure_set(v___f_3756_, 21, v___y_3744_);
lean_closure_set(v___f_3756_, 22, v___y_3746_);
lean_closure_set(v___f_3756_, 23, v___y_3731_);
lean_closure_set(v___f_3756_, 24, v___y_3748_);
lean_closure_set(v___f_3756_, 25, v___y_3749_);
v___x_3757_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_3757_, 0, v___f_3756_);
v___x_3758_ = l_Lean_Elab_Tactic_focus___redArg(v___x_3757_, v___y_3742_, v___y_3747_, v___y_3738_, v___y_3741_, v___y_3739_, v___y_3730_, v___y_3728_, v___y_3734_);
return v___x_3758_;
}
v___jp_3759_:
{
lean_object* v___x_3782_; 
v___x_3782_ = l_Lean_Syntax_getOptional_x3f(v___y_3765_);
lean_dec(v___y_3765_);
if (lean_obj_tag(v___x_3782_) == 0)
{
lean_object* v___x_3783_; 
v___x_3783_ = lean_box(0);
v___y_3728_ = v___y_3760_;
v___y_3729_ = v___y_3761_;
v___y_3730_ = v___y_3762_;
v___y_3731_ = v___y_3763_;
v___y_3732_ = v___y_3764_;
v___y_3733_ = v_usingArg_3781_;
v___y_3734_ = v___y_3766_;
v___y_3735_ = v___y_3767_;
v___y_3736_ = v___y_3768_;
v___y_3737_ = v_usingTk_x3f_3780_;
v___y_3738_ = v___y_3769_;
v___y_3739_ = v___y_3770_;
v___y_3740_ = v___y_3771_;
v___y_3741_ = v___y_3772_;
v___y_3742_ = v___y_3773_;
v___y_3743_ = v___y_3774_;
v___y_3744_ = v___y_3776_;
v___y_3745_ = v___y_3775_;
v___y_3746_ = v___y_3777_;
v___y_3747_ = v___y_3778_;
v___y_3748_ = v___y_3779_;
v___y_3749_ = v___x_3783_;
goto v___jp_3727_;
}
else
{
lean_object* v_val_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3791_; 
v_val_3784_ = lean_ctor_get(v___x_3782_, 0);
v_isSharedCheck_3791_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3791_ == 0)
{
v___x_3786_ = v___x_3782_;
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_val_3784_);
lean_dec(v___x_3782_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
lean_object* v___x_3789_; 
if (v_isShared_3787_ == 0)
{
v___x_3789_ = v___x_3786_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v_val_3784_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
v___y_3728_ = v___y_3760_;
v___y_3729_ = v___y_3761_;
v___y_3730_ = v___y_3762_;
v___y_3731_ = v___y_3763_;
v___y_3732_ = v___y_3764_;
v___y_3733_ = v_usingArg_3781_;
v___y_3734_ = v___y_3766_;
v___y_3735_ = v___y_3767_;
v___y_3736_ = v___y_3768_;
v___y_3737_ = v_usingTk_x3f_3780_;
v___y_3738_ = v___y_3769_;
v___y_3739_ = v___y_3770_;
v___y_3740_ = v___y_3771_;
v___y_3741_ = v___y_3772_;
v___y_3742_ = v___y_3773_;
v___y_3743_ = v___y_3774_;
v___y_3744_ = v___y_3776_;
v___y_3745_ = v___y_3775_;
v___y_3746_ = v___y_3777_;
v___y_3747_ = v___y_3778_;
v___y_3748_ = v___y_3779_;
v___y_3749_ = v___x_3789_;
goto v___jp_3727_;
}
}
}
}
v___jp_3792_:
{
lean_object* v___x_3814_; lean_object* v___x_3815_; uint8_t v___x_3816_; 
v___x_3814_ = lean_unsigned_to_nat(4u);
v___x_3815_ = l_Lean_Syntax_getArg(v___y_3794_, v___x_3814_);
lean_dec(v___y_3794_);
v___x_3816_ = l_Lean_Syntax_isNone(v___x_3815_);
if (v___x_3816_ == 0)
{
uint8_t v___x_3817_; 
lean_inc(v___x_3815_);
v___x_3817_ = l_Lean_Syntax_matchesNull(v___x_3815_, v___y_3796_);
lean_dec(v___y_3796_);
if (v___x_3817_ == 0)
{
lean_object* v___x_3818_; 
lean_dec(v___x_3815_);
lean_dec(v_args_3813_);
lean_dec(v___y_3812_);
lean_dec(v___y_3810_);
lean_dec(v___y_3809_);
lean_dec(v___y_3808_);
lean_dec(v___y_3801_);
lean_dec(v___y_3799_);
lean_dec(v___y_3795_);
lean_dec(v_tk_3725_);
v___x_3818_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3818_;
}
else
{
lean_object* v_usingTk_x3f_3819_; lean_object* v_usingArg_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; 
v_usingTk_x3f_3819_ = l_Lean_Syntax_getArg(v___x_3815_, v___x_3724_);
v_usingArg_3820_ = l_Lean_Syntax_getArg(v___x_3815_, v___x_3726_);
lean_dec(v___x_3815_);
v___x_3821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3821_, 0, v_usingTk_x3f_3819_);
v___x_3822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3822_, 0, v_usingArg_3820_);
v___y_3760_ = v___y_3793_;
v___y_3761_ = v___y_3795_;
v___y_3762_ = v___y_3797_;
v___y_3763_ = v_args_3813_;
v___y_3764_ = v___y_3798_;
v___y_3765_ = v___y_3799_;
v___y_3766_ = v___y_3800_;
v___y_3767_ = v___y_3801_;
v___y_3768_ = v___y_3802_;
v___y_3769_ = v___y_3803_;
v___y_3770_ = v___y_3804_;
v___y_3771_ = v___y_3805_;
v___y_3772_ = v___y_3806_;
v___y_3773_ = v___y_3807_;
v___y_3774_ = v___y_3808_;
v___y_3775_ = v___x_3814_;
v___y_3776_ = v___y_3809_;
v___y_3777_ = v___y_3810_;
v___y_3778_ = v___y_3811_;
v___y_3779_ = v___y_3812_;
v_usingTk_x3f_3780_ = v___x_3821_;
v_usingArg_3781_ = v___x_3822_;
goto v___jp_3759_;
}
}
else
{
lean_object* v___x_3823_; 
lean_dec(v___x_3815_);
lean_dec(v___y_3796_);
v___x_3823_ = lean_box(0);
v___y_3760_ = v___y_3793_;
v___y_3761_ = v___y_3795_;
v___y_3762_ = v___y_3797_;
v___y_3763_ = v_args_3813_;
v___y_3764_ = v___y_3798_;
v___y_3765_ = v___y_3799_;
v___y_3766_ = v___y_3800_;
v___y_3767_ = v___y_3801_;
v___y_3768_ = v___y_3802_;
v___y_3769_ = v___y_3803_;
v___y_3770_ = v___y_3804_;
v___y_3771_ = v___y_3805_;
v___y_3772_ = v___y_3806_;
v___y_3773_ = v___y_3807_;
v___y_3774_ = v___y_3808_;
v___y_3775_ = v___x_3814_;
v___y_3776_ = v___y_3809_;
v___y_3777_ = v___y_3810_;
v___y_3778_ = v___y_3811_;
v___y_3779_ = v___y_3812_;
v_usingTk_x3f_3780_ = v___x_3823_;
v_usingArg_3781_ = v___x_3823_;
goto v___jp_3759_;
}
}
v___jp_3824_:
{
lean_object* v___x_3846_; uint8_t v___x_3847_; 
v___x_3846_ = l_Lean_Syntax_getArg(v___y_3834_, v___y_3835_);
lean_dec(v___y_3835_);
v___x_3847_ = l_Lean_Syntax_isNone(v___x_3846_);
if (v___x_3847_ == 0)
{
uint8_t v___x_3848_; 
lean_inc(v___x_3846_);
v___x_3848_ = l_Lean_Syntax_matchesNull(v___x_3846_, v___x_3726_);
if (v___x_3848_ == 0)
{
lean_object* v___x_3849_; 
lean_dec(v___x_3846_);
lean_dec(v_only_3837_);
lean_dec(v___y_3836_);
lean_dec(v___y_3834_);
lean_dec(v___y_3833_);
lean_dec(v___y_3831_);
lean_dec(v___y_3830_);
lean_dec(v___y_3829_);
lean_dec(v___y_3828_);
lean_dec(v___y_3825_);
lean_dec(v_tk_3725_);
v___x_3849_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3849_;
}
else
{
lean_object* v___x_3850_; lean_object* v___x_3851_; uint8_t v___x_3852_; 
v___x_3850_ = l_Lean_Syntax_getArg(v___x_3846_, v___x_3724_);
lean_dec(v___x_3846_);
v___x_3851_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
lean_inc(v___x_3850_);
v___x_3852_ = l_Lean_Syntax_isOfKind(v___x_3850_, v___x_3851_);
if (v___x_3852_ == 0)
{
lean_object* v___x_3853_; 
lean_dec(v___x_3850_);
lean_dec(v_only_3837_);
lean_dec(v___y_3836_);
lean_dec(v___y_3834_);
lean_dec(v___y_3833_);
lean_dec(v___y_3831_);
lean_dec(v___y_3830_);
lean_dec(v___y_3829_);
lean_dec(v___y_3828_);
lean_dec(v___y_3825_);
lean_dec(v_tk_3725_);
v___x_3853_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3853_;
}
else
{
lean_object* v___x_3854_; lean_object* v_args_3855_; lean_object* v___x_3856_; 
v___x_3854_ = l_Lean_Syntax_getArg(v___x_3850_, v___x_3726_);
lean_dec(v___x_3850_);
v_args_3855_ = l_Lean_Syntax_getArgs(v___x_3854_);
lean_dec(v___x_3854_);
v___x_3856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3856_, 0, v_args_3855_);
v___y_3793_ = v___y_3844_;
v___y_3794_ = v___y_3834_;
v___y_3795_ = v___y_3831_;
v___y_3796_ = v___y_3836_;
v___y_3797_ = v___y_3843_;
v___y_3798_ = v___y_3832_;
v___y_3799_ = v___y_3833_;
v___y_3800_ = v___y_3845_;
v___y_3801_ = v___y_3825_;
v___y_3802_ = v___y_3826_;
v___y_3803_ = v___y_3840_;
v___y_3804_ = v___y_3842_;
v___y_3805_ = v___y_3827_;
v___y_3806_ = v___y_3841_;
v___y_3807_ = v___y_3838_;
v___y_3808_ = v___y_3828_;
v___y_3809_ = v___y_3829_;
v___y_3810_ = v___y_3830_;
v___y_3811_ = v___y_3839_;
v___y_3812_ = v_only_3837_;
v_args_3813_ = v___x_3856_;
goto v___jp_3792_;
}
}
}
else
{
lean_object* v___x_3857_; 
lean_dec(v___x_3846_);
v___x_3857_ = lean_box(0);
v___y_3793_ = v___y_3844_;
v___y_3794_ = v___y_3834_;
v___y_3795_ = v___y_3831_;
v___y_3796_ = v___y_3836_;
v___y_3797_ = v___y_3843_;
v___y_3798_ = v___y_3832_;
v___y_3799_ = v___y_3833_;
v___y_3800_ = v___y_3845_;
v___y_3801_ = v___y_3825_;
v___y_3802_ = v___y_3826_;
v___y_3803_ = v___y_3840_;
v___y_3804_ = v___y_3842_;
v___y_3805_ = v___y_3827_;
v___y_3806_ = v___y_3841_;
v___y_3807_ = v___y_3838_;
v___y_3808_ = v___y_3828_;
v___y_3809_ = v___y_3829_;
v___y_3810_ = v___y_3830_;
v___y_3811_ = v___y_3839_;
v___y_3812_ = v_only_3837_;
v_args_3813_ = v___x_3857_;
goto v___jp_3792_;
}
}
v___jp_3858_:
{
lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; uint8_t v___x_3873_; 
v___x_3870_ = lean_unsigned_to_nat(3u);
v___x_3871_ = l_Lean_Syntax_getArg(v_stx_3706_, v___x_3870_);
lean_dec(v_stx_3706_);
v___x_3872_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6));
lean_inc(v___x_3871_);
v___x_3873_ = l_Lean_Syntax_isOfKind(v___x_3871_, v___x_3872_);
if (v___x_3873_ == 0)
{
lean_object* v___x_3874_; 
lean_dec(v___x_3871_);
lean_dec(v_unfold_3869_);
lean_dec(v___y_3866_);
lean_dec(v___y_3865_);
lean_dec(v_tk_3725_);
v___x_3874_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3874_;
}
else
{
lean_object* v___x_3875_; lean_object* v___x_3876_; uint8_t v___x_3877_; 
v___x_3875_ = l_Lean_Syntax_getArg(v___x_3871_, v___x_3724_);
v___x_3876_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8));
lean_inc(v___x_3875_);
v___x_3877_ = l_Lean_Syntax_isOfKind(v___x_3875_, v___x_3876_);
if (v___x_3877_ == 0)
{
lean_object* v___x_3878_; 
lean_dec(v___x_3875_);
lean_dec(v___x_3871_);
lean_dec(v_unfold_3869_);
lean_dec(v___y_3866_);
lean_dec(v___y_3865_);
lean_dec(v_tk_3725_);
v___x_3878_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3878_;
}
else
{
lean_object* v___x_3879_; lean_object* v___x_3880_; uint8_t v___x_3881_; 
v___x_3879_ = l_Lean_Syntax_getArg(v___x_3871_, v___x_3726_);
v___x_3880_ = l_Lean_Syntax_getArg(v___x_3871_, v___y_3866_);
v___x_3881_ = l_Lean_Syntax_isNone(v___x_3880_);
if (v___x_3881_ == 0)
{
uint8_t v___x_3882_; 
lean_inc(v___x_3880_);
v___x_3882_ = l_Lean_Syntax_matchesNull(v___x_3880_, v___x_3726_);
if (v___x_3882_ == 0)
{
lean_object* v___x_3883_; 
lean_dec(v___x_3880_);
lean_dec(v___x_3879_);
lean_dec(v___x_3875_);
lean_dec(v___x_3871_);
lean_dec(v_unfold_3869_);
lean_dec(v___y_3866_);
lean_dec(v___y_3865_);
lean_dec(v_tk_3725_);
v___x_3883_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3883_;
}
else
{
lean_object* v_only_3884_; lean_object* v___x_3885_; 
v_only_3884_ = l_Lean_Syntax_getArg(v___x_3880_, v___x_3724_);
lean_dec(v___x_3880_);
v___x_3885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3885_, 0, v_only_3884_);
lean_inc(v___y_3866_);
v___y_3825_ = v___x_3875_;
v___y_3826_ = v___x_3873_;
v___y_3827_ = v___x_3872_;
v___y_3828_ = v___x_3870_;
v___y_3829_ = v___y_3865_;
v___y_3830_ = v_unfold_3869_;
v___y_3831_ = v___y_3866_;
v___y_3832_ = v___x_3876_;
v___y_3833_ = v___x_3879_;
v___y_3834_ = v___x_3871_;
v___y_3835_ = v___x_3870_;
v___y_3836_ = v___y_3866_;
v_only_3837_ = v___x_3885_;
v___y_3838_ = v___y_3863_;
v___y_3839_ = v___y_3859_;
v___y_3840_ = v___y_3862_;
v___y_3841_ = v___y_3864_;
v___y_3842_ = v___y_3861_;
v___y_3843_ = v___y_3860_;
v___y_3844_ = v___y_3868_;
v___y_3845_ = v___y_3867_;
goto v___jp_3824_;
}
}
else
{
lean_object* v___x_3886_; 
lean_dec(v___x_3880_);
v___x_3886_ = lean_box(0);
lean_inc(v___y_3866_);
v___y_3825_ = v___x_3875_;
v___y_3826_ = v___x_3873_;
v___y_3827_ = v___x_3872_;
v___y_3828_ = v___x_3870_;
v___y_3829_ = v___y_3865_;
v___y_3830_ = v_unfold_3869_;
v___y_3831_ = v___y_3866_;
v___y_3832_ = v___x_3876_;
v___y_3833_ = v___x_3879_;
v___y_3834_ = v___x_3871_;
v___y_3835_ = v___x_3870_;
v___y_3836_ = v___y_3866_;
v_only_3837_ = v___x_3886_;
v___y_3838_ = v___y_3863_;
v___y_3839_ = v___y_3859_;
v___y_3840_ = v___y_3862_;
v___y_3841_ = v___y_3864_;
v___y_3842_ = v___y_3861_;
v___y_3843_ = v___y_3860_;
v___y_3844_ = v___y_3868_;
v___y_3845_ = v___y_3867_;
goto v___jp_3824_;
}
}
}
}
v___jp_3887_:
{
lean_object* v___x_3897_; lean_object* v___x_3898_; uint8_t v___x_3899_; 
v___x_3897_ = lean_unsigned_to_nat(2u);
v___x_3898_ = l_Lean_Syntax_getArg(v_stx_3706_, v___x_3897_);
v___x_3899_ = l_Lean_Syntax_isNone(v___x_3898_);
if (v___x_3899_ == 0)
{
uint8_t v___x_3900_; 
lean_inc(v___x_3898_);
v___x_3900_ = l_Lean_Syntax_matchesNull(v___x_3898_, v___x_3726_);
if (v___x_3900_ == 0)
{
lean_object* v___x_3901_; 
lean_dec(v___x_3898_);
lean_dec(v_squeeze_3888_);
lean_dec(v_tk_3725_);
lean_dec(v_stx_3706_);
v___x_3901_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3901_;
}
else
{
lean_object* v_unfold_3902_; lean_object* v___x_3903_; 
v_unfold_3902_ = l_Lean_Syntax_getArg(v___x_3898_, v___x_3724_);
lean_dec(v___x_3898_);
v___x_3903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3903_, 0, v_unfold_3902_);
v___y_3859_ = v___y_3890_;
v___y_3860_ = v___y_3894_;
v___y_3861_ = v___y_3893_;
v___y_3862_ = v___y_3891_;
v___y_3863_ = v___y_3889_;
v___y_3864_ = v___y_3892_;
v___y_3865_ = v_squeeze_3888_;
v___y_3866_ = v___x_3897_;
v___y_3867_ = v___y_3896_;
v___y_3868_ = v___y_3895_;
v_unfold_3869_ = v___x_3903_;
goto v___jp_3858_;
}
}
else
{
lean_object* v___x_3904_; 
lean_dec(v___x_3898_);
v___x_3904_ = lean_box(0);
v___y_3859_ = v___y_3890_;
v___y_3860_ = v___y_3894_;
v___y_3861_ = v___y_3893_;
v___y_3862_ = v___y_3891_;
v___y_3863_ = v___y_3889_;
v___y_3864_ = v___y_3892_;
v___y_3865_ = v_squeeze_3888_;
v___y_3866_ = v___x_3897_;
v___y_3867_ = v___y_3896_;
v___y_3868_ = v___y_3895_;
v_unfold_3869_ = v___x_3904_;
goto v___jp_3858_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___boxed(lean_object* v_useReducible_3912_, lean_object* v_stx_3913_, lean_object* v_a_3914_, lean_object* v_a_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_){
_start:
{
uint8_t v_useReducible_boxed_3923_; lean_object* v_res_3924_; 
v_useReducible_boxed_3923_ = lean_unbox(v_useReducible_3912_);
v_res_3924_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v_useReducible_boxed_3923_, v_stx_3913_, v_a_3914_, v_a_3915_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_);
lean_dec(v_a_3921_);
lean_dec_ref(v_a_3920_);
lean_dec(v_a_3919_);
lean_dec_ref(v_a_3918_);
lean_dec(v_a_3917_);
lean_dec_ref(v_a_3916_);
lean_dec(v_a_3915_);
lean_dec_ref(v_a_3914_);
return v_res_3924_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(lean_object* v_mvarId_3925_, lean_object* v_val_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_){
_start:
{
lean_object* v___x_3936_; 
v___x_3936_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(v_mvarId_3925_, v_val_3926_, v___y_3932_);
return v___x_3936_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___boxed(lean_object* v_mvarId_3937_, lean_object* v_val_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_){
_start:
{
lean_object* v_res_3948_; 
v_res_3948_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(v_mvarId_3937_, v_val_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_);
lean_dec(v___y_3946_);
lean_dec_ref(v___y_3945_);
lean_dec(v___y_3944_);
lean_dec_ref(v___y_3943_);
lean_dec(v___y_3942_);
lean_dec_ref(v___y_3941_);
lean_dec(v___y_3940_);
lean_dec_ref(v___y_3939_);
return v_res_3948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5(lean_object* v_o_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
lean_object* v___x_3959_; 
v___x_3959_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(v_o_3949_, v___y_3957_);
return v___x_3959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___boxed(lean_object* v_o_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_){
_start:
{
lean_object* v_res_3970_; 
v_res_3970_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5(v_o_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_);
lean_dec(v___y_3968_);
lean_dec_ref(v___y_3967_);
lean_dec(v___y_3966_);
lean_dec_ref(v___y_3965_);
lean_dec(v___y_3964_);
lean_dec_ref(v___y_3963_);
lean_dec(v___y_3962_);
lean_dec_ref(v___y_3961_);
return v_res_3970_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5(lean_object* v_00_u03b1_3971_, lean_object* v_msg_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_){
_start:
{
lean_object* v___x_3982_; 
v___x_3982_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_msg_3972_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_);
return v___x_3982_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___boxed(lean_object* v_00_u03b1_3983_, lean_object* v_msg_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_){
_start:
{
lean_object* v_res_3994_; 
v_res_3994_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5(v_00_u03b1_3983_, v_msg_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_);
lean_dec(v___y_3992_);
lean_dec_ref(v___y_3991_);
lean_dec(v___y_3990_);
lean_dec_ref(v___y_3989_);
lean_dec(v___y_3988_);
lean_dec_ref(v___y_3987_);
lean_dec(v___y_3986_);
lean_dec_ref(v___y_3985_);
return v_res_3994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7(lean_object* v_00_u03b1_3995_, lean_object* v_x_3996_, lean_object* v_mkInfoTree_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_){
_start:
{
lean_object* v___x_4007_; 
v___x_4007_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v_x_3996_, v_mkInfoTree_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_);
return v___x_4007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___boxed(lean_object* v_00_u03b1_4008_, lean_object* v_x_4009_, lean_object* v_mkInfoTree_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_){
_start:
{
lean_object* v_res_4020_; 
v_res_4020_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7(v_00_u03b1_4008_, v_x_4009_, v_mkInfoTree_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_);
lean_dec(v___y_4018_);
lean_dec_ref(v___y_4017_);
lean_dec(v___y_4016_);
lean_dec_ref(v___y_4015_);
lean_dec(v___y_4014_);
lean_dec_ref(v___y_4013_);
lean_dec(v___y_4012_);
lean_dec_ref(v___y_4011_);
return v_res_4020_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3(lean_object* v_00_u03b2_4021_, lean_object* v_x_4022_, lean_object* v_x_4023_, lean_object* v_x_4024_){
_start:
{
lean_object* v___x_4025_; 
v___x_4025_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(v_x_4022_, v_x_4023_, v_x_4024_);
return v___x_4025_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5(lean_object* v_00_u03b2_4026_, lean_object* v_m_4027_, lean_object* v_a_4028_){
_start:
{
uint8_t v___x_4029_; 
v___x_4029_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(v_m_4027_, v_a_4028_);
return v___x_4029_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___boxed(lean_object* v_00_u03b2_4030_, lean_object* v_m_4031_, lean_object* v_a_4032_){
_start:
{
uint8_t v_res_4033_; lean_object* v_r_4034_; 
v_res_4033_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5(v_00_u03b2_4030_, v_m_4031_, v_a_4032_);
lean_dec_ref(v_a_4032_);
lean_dec_ref(v_m_4031_);
v_r_4034_ = lean_box(v_res_4033_);
return v_r_4034_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6(lean_object* v_00_u03b2_4035_, lean_object* v_m_4036_, lean_object* v_a_4037_, lean_object* v_b_4038_){
_start:
{
lean_object* v___x_4039_; 
v___x_4039_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(v_m_4036_, v_a_4037_, v_b_4038_);
return v___x_4039_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__15(lean_object* v_mvarId_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_){
_start:
{
lean_object* v___x_4051_; 
v___x_4051_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__15___redArg(v_mvarId_4040_, v___y_4041_, v___y_4047_);
return v___x_4051_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__15___boxed(lean_object* v_mvarId_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_){
_start:
{
lean_object* v_res_4063_; 
v_res_4063_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__15(v_mvarId_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_);
lean_dec(v___y_4061_);
lean_dec_ref(v___y_4060_);
lean_dec(v___y_4059_);
lean_dec_ref(v___y_4058_);
lean_dec(v___y_4057_);
lean_dec_ref(v___y_4056_);
lean_dec(v___y_4055_);
lean_dec_ref(v___y_4054_);
lean_dec(v_mvarId_4052_);
return v_res_4063_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16(lean_object* v_mvarId_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_){
_start:
{
lean_object* v___x_4075_; 
v___x_4075_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg(v_mvarId_4064_, v___y_4065_, v___y_4071_);
return v___x_4075_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___boxed(lean_object* v_mvarId_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_){
_start:
{
lean_object* v_res_4087_; 
v_res_4087_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16(v_mvarId_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_);
lean_dec(v___y_4085_);
lean_dec_ref(v___y_4084_);
lean_dec(v___y_4083_);
lean_dec_ref(v___y_4082_);
lean_dec(v___y_4081_);
lean_dec_ref(v___y_4080_);
lean_dec(v___y_4079_);
lean_dec_ref(v___y_4078_);
lean_dec(v_mvarId_4076_);
return v_res_4087_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10(lean_object* v_00_u03b2_4088_, lean_object* v_x_4089_, size_t v_x_4090_, size_t v_x_4091_, lean_object* v_x_4092_, lean_object* v_x_4093_){
_start:
{
lean_object* v___x_4094_; 
v___x_4094_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___redArg(v_x_4089_, v_x_4090_, v_x_4091_, v_x_4092_, v_x_4093_);
return v___x_4094_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___boxed(lean_object* v_00_u03b2_4095_, lean_object* v_x_4096_, lean_object* v_x_4097_, lean_object* v_x_4098_, lean_object* v_x_4099_, lean_object* v_x_4100_){
_start:
{
size_t v_x_98936__boxed_4101_; size_t v_x_98937__boxed_4102_; lean_object* v_res_4103_; 
v_x_98936__boxed_4101_ = lean_unbox_usize(v_x_4097_);
lean_dec(v_x_4097_);
v_x_98937__boxed_4102_ = lean_unbox_usize(v_x_4098_);
lean_dec(v_x_4098_);
v_res_4103_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10(v_00_u03b2_4095_, v_x_4096_, v_x_98936__boxed_4101_, v_x_98937__boxed_4102_, v_x_4099_, v_x_4100_);
return v_res_4103_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11(lean_object* v_00_u03b2_4104_, lean_object* v_a_4105_, lean_object* v_x_4106_){
_start:
{
uint8_t v___x_4107_; 
v___x_4107_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___redArg(v_a_4105_, v_x_4106_);
return v___x_4107_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___boxed(lean_object* v_00_u03b2_4108_, lean_object* v_a_4109_, lean_object* v_x_4110_){
_start:
{
uint8_t v_res_4111_; lean_object* v_r_4112_; 
v_res_4111_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11(v_00_u03b2_4108_, v_a_4109_, v_x_4110_);
lean_dec(v_x_4110_);
lean_dec_ref(v_a_4109_);
v_r_4112_ = lean_box(v_res_4111_);
return v_r_4112_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13(lean_object* v_00_u03b2_4113_, lean_object* v_data_4114_){
_start:
{
lean_object* v___x_4115_; 
v___x_4115_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13___redArg(v_data_4114_);
return v___x_4115_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__19(lean_object* v_00_u03b2_4116_, lean_object* v_n_4117_, lean_object* v_k_4118_, lean_object* v_v_4119_){
_start:
{
lean_object* v___x_4120_; 
v___x_4120_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__19___redArg(v_n_4117_, v_k_4118_, v_v_4119_);
return v___x_4120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__20(lean_object* v_00_u03b2_4121_, size_t v_depth_4122_, lean_object* v_keys_4123_, lean_object* v_vals_4124_, lean_object* v_heq_4125_, lean_object* v_i_4126_, lean_object* v_entries_4127_){
_start:
{
lean_object* v___x_4128_; 
v___x_4128_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__20___redArg(v_depth_4122_, v_keys_4123_, v_vals_4124_, v_i_4126_, v_entries_4127_);
return v___x_4128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__20___boxed(lean_object* v_00_u03b2_4129_, lean_object* v_depth_4130_, lean_object* v_keys_4131_, lean_object* v_vals_4132_, lean_object* v_heq_4133_, lean_object* v_i_4134_, lean_object* v_entries_4135_){
_start:
{
size_t v_depth_boxed_4136_; lean_object* v_res_4137_; 
v_depth_boxed_4136_ = lean_unbox_usize(v_depth_4130_);
lean_dec(v_depth_4130_);
v_res_4137_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__20(v_00_u03b2_4129_, v_depth_boxed_4136_, v_keys_4131_, v_vals_4132_, v_heq_4133_, v_i_4134_, v_entries_4135_);
lean_dec_ref(v_vals_4132_);
lean_dec_ref(v_keys_4131_);
return v_res_4137_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13_spec__15(lean_object* v_00_u03b2_4138_, lean_object* v_i_4139_, lean_object* v_source_4140_, lean_object* v_target_4141_){
_start:
{
lean_object* v___x_4142_; 
v___x_4142_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13_spec__15___redArg(v_i_4139_, v_source_4140_, v_target_4141_);
return v___x_4142_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__19_spec__21(lean_object* v_00_u03b2_4143_, lean_object* v_x_4144_, lean_object* v_x_4145_, lean_object* v_x_4146_, lean_object* v_x_4147_){
_start:
{
lean_object* v___x_4148_; 
v___x_4148_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__19_spec__21___redArg(v_x_4144_, v_x_4145_, v_x_4146_, v_x_4147_);
return v___x_4148_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13_spec__15_spec__20(lean_object* v_00_u03b2_4149_, lean_object* v_x_4150_, lean_object* v_x_4151_){
_start:
{
lean_object* v___x_4152_; 
v___x_4152_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13_spec__15_spec__20___redArg(v_x_4150_, v_x_4151_);
return v___x_4152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa(lean_object* v_a_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_){
_start:
{
uint8_t v___x_4163_; lean_object* v___x_4164_; 
v___x_4163_ = 1;
v___x_4164_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v___x_4163_, v_a_4153_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_);
return v___x_4164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed(lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_){
_start:
{
lean_object* v_res_4175_; 
v_res_4175_ = l_Lean_Elab_Tactic_Simpa_evalSimpa(v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_);
lean_dec(v_a_4173_);
lean_dec_ref(v_a_4172_);
lean_dec(v_a_4171_);
lean_dec_ref(v_a_4170_);
lean_dec(v_a_4169_);
lean_dec_ref(v_a_4168_);
lean_dec(v_a_4167_);
lean_dec_ref(v_a_4166_);
return v_res_4175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1(){
_start:
{
lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; 
v___x_4185_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4186_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
v___x_4187_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2));
v___x_4188_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed), 10, 0);
v___x_4189_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4185_, v___x_4186_, v___x_4187_, v___x_4188_);
return v___x_4189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___boxed(lean_object* v_a_4190_){
_start:
{
lean_object* v_res_4191_; 
v_res_4191_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1();
return v_res_4191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3(){
_start:
{
lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; 
v___x_4218_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2));
v___x_4219_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6));
v___x_4220_ = l_Lean_addBuiltinDeclarationRanges(v___x_4218_, v___x_4219_);
return v___x_4220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___boxed(lean_object* v_a_4221_){
_start:
{
lean_object* v_res_4222_; 
v_res_4222_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3();
return v_res_4222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(lean_object* v_x_4225_){
_start:
{
lean_object* v___x_4226_; 
v___x_4226_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
return v___x_4226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___boxed(lean_object* v_x_4227_){
_start:
{
lean_object* v_res_4228_; 
v_res_4228_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v_x_4227_);
lean_dec(v_x_4227_);
return v_res_4228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang(lean_object* v_stx_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_, lean_object* v_a_4244_, lean_object* v_a_4245_, lean_object* v_a_4246_, lean_object* v_a_4247_, lean_object* v_a_4248_){
_start:
{
lean_object* v___y_4251_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4262_; uint8_t v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v___y_4268_; lean_object* v___y_4269_; lean_object* v___y_4270_; lean_object* v___y_4271_; lean_object* v___y_4272_; lean_object* v___x_4281_; uint8_t v___x_4282_; 
v___x_4281_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0));
lean_inc(v_stx_4240_);
v___x_4282_ = l_Lean_Syntax_isOfKind(v_stx_4240_, v___x_4281_);
if (v___x_4282_ == 0)
{
lean_object* v___x_4283_; 
lean_dec(v_stx_4240_);
v___x_4283_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4283_;
}
else
{
lean_object* v___x_4284_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4290_; lean_object* v___y_4291_; lean_object* v___y_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4297_; lean_object* v___y_4298_; uint8_t v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v___y_4303_; lean_object* v___y_4304_; lean_object* v___y_4305_; lean_object* v___y_4306_; lean_object* v___y_4307_; lean_object* v___y_4322_; lean_object* v___y_4323_; lean_object* v___y_4324_; lean_object* v___y_4325_; lean_object* v___y_4326_; lean_object* v___y_4327_; lean_object* v___y_4328_; lean_object* v___y_4329_; lean_object* v___y_4330_; lean_object* v___y_4331_; lean_object* v___y_4332_; lean_object* v___y_4333_; lean_object* v___y_4334_; uint8_t v___y_4335_; lean_object* v___y_4336_; lean_object* v___y_4337_; lean_object* v___y_4338_; lean_object* v___y_4339_; lean_object* v___y_4340_; lean_object* v___y_4341_; lean_object* v___y_4342_; lean_object* v___y_4343_; lean_object* v___y_4353_; lean_object* v___y_4354_; lean_object* v___y_4355_; lean_object* v___y_4356_; lean_object* v___y_4357_; lean_object* v___y_4358_; lean_object* v___y_4359_; lean_object* v___y_4360_; lean_object* v___y_4361_; lean_object* v___y_4362_; lean_object* v___y_4363_; lean_object* v___y_4364_; uint8_t v___y_4365_; lean_object* v___y_4366_; lean_object* v___y_4367_; lean_object* v___y_4368_; lean_object* v___y_4369_; lean_object* v___y_4370_; lean_object* v___y_4371_; lean_object* v___y_4372_; lean_object* v___y_4373_; lean_object* v___y_4382_; lean_object* v___y_4383_; lean_object* v___y_4384_; lean_object* v___y_4385_; lean_object* v___y_4386_; lean_object* v___y_4387_; lean_object* v___y_4388_; lean_object* v___y_4389_; lean_object* v___y_4390_; lean_object* v___y_4391_; lean_object* v___y_4392_; lean_object* v___y_4393_; uint8_t v___y_4394_; lean_object* v___y_4395_; lean_object* v___y_4396_; lean_object* v___y_4397_; lean_object* v___y_4398_; lean_object* v___y_4399_; lean_object* v___y_4400_; lean_object* v___y_4401_; lean_object* v___y_4402_; lean_object* v_tk_4411_; lean_object* v___y_4413_; lean_object* v___y_4414_; lean_object* v___y_4415_; lean_object* v___y_4416_; lean_object* v___y_4417_; lean_object* v___y_4418_; lean_object* v___y_4419_; lean_object* v___y_4420_; lean_object* v___y_4421_; lean_object* v___y_4422_; lean_object* v___y_4423_; lean_object* v___y_4424_; lean_object* v___y_4425_; lean_object* v___y_4426_; lean_object* v___y_4427_; lean_object* v___y_4444_; lean_object* v___y_4445_; lean_object* v___y_4446_; lean_object* v___y_4447_; lean_object* v___y_4448_; lean_object* v___y_4449_; lean_object* v_args_4450_; lean_object* v___y_4451_; lean_object* v___y_4452_; lean_object* v___y_4453_; lean_object* v___y_4454_; lean_object* v___y_4455_; lean_object* v___y_4456_; lean_object* v___y_4457_; lean_object* v___y_4458_; lean_object* v___x_4471_; lean_object* v___y_4473_; lean_object* v___y_4474_; lean_object* v___y_4475_; lean_object* v___y_4476_; lean_object* v___y_4477_; lean_object* v___y_4478_; lean_object* v_only_4479_; lean_object* v___y_4480_; lean_object* v___y_4481_; lean_object* v___y_4482_; lean_object* v___y_4483_; lean_object* v___y_4484_; lean_object* v___y_4485_; lean_object* v___y_4486_; lean_object* v___y_4487_; lean_object* v___y_4501_; lean_object* v___y_4502_; lean_object* v_unfold_4503_; lean_object* v___y_4504_; lean_object* v___y_4505_; lean_object* v___y_4506_; lean_object* v___y_4507_; lean_object* v___y_4508_; lean_object* v___y_4509_; lean_object* v___y_4510_; lean_object* v___y_4511_; lean_object* v_squeeze_4530_; lean_object* v___y_4531_; lean_object* v___y_4532_; lean_object* v___y_4533_; lean_object* v___y_4534_; lean_object* v___y_4535_; lean_object* v___y_4536_; lean_object* v___y_4537_; lean_object* v___y_4538_; lean_object* v___x_4547_; uint8_t v___x_4548_; 
v___x_4284_ = lean_unsigned_to_nat(0u);
v_tk_4411_ = l_Lean_Syntax_getArg(v_stx_4240_, v___x_4284_);
v___x_4471_ = lean_unsigned_to_nat(1u);
v___x_4547_ = l_Lean_Syntax_getArg(v_stx_4240_, v___x_4471_);
v___x_4548_ = l_Lean_Syntax_isNone(v___x_4547_);
if (v___x_4548_ == 0)
{
uint8_t v___x_4549_; 
lean_inc(v___x_4547_);
v___x_4549_ = l_Lean_Syntax_matchesNull(v___x_4547_, v___x_4471_);
if (v___x_4549_ == 0)
{
lean_object* v___x_4550_; 
lean_dec(v___x_4547_);
lean_dec(v_tk_4411_);
lean_dec(v_stx_4240_);
v___x_4550_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4550_;
}
else
{
lean_object* v_squeeze_4551_; lean_object* v___x_4552_; 
v_squeeze_4551_ = l_Lean_Syntax_getArg(v___x_4547_, v___x_4284_);
lean_dec(v___x_4547_);
v___x_4552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4552_, 0, v_squeeze_4551_);
v_squeeze_4530_ = v___x_4552_;
v___y_4531_ = v_a_4241_;
v___y_4532_ = v_a_4242_;
v___y_4533_ = v_a_4243_;
v___y_4534_ = v_a_4244_;
v___y_4535_ = v_a_4245_;
v___y_4536_ = v_a_4246_;
v___y_4537_ = v_a_4247_;
v___y_4538_ = v_a_4248_;
goto v___jp_4529_;
}
}
else
{
lean_object* v___x_4553_; 
lean_dec(v___x_4547_);
v___x_4553_ = lean_box(0);
v_squeeze_4530_ = v___x_4553_;
v___y_4531_ = v_a_4241_;
v___y_4532_ = v_a_4242_;
v___y_4533_ = v_a_4243_;
v___y_4534_ = v_a_4244_;
v___y_4535_ = v_a_4245_;
v___y_4536_ = v_a_4246_;
v___y_4537_ = v_a_4247_;
v___y_4538_ = v_a_4248_;
goto v___jp_4529_;
}
v___jp_4285_:
{
lean_object* v___x_4308_; lean_object* v___x_4309_; 
lean_inc_ref(v___y_4304_);
v___x_4308_ = l_Array_append___redArg(v___y_4304_, v___y_4307_);
lean_dec_ref(v___y_4307_);
lean_inc(v___y_4302_);
lean_inc(v___y_4296_);
v___x_4309_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4309_, 0, v___y_4296_);
lean_ctor_set(v___x_4309_, 1, v___y_4302_);
lean_ctor_set(v___x_4309_, 2, v___x_4308_);
if (lean_obj_tag(v___y_4293_) == 1)
{
lean_object* v_val_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; 
v_val_4310_ = lean_ctor_get(v___y_4293_, 0);
lean_inc(v_val_4310_);
lean_dec_ref_known(v___y_4293_, 1);
v___x_4311_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
v___x_4312_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_4296_, 4);
v___x_4313_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4313_, 0, v___y_4296_);
lean_ctor_set(v___x_4313_, 1, v___x_4312_);
lean_inc_ref(v___y_4304_);
v___x_4314_ = l_Array_append___redArg(v___y_4304_, v_val_4310_);
lean_dec(v_val_4310_);
lean_inc(v___y_4302_);
v___x_4315_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4315_, 0, v___y_4296_);
lean_ctor_set(v___x_4315_, 1, v___y_4302_);
lean_ctor_set(v___x_4315_, 2, v___x_4314_);
v___x_4316_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_4317_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4317_, 0, v___y_4296_);
lean_ctor_set(v___x_4317_, 1, v___x_4316_);
v___x_4318_ = l_Lean_Syntax_node3(v___y_4296_, v___x_4311_, v___x_4313_, v___x_4315_, v___x_4317_);
v___x_4319_ = l_Array_mkArray1___redArg(v___x_4318_);
v___y_4251_ = v___y_4286_;
v___y_4252_ = v___y_4287_;
v___y_4253_ = v___y_4288_;
v___y_4254_ = v___y_4289_;
v___y_4255_ = v___y_4290_;
v___y_4256_ = v___y_4291_;
v___y_4257_ = v___y_4292_;
v___y_4258_ = v___y_4294_;
v___y_4259_ = v___y_4295_;
v___y_4260_ = v___y_4296_;
v___y_4261_ = v___y_4297_;
v___y_4262_ = v___y_4298_;
v___y_4263_ = v___y_4299_;
v___y_4264_ = v___y_4300_;
v___y_4265_ = v___x_4309_;
v___y_4266_ = v___y_4301_;
v___y_4267_ = v___y_4302_;
v___y_4268_ = v___y_4303_;
v___y_4269_ = v___y_4304_;
v___y_4270_ = v___y_4305_;
v___y_4271_ = v___y_4306_;
v___y_4272_ = v___x_4319_;
goto v___jp_4250_;
}
else
{
lean_object* v___x_4320_; 
lean_dec(v___y_4293_);
v___x_4320_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___y_4251_ = v___y_4286_;
v___y_4252_ = v___y_4287_;
v___y_4253_ = v___y_4288_;
v___y_4254_ = v___y_4289_;
v___y_4255_ = v___y_4290_;
v___y_4256_ = v___y_4291_;
v___y_4257_ = v___y_4292_;
v___y_4258_ = v___y_4294_;
v___y_4259_ = v___y_4295_;
v___y_4260_ = v___y_4296_;
v___y_4261_ = v___y_4297_;
v___y_4262_ = v___y_4298_;
v___y_4263_ = v___y_4299_;
v___y_4264_ = v___y_4300_;
v___y_4265_ = v___x_4309_;
v___y_4266_ = v___y_4301_;
v___y_4267_ = v___y_4302_;
v___y_4268_ = v___y_4303_;
v___y_4269_ = v___y_4304_;
v___y_4270_ = v___y_4305_;
v___y_4271_ = v___y_4306_;
v___y_4272_ = v___x_4320_;
goto v___jp_4250_;
}
}
v___jp_4321_:
{
lean_object* v___x_4344_; lean_object* v___x_4345_; 
lean_inc_ref(v___y_4340_);
v___x_4344_ = l_Array_append___redArg(v___y_4340_, v___y_4343_);
lean_dec_ref(v___y_4343_);
lean_inc(v___y_4338_);
lean_inc(v___y_4332_);
v___x_4345_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4345_, 0, v___y_4332_);
lean_ctor_set(v___x_4345_, 1, v___y_4338_);
lean_ctor_set(v___x_4345_, 2, v___x_4344_);
if (lean_obj_tag(v___y_4324_) == 1)
{
lean_object* v_val_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; 
v_val_4346_ = lean_ctor_get(v___y_4324_, 0);
lean_inc(v_val_4346_);
lean_dec_ref_known(v___y_4324_, 1);
v___x_4347_ = l_Lean_SourceInfo_fromRef(v_val_4346_, v___x_4282_);
lean_dec(v_val_4346_);
v___x_4348_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_4349_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4349_, 0, v___x_4347_);
lean_ctor_set(v___x_4349_, 1, v___x_4348_);
v___x_4350_ = l_Array_mkArray1___redArg(v___x_4349_);
v___y_4286_ = v___y_4322_;
v___y_4287_ = v___y_4323_;
v___y_4288_ = v___y_4325_;
v___y_4289_ = v___x_4345_;
v___y_4290_ = v___y_4326_;
v___y_4291_ = v___y_4327_;
v___y_4292_ = v___y_4328_;
v___y_4293_ = v___y_4329_;
v___y_4294_ = v___y_4330_;
v___y_4295_ = v___y_4331_;
v___y_4296_ = v___y_4332_;
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
v___y_4307_ = v___x_4350_;
goto v___jp_4285_;
}
else
{
lean_object* v___x_4351_; 
v___x_4351_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_4324_);
lean_dec(v___y_4324_);
v___y_4286_ = v___y_4322_;
v___y_4287_ = v___y_4323_;
v___y_4288_ = v___y_4325_;
v___y_4289_ = v___x_4345_;
v___y_4290_ = v___y_4326_;
v___y_4291_ = v___y_4327_;
v___y_4292_ = v___y_4328_;
v___y_4293_ = v___y_4329_;
v___y_4294_ = v___y_4330_;
v___y_4295_ = v___y_4331_;
v___y_4296_ = v___y_4332_;
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
v___y_4307_ = v___x_4351_;
goto v___jp_4285_;
}
}
v___jp_4352_:
{
lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; 
lean_inc_ref(v___y_4371_);
v___x_4374_ = l_Array_append___redArg(v___y_4371_, v___y_4373_);
lean_dec_ref(v___y_4373_);
lean_inc(v___y_4368_);
lean_inc(v___y_4362_);
v___x_4375_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4375_, 0, v___y_4362_);
lean_ctor_set(v___x_4375_, 1, v___y_4368_);
lean_ctor_set(v___x_4375_, 2, v___x_4374_);
v___x_4376_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6));
if (lean_obj_tag(v___y_4369_) == 0)
{
lean_object* v___x_4377_; 
v___x_4377_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___y_4322_ = v___y_4353_;
v___y_4323_ = v___y_4354_;
v___y_4324_ = v___y_4355_;
v___y_4325_ = v___y_4356_;
v___y_4326_ = v___y_4357_;
v___y_4327_ = v___y_4358_;
v___y_4328_ = v___x_4375_;
v___y_4329_ = v___y_4359_;
v___y_4330_ = v___y_4360_;
v___y_4331_ = v___y_4361_;
v___y_4332_ = v___y_4362_;
v___y_4333_ = v___y_4363_;
v___y_4334_ = v___y_4364_;
v___y_4335_ = v___y_4365_;
v___y_4336_ = v___y_4366_;
v___y_4337_ = v___y_4367_;
v___y_4338_ = v___y_4368_;
v___y_4339_ = v___y_4370_;
v___y_4340_ = v___y_4371_;
v___y_4341_ = v___y_4372_;
v___y_4342_ = v___x_4376_;
v___y_4343_ = v___x_4377_;
goto v___jp_4321_;
}
else
{
lean_object* v_val_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; 
v_val_4378_ = lean_ctor_get(v___y_4369_, 0);
lean_inc(v_val_4378_);
lean_dec_ref_known(v___y_4369_, 1);
v___x_4379_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___x_4380_ = lean_array_push(v___x_4379_, v_val_4378_);
v___y_4322_ = v___y_4353_;
v___y_4323_ = v___y_4354_;
v___y_4324_ = v___y_4355_;
v___y_4325_ = v___y_4356_;
v___y_4326_ = v___y_4357_;
v___y_4327_ = v___y_4358_;
v___y_4328_ = v___x_4375_;
v___y_4329_ = v___y_4359_;
v___y_4330_ = v___y_4360_;
v___y_4331_ = v___y_4361_;
v___y_4332_ = v___y_4362_;
v___y_4333_ = v___y_4363_;
v___y_4334_ = v___y_4364_;
v___y_4335_ = v___y_4365_;
v___y_4336_ = v___y_4366_;
v___y_4337_ = v___y_4367_;
v___y_4338_ = v___y_4368_;
v___y_4339_ = v___y_4370_;
v___y_4340_ = v___y_4371_;
v___y_4341_ = v___y_4372_;
v___y_4342_ = v___x_4376_;
v___y_4343_ = v___x_4380_;
goto v___jp_4321_;
}
}
v___jp_4381_:
{
lean_object* v___x_4403_; lean_object* v___x_4404_; 
lean_inc_ref(v___y_4401_);
v___x_4403_ = l_Array_append___redArg(v___y_4401_, v___y_4402_);
lean_dec_ref(v___y_4402_);
lean_inc(v___y_4398_);
lean_inc(v___y_4391_);
v___x_4404_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4404_, 0, v___y_4391_);
lean_ctor_set(v___x_4404_, 1, v___y_4398_);
lean_ctor_set(v___x_4404_, 2, v___x_4403_);
if (lean_obj_tag(v___y_4396_) == 1)
{
lean_object* v_val_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; 
v_val_4405_ = lean_ctor_get(v___y_4396_, 0);
lean_inc(v_val_4405_);
lean_dec_ref_known(v___y_4396_, 1);
v___x_4406_ = l_Lean_SourceInfo_fromRef(v_val_4405_, v___x_4282_);
lean_dec(v_val_4405_);
v___x_4407_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__9));
v___x_4408_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4408_, 0, v___x_4406_);
lean_ctor_set(v___x_4408_, 1, v___x_4407_);
v___x_4409_ = l_Array_mkArray1___redArg(v___x_4408_);
v___y_4353_ = v___y_4382_;
v___y_4354_ = v___y_4383_;
v___y_4355_ = v___y_4384_;
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
v___y_4367_ = v___y_4397_;
v___y_4368_ = v___y_4398_;
v___y_4369_ = v___y_4399_;
v___y_4370_ = v___y_4400_;
v___y_4371_ = v___y_4401_;
v___y_4372_ = v___x_4404_;
v___y_4373_ = v___x_4409_;
goto v___jp_4352_;
}
else
{
lean_object* v___x_4410_; 
v___x_4410_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_4396_);
lean_dec(v___y_4396_);
v___y_4353_ = v___y_4382_;
v___y_4354_ = v___y_4383_;
v___y_4355_ = v___y_4384_;
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
v___y_4367_ = v___y_4397_;
v___y_4368_ = v___y_4398_;
v___y_4369_ = v___y_4399_;
v___y_4370_ = v___y_4400_;
v___y_4371_ = v___y_4401_;
v___y_4372_ = v___x_4404_;
v___y_4373_ = v___x_4410_;
goto v___jp_4352_;
}
}
v___jp_4412_:
{
lean_object* v_ref_4428_; uint8_t v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; 
v_ref_4428_ = lean_ctor_get(v___y_4422_, 2);
v___x_4429_ = 0;
v___x_4430_ = l_Lean_SourceInfo_fromRef(v_ref_4428_, v___x_4429_);
v___x_4431_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1));
v___x_4432_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
v___x_4433_ = l_Lean_SourceInfo_fromRef(v_tk_4411_, v___x_4282_);
lean_dec(v_tk_4411_);
v___x_4434_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4434_, 0, v___x_4433_);
lean_ctor_set(v___x_4434_, 1, v___x_4431_);
v___x_4435_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_4436_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6);
if (lean_obj_tag(v___y_4423_) == 1)
{
lean_object* v_val_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; 
v_val_4437_ = lean_ctor_get(v___y_4423_, 0);
lean_inc(v_val_4437_);
lean_dec_ref_known(v___y_4423_, 1);
v___x_4438_ = l_Lean_SourceInfo_fromRef(v_val_4437_, v___x_4282_);
lean_dec(v_val_4437_);
v___x_4439_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__1));
v___x_4440_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4440_, 0, v___x_4438_);
lean_ctor_set(v___x_4440_, 1, v___x_4439_);
v___x_4441_ = l_Array_mkArray1___redArg(v___x_4440_);
v___y_4382_ = v___y_4413_;
v___y_4383_ = v___y_4414_;
v___y_4384_ = v___y_4415_;
v___y_4385_ = v___y_4416_;
v___y_4386_ = v___y_4417_;
v___y_4387_ = v___x_4432_;
v___y_4388_ = v___y_4418_;
v___y_4389_ = v___y_4419_;
v___y_4390_ = v___x_4434_;
v___y_4391_ = v___x_4430_;
v___y_4392_ = v___y_4420_;
v___y_4393_ = v___y_4421_;
v___y_4394_ = v___x_4429_;
v___y_4395_ = v___y_4422_;
v___y_4396_ = v___y_4424_;
v___y_4397_ = v___y_4425_;
v___y_4398_ = v___x_4435_;
v___y_4399_ = v___y_4427_;
v___y_4400_ = v___y_4426_;
v___y_4401_ = v___x_4436_;
v___y_4402_ = v___x_4441_;
goto v___jp_4381_;
}
else
{
lean_object* v___x_4442_; 
v___x_4442_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_4423_);
lean_dec(v___y_4423_);
v___y_4382_ = v___y_4413_;
v___y_4383_ = v___y_4414_;
v___y_4384_ = v___y_4415_;
v___y_4385_ = v___y_4416_;
v___y_4386_ = v___y_4417_;
v___y_4387_ = v___x_4432_;
v___y_4388_ = v___y_4418_;
v___y_4389_ = v___y_4419_;
v___y_4390_ = v___x_4434_;
v___y_4391_ = v___x_4430_;
v___y_4392_ = v___y_4420_;
v___y_4393_ = v___y_4421_;
v___y_4394_ = v___x_4429_;
v___y_4395_ = v___y_4422_;
v___y_4396_ = v___y_4424_;
v___y_4397_ = v___y_4425_;
v___y_4398_ = v___x_4435_;
v___y_4399_ = v___y_4427_;
v___y_4400_ = v___y_4426_;
v___y_4401_ = v___x_4436_;
v___y_4402_ = v___x_4442_;
goto v___jp_4381_;
}
}
v___jp_4443_:
{
lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; 
v___x_4459_ = lean_unsigned_to_nat(5u);
v___x_4460_ = l_Lean_Syntax_getArg(v___y_4448_, v___x_4459_);
lean_dec(v___y_4448_);
v___x_4461_ = l_Lean_Syntax_getOptional_x3f(v___y_4449_);
lean_dec(v___y_4449_);
if (lean_obj_tag(v___x_4461_) == 0)
{
lean_object* v___x_4462_; 
v___x_4462_ = lean_box(0);
v___y_4413_ = v___y_4453_;
v___y_4414_ = v___x_4460_;
v___y_4415_ = v___y_4444_;
v___y_4416_ = v___y_4456_;
v___y_4417_ = v___y_4452_;
v___y_4418_ = v_args_4450_;
v___y_4419_ = v___y_4447_;
v___y_4420_ = v___y_4451_;
v___y_4421_ = v___y_4458_;
v___y_4422_ = v___y_4457_;
v___y_4423_ = v___y_4446_;
v___y_4424_ = v___y_4445_;
v___y_4425_ = v___y_4455_;
v___y_4426_ = v___y_4454_;
v___y_4427_ = v___x_4462_;
goto v___jp_4412_;
}
else
{
lean_object* v_val_4463_; lean_object* v___x_4465_; uint8_t v_isShared_4466_; uint8_t v_isSharedCheck_4470_; 
v_val_4463_ = lean_ctor_get(v___x_4461_, 0);
v_isSharedCheck_4470_ = !lean_is_exclusive(v___x_4461_);
if (v_isSharedCheck_4470_ == 0)
{
v___x_4465_ = v___x_4461_;
v_isShared_4466_ = v_isSharedCheck_4470_;
goto v_resetjp_4464_;
}
else
{
lean_inc(v_val_4463_);
lean_dec(v___x_4461_);
v___x_4465_ = lean_box(0);
v_isShared_4466_ = v_isSharedCheck_4470_;
goto v_resetjp_4464_;
}
v_resetjp_4464_:
{
lean_object* v___x_4468_; 
if (v_isShared_4466_ == 0)
{
v___x_4468_ = v___x_4465_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4469_; 
v_reuseFailAlloc_4469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4469_, 0, v_val_4463_);
v___x_4468_ = v_reuseFailAlloc_4469_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
v___y_4413_ = v___y_4453_;
v___y_4414_ = v___x_4460_;
v___y_4415_ = v___y_4444_;
v___y_4416_ = v___y_4456_;
v___y_4417_ = v___y_4452_;
v___y_4418_ = v_args_4450_;
v___y_4419_ = v___y_4447_;
v___y_4420_ = v___y_4451_;
v___y_4421_ = v___y_4458_;
v___y_4422_ = v___y_4457_;
v___y_4423_ = v___y_4446_;
v___y_4424_ = v___y_4445_;
v___y_4425_ = v___y_4455_;
v___y_4426_ = v___y_4454_;
v___y_4427_ = v___x_4468_;
goto v___jp_4412_;
}
}
}
}
v___jp_4472_:
{
lean_object* v___x_4488_; uint8_t v___x_4489_; 
v___x_4488_ = l_Lean_Syntax_getArg(v___y_4475_, v___y_4477_);
v___x_4489_ = l_Lean_Syntax_isNone(v___x_4488_);
if (v___x_4489_ == 0)
{
uint8_t v___x_4490_; 
lean_inc(v___x_4488_);
v___x_4490_ = l_Lean_Syntax_matchesNull(v___x_4488_, v___x_4471_);
if (v___x_4490_ == 0)
{
lean_object* v___x_4491_; 
lean_dec(v___x_4488_);
lean_dec(v_only_4479_);
lean_dec(v___y_4478_);
lean_dec(v___y_4476_);
lean_dec(v___y_4475_);
lean_dec(v___y_4474_);
lean_dec(v___y_4473_);
lean_dec(v_tk_4411_);
v___x_4491_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4491_;
}
else
{
lean_object* v___x_4492_; lean_object* v___x_4493_; uint8_t v___x_4494_; 
v___x_4492_ = l_Lean_Syntax_getArg(v___x_4488_, v___x_4284_);
lean_dec(v___x_4488_);
v___x_4493_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
lean_inc(v___x_4492_);
v___x_4494_ = l_Lean_Syntax_isOfKind(v___x_4492_, v___x_4493_);
if (v___x_4494_ == 0)
{
lean_object* v___x_4495_; 
lean_dec(v___x_4492_);
lean_dec(v_only_4479_);
lean_dec(v___y_4478_);
lean_dec(v___y_4476_);
lean_dec(v___y_4475_);
lean_dec(v___y_4474_);
lean_dec(v___y_4473_);
lean_dec(v_tk_4411_);
v___x_4495_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4495_;
}
else
{
lean_object* v___x_4496_; lean_object* v_args_4497_; lean_object* v___x_4498_; 
v___x_4496_ = l_Lean_Syntax_getArg(v___x_4492_, v___x_4471_);
lean_dec(v___x_4492_);
v_args_4497_ = l_Lean_Syntax_getArgs(v___x_4496_);
lean_dec(v___x_4496_);
v___x_4498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4498_, 0, v_args_4497_);
v___y_4444_ = v_only_4479_;
v___y_4445_ = v___y_4474_;
v___y_4446_ = v___y_4473_;
v___y_4447_ = v___y_4476_;
v___y_4448_ = v___y_4475_;
v___y_4449_ = v___y_4478_;
v_args_4450_ = v___x_4498_;
v___y_4451_ = v___y_4480_;
v___y_4452_ = v___y_4481_;
v___y_4453_ = v___y_4482_;
v___y_4454_ = v___y_4483_;
v___y_4455_ = v___y_4484_;
v___y_4456_ = v___y_4485_;
v___y_4457_ = v___y_4486_;
v___y_4458_ = v___y_4487_;
goto v___jp_4443_;
}
}
}
else
{
lean_object* v___x_4499_; 
lean_dec(v___x_4488_);
v___x_4499_ = lean_box(0);
v___y_4444_ = v_only_4479_;
v___y_4445_ = v___y_4474_;
v___y_4446_ = v___y_4473_;
v___y_4447_ = v___y_4476_;
v___y_4448_ = v___y_4475_;
v___y_4449_ = v___y_4478_;
v_args_4450_ = v___x_4499_;
v___y_4451_ = v___y_4480_;
v___y_4452_ = v___y_4481_;
v___y_4453_ = v___y_4482_;
v___y_4454_ = v___y_4483_;
v___y_4455_ = v___y_4484_;
v___y_4456_ = v___y_4485_;
v___y_4457_ = v___y_4486_;
v___y_4458_ = v___y_4487_;
goto v___jp_4443_;
}
}
v___jp_4500_:
{
lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; uint8_t v___x_4515_; 
v___x_4512_ = lean_unsigned_to_nat(3u);
v___x_4513_ = l_Lean_Syntax_getArg(v_stx_4240_, v___x_4512_);
lean_dec(v_stx_4240_);
v___x_4514_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2));
lean_inc(v___x_4513_);
v___x_4515_ = l_Lean_Syntax_isOfKind(v___x_4513_, v___x_4514_);
if (v___x_4515_ == 0)
{
lean_object* v___x_4516_; 
lean_dec(v___x_4513_);
lean_dec(v_unfold_4503_);
lean_dec(v___y_4501_);
lean_dec(v_tk_4411_);
v___x_4516_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4516_;
}
else
{
lean_object* v___x_4517_; lean_object* v___x_4518_; uint8_t v___x_4519_; 
v___x_4517_ = l_Lean_Syntax_getArg(v___x_4513_, v___x_4284_);
v___x_4518_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8));
lean_inc(v___x_4517_);
v___x_4519_ = l_Lean_Syntax_isOfKind(v___x_4517_, v___x_4518_);
if (v___x_4519_ == 0)
{
lean_object* v___x_4520_; 
lean_dec(v___x_4517_);
lean_dec(v___x_4513_);
lean_dec(v_unfold_4503_);
lean_dec(v___y_4501_);
lean_dec(v_tk_4411_);
v___x_4520_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4520_;
}
else
{
lean_object* v___x_4521_; lean_object* v___x_4522_; uint8_t v___x_4523_; 
v___x_4521_ = l_Lean_Syntax_getArg(v___x_4513_, v___x_4471_);
v___x_4522_ = l_Lean_Syntax_getArg(v___x_4513_, v___y_4502_);
v___x_4523_ = l_Lean_Syntax_isNone(v___x_4522_);
if (v___x_4523_ == 0)
{
uint8_t v___x_4524_; 
lean_inc(v___x_4522_);
v___x_4524_ = l_Lean_Syntax_matchesNull(v___x_4522_, v___x_4471_);
if (v___x_4524_ == 0)
{
lean_object* v___x_4525_; 
lean_dec(v___x_4522_);
lean_dec(v___x_4521_);
lean_dec(v___x_4517_);
lean_dec(v___x_4513_);
lean_dec(v_unfold_4503_);
lean_dec(v___y_4501_);
lean_dec(v_tk_4411_);
v___x_4525_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4525_;
}
else
{
lean_object* v_only_4526_; lean_object* v___x_4527_; 
v_only_4526_ = l_Lean_Syntax_getArg(v___x_4522_, v___x_4284_);
lean_dec(v___x_4522_);
v___x_4527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4527_, 0, v_only_4526_);
v___y_4473_ = v___y_4501_;
v___y_4474_ = v_unfold_4503_;
v___y_4475_ = v___x_4513_;
v___y_4476_ = v___x_4517_;
v___y_4477_ = v___x_4512_;
v___y_4478_ = v___x_4521_;
v_only_4479_ = v___x_4527_;
v___y_4480_ = v___y_4504_;
v___y_4481_ = v___y_4505_;
v___y_4482_ = v___y_4506_;
v___y_4483_ = v___y_4507_;
v___y_4484_ = v___y_4508_;
v___y_4485_ = v___y_4509_;
v___y_4486_ = v___y_4510_;
v___y_4487_ = v___y_4511_;
goto v___jp_4472_;
}
}
else
{
lean_object* v___x_4528_; 
lean_dec(v___x_4522_);
v___x_4528_ = lean_box(0);
v___y_4473_ = v___y_4501_;
v___y_4474_ = v_unfold_4503_;
v___y_4475_ = v___x_4513_;
v___y_4476_ = v___x_4517_;
v___y_4477_ = v___x_4512_;
v___y_4478_ = v___x_4521_;
v_only_4479_ = v___x_4528_;
v___y_4480_ = v___y_4504_;
v___y_4481_ = v___y_4505_;
v___y_4482_ = v___y_4506_;
v___y_4483_ = v___y_4507_;
v___y_4484_ = v___y_4508_;
v___y_4485_ = v___y_4509_;
v___y_4486_ = v___y_4510_;
v___y_4487_ = v___y_4511_;
goto v___jp_4472_;
}
}
}
}
v___jp_4529_:
{
lean_object* v___x_4539_; lean_object* v___x_4540_; uint8_t v___x_4541_; 
v___x_4539_ = lean_unsigned_to_nat(2u);
v___x_4540_ = l_Lean_Syntax_getArg(v_stx_4240_, v___x_4539_);
v___x_4541_ = l_Lean_Syntax_isNone(v___x_4540_);
if (v___x_4541_ == 0)
{
uint8_t v___x_4542_; 
lean_inc(v___x_4540_);
v___x_4542_ = l_Lean_Syntax_matchesNull(v___x_4540_, v___x_4471_);
if (v___x_4542_ == 0)
{
lean_object* v___x_4543_; 
lean_dec(v___x_4540_);
lean_dec(v_squeeze_4530_);
lean_dec(v_tk_4411_);
lean_dec(v_stx_4240_);
v___x_4543_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4543_;
}
else
{
lean_object* v_unfold_4544_; lean_object* v___x_4545_; 
v_unfold_4544_ = l_Lean_Syntax_getArg(v___x_4540_, v___x_4284_);
lean_dec(v___x_4540_);
v___x_4545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4545_, 0, v_unfold_4544_);
v___y_4501_ = v_squeeze_4530_;
v___y_4502_ = v___x_4539_;
v_unfold_4503_ = v___x_4545_;
v___y_4504_ = v___y_4531_;
v___y_4505_ = v___y_4532_;
v___y_4506_ = v___y_4533_;
v___y_4507_ = v___y_4534_;
v___y_4508_ = v___y_4535_;
v___y_4509_ = v___y_4536_;
v___y_4510_ = v___y_4537_;
v___y_4511_ = v___y_4538_;
goto v___jp_4500_;
}
}
else
{
lean_object* v___x_4546_; 
lean_dec(v___x_4540_);
v___x_4546_ = lean_box(0);
v___y_4501_ = v_squeeze_4530_;
v___y_4502_ = v___x_4539_;
v_unfold_4503_ = v___x_4546_;
v___y_4504_ = v___y_4531_;
v___y_4505_ = v___y_4532_;
v___y_4506_ = v___y_4533_;
v___y_4507_ = v___y_4534_;
v___y_4508_ = v___y_4535_;
v___y_4509_ = v___y_4536_;
v___y_4510_ = v___y_4537_;
v___y_4511_ = v___y_4538_;
goto v___jp_4500_;
}
}
}
v___jp_4250_:
{
lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; 
lean_inc_ref(v___y_4269_);
v___x_4273_ = l_Array_append___redArg(v___y_4269_, v___y_4272_);
lean_dec_ref(v___y_4272_);
lean_inc_n(v___y_4267_, 2);
lean_inc_n(v___y_4260_, 4);
v___x_4274_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4274_, 0, v___y_4260_);
lean_ctor_set(v___x_4274_, 1, v___y_4267_);
lean_ctor_set(v___x_4274_, 2, v___x_4273_);
v___x_4275_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__5));
v___x_4276_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4276_, 0, v___y_4260_);
lean_ctor_set(v___x_4276_, 1, v___x_4275_);
v___x_4277_ = l_Lean_Syntax_node2(v___y_4260_, v___y_4267_, v___x_4276_, v___y_4252_);
lean_inc(v___y_4271_);
v___x_4278_ = l_Lean_Syntax_node5(v___y_4260_, v___y_4271_, v___y_4258_, v___y_4254_, v___y_4265_, v___x_4274_, v___x_4277_);
lean_inc(v___y_4256_);
v___x_4279_ = l_Lean_Syntax_node4(v___y_4260_, v___y_4256_, v___y_4259_, v___y_4270_, v___y_4257_, v___x_4278_);
v___x_4280_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v___y_4263_, v___x_4279_, v___y_4261_, v___y_4255_, v___y_4251_, v___y_4268_, v___y_4266_, v___y_4253_, v___y_4264_, v___y_4262_);
return v___x_4280_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___boxed(lean_object* v_stx_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_, lean_object* v_a_4558_, lean_object* v_a_4559_, lean_object* v_a_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_){
_start:
{
lean_object* v_res_4564_; 
v_res_4564_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang(v_stx_4554_, v_a_4555_, v_a_4556_, v_a_4557_, v_a_4558_, v_a_4559_, v_a_4560_, v_a_4561_, v_a_4562_);
lean_dec(v_a_4562_);
lean_dec_ref(v_a_4561_);
lean_dec(v_a_4560_);
lean_dec_ref(v_a_4559_);
lean_dec(v_a_4558_);
lean_dec_ref(v_a_4557_);
lean_dec(v_a_4556_);
lean_dec_ref(v_a_4555_);
return v_res_4564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1(){
_start:
{
lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; 
v___x_4573_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4574_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0));
v___x_4575_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1));
v___x_4576_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___boxed), 10, 0);
v___x_4577_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4573_, v___x_4574_, v___x_4575_, v___x_4576_);
return v___x_4577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___boxed(lean_object* v_a_4578_){
_start:
{
lean_object* v_res_4579_; 
v_res_4579_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1();
return v_res_4579_;
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
