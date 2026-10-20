// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Contract
// Imports: public import Std.Tactic.Do.Syntax public import Std.WP public import Lean.Elab.Util public import Lean.Elab.Command public import Lean.Elab.Do.Basic import Lean.DocString.Extension import Lean.Meta.Tactic.Simp.Main meta import Lean.Parser.Command meta import Lean.Parser.Term meta import Lean.Parser.Do import Init.Syntax import Init.Grind.Interactive
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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_empty___redArg();
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_SimpTheorems_addConst(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Elab_Do_experimental_intrinsic;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldProjInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getAtomVal(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_mkCIdent(lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_ensureUnitAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_mkPUnit___redArg(lean_object*);
lean_object* l_Lean_Elab_Do_mkMonadApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_mkBindUnlessPure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_Lean_Elab_Term_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* l_Lean_Elab_Term_tryPostpone(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Do_doElemElabAttribute;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Macro_hasDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "explicitBinder"};
static const lean_object* l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__3_value),LEAN_SCALAR_PTR_LITERAL(49, 119, 193, 23, 170, 93, 183, 238)}};
static const lean_object* l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_contractBinderIdents(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "whereStructInst"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(164, 171, 248, 18, 201, 160, 43, 108)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declValEqns"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(185, 66, 113, 88, 174, 230, 155, 36)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__7_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__8_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__7_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__11_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__12_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_getPath(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_getPath___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_setPath(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_setPath___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "spec"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 105, 220, 149, 84, 64, 243, 129)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0___closed__0_value),((lean_object*)&l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "duplicate `spec` section"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "contractDeclVal"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 214, 40, 194, 192, 243, 241, 169)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__2_value),((lean_object*)&l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "throwsClause"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 245, 79, 142, 188, 231, 201, 155)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(209, 134, 40, 160, 122, 195, 31, 223)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "WP"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__7_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__6_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "EPostSlot"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "set"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__9_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__4_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__10_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__10_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__8_value),LEAN_SCALAR_PTR_LITERAL(111, 147, 31, 83, 253, 106, 140, 151)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__10_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__9_value),LEAN_SCALAR_PTR_LITERAL(55, 180, 133, 168, 66, 6, 92, 213)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__10_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__11;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__12_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__13_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__13_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__12_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__13_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__14_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__15_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__15_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__15_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__14_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__15_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__16_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__17 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__17_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__17_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__18 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__18_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__19 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__19_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__20;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__21 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__21_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__22 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__22_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__23 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__23_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__24_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__21_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__24_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__22_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__24_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__23_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__24 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__24_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__24_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__25 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__25_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__26 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__26_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__27_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__26_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__27 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__27_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__27_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__28 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__28_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__4_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__29_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__29 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__29_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__29_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__30 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__30_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__31_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__31_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__31 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__31_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__31_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__32 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__32_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__33 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__33_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__33_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__34 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__34_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__34_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__35 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__35_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__32_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__35_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__36 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__36_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__30_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__36_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__37 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__37_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__28_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__37_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__38 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__38_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__25_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__38_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__39 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__39_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__40 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__40_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__41_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__41_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__41_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__40_value),LEAN_SCALAR_PTR_LITERAL(249, 155, 133, 242, 71, 132, 191, 97)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__41 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__41_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__42 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__42_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "in"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "open"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "openScoped"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "scoped"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Std.WP"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_expandDefContract___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__5;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Lean.Order"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_expandDefContract___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__7;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__10_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__11_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__12_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__13_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__14_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__15_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "theorem"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__16_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__17_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declSig"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__18_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__19 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__19_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__20 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__20_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__21 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__21_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__22 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__22_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "by"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__23 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__23_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__24 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__24_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__25 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__25_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "vcgen"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__26 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__26_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__27 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__27_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__28 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__28_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpLemma"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__29 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__29_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__30 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__30_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "vcgenDischargeGrind"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__31 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__31_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__32 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__32_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindSeq"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__33 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__33_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "grindSeq1Indented"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__34 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__34_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "grindStep"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__35 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__35_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "grindTry_"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__36 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__36_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "try"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__37 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__37_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "finish"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__38 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__38_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "first"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__39 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__39_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__40 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__40_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__40_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__41 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__41_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__42 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__42_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "done"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__43 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__43_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "fail"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__44 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__44_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__45 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__45_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__46 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__46_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "contractEPosts"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__47 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__47_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "contract_eposts%"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__48 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__48_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_expandDefContract___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__49;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "tripleExceptPost"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__50 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__50_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⦃"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__51 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__51_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⦄"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__52 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__52_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_expandDefContract___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__53;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__54 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__54_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "unproved verification conditions for the contract of `"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__55 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__55_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "`; discharge them in a `where finally | spec => ...` section of the definition"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__56 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__56_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "skip"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__57 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__57_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "`; the `where finally | spec => ...` section does not discharge them"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__58 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__58_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 5, .m_data = "term⊥"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__59 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__59_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__60_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__60_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__26_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__60_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__59_value),LEAN_SCALAR_PTR_LITERAL(232, 78, 68, 112, 65, 121, 100, 195)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__60 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__60_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⊥"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__61 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__61_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "ensuresClause"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__62 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__62_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__63_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__63_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__63_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__63_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__63_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__63_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__62_value),LEAN_SCALAR_PTR_LITERAL(80, 249, 216, 241, 199, 195, 198, 237)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__63 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__63_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__64 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__64_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__65_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__65_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__65_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__65_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__65_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__65_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__64_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__65 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__65_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__66 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__66_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__67 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__67_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 5, .m_data = "term⊤"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__68 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__68_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__69_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__69_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__69_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__26_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__69_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__68_value),LEAN_SCALAR_PTR_LITERAL(137, 158, 127, 165, 41, 148, 243, 67)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__69 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__69_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⊤"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__70 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__70_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "requiresClause"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__71 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__71_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__72_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__72_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__72_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__72_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__72_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__72_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__71_value),LEAN_SCALAR_PTR_LITERAL(132, 130, 91, 181, 57, 218, 183, 96)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__72 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__72_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 134, .m_capacity = 134, .m_length = 133, .m_data = "`given`/`requires`/`ensures`/`throws` contracts elaborate to a `vcgen`-proved specification theorem; add `import Std.WP` to use them."};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__73 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__73_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Triple"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__74 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__74_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__75_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__4_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__75_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__75_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__75_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__74_value),LEAN_SCALAR_PTR_LITERAL(202, 119, 227, 254, 29, 206, 25, 24)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__75 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__75_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__76 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__76_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__77_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__77_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__77_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__77_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__77_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_expandDefContract___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__77_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__76_value),LEAN_SCALAR_PTR_LITERAL(248, 187, 217, 228, 39, 184, 218, 135)}};
static const lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___closed__77 = (const lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__77_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_expandDefContract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__0_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__0_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__8_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "expandDefContract"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__21_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__2_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__22_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__2_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__23_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(57, 222, 255, 251, 159, 111, 208, 249)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 324, .m_capacity = 324, .m_length = 313, .m_data = "Expand a `def` carrying `given`/`requires`/`ensures`/`throws` clauses into the plain `def`\nplus a spec theorem `@[spec] theorem f.spec : ∀ xs, ⦃P⦄ f args ⦃fun b => Q; E⦄` proved by\n`vcgen`. A `where finally | spec => steps` section supplies `grind`-mode steps for the\nverification conditions `finish` leaves open."};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3___boxed(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__0;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__2;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 32, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 1, 1, 1, 0, 1),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 1, 1, 0, 0),LEAN_SCALAR_PTR_LITERAL(0, 1, 1, 1, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3_value;
static const lean_array_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__5;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__6;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__7;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__8;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__18___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___closed__0_value;
static const lean_array_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__9(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__0;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__1;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__0___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__1___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Prod"};
static const lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "fst_bot"};
static const lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__26_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(85, 207, 85, 101, 141, 28, 12, 60)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__3_value),LEAN_SCALAR_PTR_LITERAL(186, 58, 243, 31, 167, 194, 180, 25)}};
static const lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "snd_bot"};
static const lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__26_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(85, 207, 85, 101, 141, 28, 12, 60)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__5_value),LEAN_SCALAR_PTR_LITERAL(57, 77, 34, 250, 153, 237, 26, 225)}};
static const lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "EStackEnd"};
static const lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "bot_eq"};
static const lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__4_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__9_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__7_value),LEAN_SCALAR_PTR_LITERAL(223, 8, 81, 115, 57, 234, 19, 38)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__8_value),LEAN_SCALAR_PTR_LITERAL(41, 7, 115, 177, 201, 198, 36, 123)}};
static const lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__9_value;
static const lean_array_object l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__4_value),((lean_object*)&l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__6_value),((lean_object*)&l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__9_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__18(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17_spec__18(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___closed__0_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___closed__0_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___closed__0_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__47_value),LEAN_SCALAR_PTR_LITERAL(112, 108, 40, 168, 196, 170, 99, 136)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "elabContractEPosts"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__21_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___closed__2_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__22_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___closed__2_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__23_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(245, 40, 68, 173, 208, 104, 41, 180)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 199, .m_capacity = 199, .m_length = 192, .m_data = "Elaborating `contract_eposts% e` unfolds the `EPostSlot.set` applications and `⊥` in `e`, e.g.\nto an `estack⟨...⟩` expression. Used in the expansion of `throws` clauses to yield simpler specs."};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts_docString__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts_docString__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts_docString__3___boxed(lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "The "};
static const lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__0 = (const lean_object*)&l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1;
static const lean_string_object l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 165, .m_capacity = 165, .m_length = 164, .m_data = " is part of the experimental intrinsic verification syntax; `set_option experimental.intrinsic true` acknowledges its experimental status and silences this warning."};
static const lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__2 = (const lean_object*)&l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "` clause"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractNotice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractNotice___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "elabContractNotice"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__21_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__22_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__23_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(60, 64, 145, 33, 235, 196, 87, 155)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 170, .m_capacity = 170, .m_length = 169, .m_data = "Report the experimental status of each contract clause the notice carries, in a slight\ncommand-level misuse of a `contractDeclVal` node. Does not change the environment."};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice_docString__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice_docString__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice_docString__3___boxed(lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__4_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "`assert` element"};
static const lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__1;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 46, 79, 112, 232, 100, 17, 35)}};
static const lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_expandDefContract___closed__2_value),LEAN_SCALAR_PTR_LITERAL(55, 166, 237, 23, 37, 47, 5, 133)}};
static const lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__28_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Gadget"};
static const lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "assertGadget"};
static const lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__4_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__8_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__6_value),LEAN_SCALAR_PTR_LITERAL(193, 119, 194, 233, 172, 109, 107, 25)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__7_value),LEAN_SCALAR_PTR_LITERAL(223, 124, 11, 88, 114, 168, 194, 251)}};
static const lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__9;
static const lean_string_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 84, .m_capacity = 84, .m_length = 83, .m_data = "the `assert` element elaborates to a `vcgen` gadget; add `import Std.WP` to use it."};
static const lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__11;
static const lean_string_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doAssertion"};
static const lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__13_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__13_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__12_value),LEAN_SCALAR_PTR_LITERAL(144, 179, 243, 245, 156, 230, 227, 142)}};
static const lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__13_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "elabDoAssertion"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__21_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__22_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__23_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 130, 201, 151, 146, 48, 207, 207)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0_spec__0(lean_object* v_as_1_, size_t v_i_2_, size_t v_stop_3_, lean_object* v_b_4_){
_start:
{
lean_object* v___y_6_; uint8_t v___x_10_; 
v___x_10_ = lean_usize_dec_eq(v_i_2_, v_stop_3_);
if (v___x_10_ == 0)
{
lean_object* v___x_11_; uint8_t v___x_12_; 
v___x_11_ = lean_array_uget_borrowed(v_as_1_, v_i_2_);
v___x_12_ = l_Lean_Syntax_isIdent(v___x_11_);
if (v___x_12_ == 0)
{
v___y_6_ = v_b_4_;
goto v___jp_5_;
}
else
{
lean_object* v___x_13_; 
lean_inc(v___x_11_);
v___x_13_ = lean_array_push(v_b_4_, v___x_11_);
v___y_6_ = v___x_13_;
goto v___jp_5_;
}
}
else
{
return v_b_4_;
}
v___jp_5_:
{
size_t v___x_7_; size_t v___x_8_; 
v___x_7_ = ((size_t)1ULL);
v___x_8_ = lean_usize_add(v_i_2_, v___x_7_);
v_i_2_ = v___x_8_;
v_b_4_ = v___y_6_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0_spec__0___boxed(lean_object* v_as_14_, lean_object* v_i_15_, lean_object* v_stop_16_, lean_object* v_b_17_){
_start:
{
size_t v_i_boxed_18_; size_t v_stop_boxed_19_; lean_object* v_res_20_; 
v_i_boxed_18_ = lean_unbox_usize(v_i_15_);
lean_dec(v_i_15_);
v_stop_boxed_19_ = lean_unbox_usize(v_stop_16_);
lean_dec(v_stop_16_);
v_res_20_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0_spec__0(v_as_14_, v_i_boxed_18_, v_stop_boxed_19_, v_b_17_);
lean_dec_ref(v_as_14_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0(lean_object* v_as_23_, lean_object* v_start_24_, lean_object* v_stop_25_){
_start:
{
lean_object* v___x_26_; uint8_t v___x_27_; 
v___x_26_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0___closed__0));
v___x_27_ = lean_nat_dec_lt(v_start_24_, v_stop_25_);
if (v___x_27_ == 0)
{
return v___x_26_;
}
else
{
lean_object* v___x_28_; uint8_t v___x_29_; 
v___x_28_ = lean_array_get_size(v_as_23_);
v___x_29_ = lean_nat_dec_le(v_stop_25_, v___x_28_);
if (v___x_29_ == 0)
{
uint8_t v___x_30_; 
v___x_30_ = lean_nat_dec_lt(v_start_24_, v___x_28_);
if (v___x_30_ == 0)
{
return v___x_26_;
}
else
{
size_t v___x_31_; size_t v___x_32_; lean_object* v___x_33_; 
v___x_31_ = lean_usize_of_nat(v_start_24_);
v___x_32_ = lean_usize_of_nat(v___x_28_);
v___x_33_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0_spec__0(v_as_23_, v___x_31_, v___x_32_, v___x_26_);
return v___x_33_;
}
}
else
{
size_t v___x_34_; size_t v___x_35_; lean_object* v___x_36_; 
v___x_34_ = lean_usize_of_nat(v_start_24_);
v___x_35_ = lean_usize_of_nat(v_stop_25_);
v___x_36_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0_spec__0(v_as_23_, v___x_34_, v___x_35_, v___x_26_);
return v___x_36_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0___boxed(lean_object* v_as_37_, lean_object* v_start_38_, lean_object* v_stop_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0(v_as_37_, v_start_38_, v_stop_39_);
lean_dec(v_stop_39_);
lean_dec(v_start_38_);
lean_dec_ref(v_as_37_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_contractBinderIdents(lean_object* v_binder_50_){
_start:
{
lean_object* v___x_51_; uint8_t v___x_52_; 
v___x_51_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__4));
lean_inc(v_binder_50_);
v___x_52_ = l_Lean_Syntax_isOfKind(v_binder_50_, v___x_51_);
if (v___x_52_ == 0)
{
uint8_t v___x_53_; 
v___x_53_ = l_Lean_Syntax_isIdent(v_binder_50_);
if (v___x_53_ == 0)
{
lean_object* v___x_54_; 
lean_dec(v_binder_50_);
v___x_54_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0___closed__0));
return v___x_54_;
}
else
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_55_ = lean_unsigned_to_nat(1u);
v___x_56_ = lean_mk_empty_array_with_capacity(v___x_55_);
v___x_57_ = lean_array_push(v___x_56_, v_binder_50_);
return v___x_57_;
}
}
else
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_65_; lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_58_ = lean_unsigned_to_nat(0u);
v___x_59_ = lean_unsigned_to_nat(1u);
v___x_60_ = l_Lean_Syntax_getArg(v_binder_50_, v___x_59_);
v___x_65_ = lean_unsigned_to_nat(2u);
v___x_66_ = l_Lean_Syntax_getArg(v_binder_50_, v___x_65_);
v___x_67_ = l_Lean_Syntax_isNone(v___x_66_);
if (v___x_67_ == 0)
{
uint8_t v___x_68_; 
v___x_68_ = l_Lean_Syntax_matchesNull(v___x_66_, v___x_65_);
if (v___x_68_ == 0)
{
uint8_t v___x_69_; 
lean_dec(v___x_60_);
v___x_69_ = l_Lean_Syntax_isIdent(v_binder_50_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; 
lean_dec(v_binder_50_);
v___x_70_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0___closed__0));
return v___x_70_;
}
else
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_mk_empty_array_with_capacity(v___x_59_);
v___x_72_ = lean_array_push(v___x_71_, v_binder_50_);
return v___x_72_;
}
}
else
{
lean_dec(v_binder_50_);
goto v___jp_61_;
}
}
else
{
lean_dec(v___x_66_);
lean_dec(v_binder_50_);
goto v___jp_61_;
}
v___jp_61_:
{
lean_object* v_ids_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v_ids_62_ = l_Lean_Syntax_getArgs(v___x_60_);
lean_dec(v___x_60_);
v___x_63_ = lean_array_get_size(v_ids_62_);
v___x_64_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0(v_ids_62_, v___x_58_, v___x_63_);
lean_dec_ref(v_ids_62_);
return v___x_64_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f(lean_object* v_v_107_){
_start:
{
lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_108_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__2));
lean_inc(v_v_107_);
v___x_109_ = l_Lean_Syntax_isOfKind(v_v_107_, v___x_108_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_110_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__4));
lean_inc(v_v_107_);
v___x_111_ = l_Lean_Syntax_isOfKind(v_v_107_, v___x_110_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_112_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__6));
v___x_113_ = l_Lean_Syntax_isOfKind(v_v_107_, v___x_112_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; 
v___x_114_ = lean_box(0);
return v___x_114_;
}
else
{
lean_object* v___x_115_; 
v___x_115_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__9));
return v___x_115_;
}
}
else
{
lean_object* v___x_116_; 
lean_dec(v_v_107_);
v___x_116_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__10));
return v___x_116_;
}
}
else
{
lean_object* v___x_117_; 
lean_dec(v_v_107_);
v___x_117_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__12));
return v___x_117_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_getPath(lean_object* v_s_118_, lean_object* v_x_119_){
_start:
{
if (lean_obj_tag(v_x_119_) == 0)
{
return v_s_118_;
}
else
{
lean_object* v_head_120_; lean_object* v_tail_121_; lean_object* v___x_122_; 
v_head_120_ = lean_ctor_get(v_x_119_, 0);
v_tail_121_ = lean_ctor_get(v_x_119_, 1);
v___x_122_ = l_Lean_Syntax_getArg(v_s_118_, v_head_120_);
lean_dec(v_s_118_);
v_s_118_ = v___x_122_;
v_x_119_ = v_tail_121_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_getPath___boxed(lean_object* v_s_124_, lean_object* v_x_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_getPath(v_s_124_, v_x_125_);
lean_dec(v_x_125_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_setPath(lean_object* v_s_127_, lean_object* v_x_128_, lean_object* v_x_129_){
_start:
{
if (lean_obj_tag(v_x_128_) == 0)
{
lean_dec(v_s_127_);
lean_inc(v_x_129_);
return v_x_129_;
}
else
{
lean_object* v_head_130_; lean_object* v_tail_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v_head_130_ = lean_ctor_get(v_x_128_, 0);
v_tail_131_ = lean_ctor_get(v_x_128_, 1);
v___x_132_ = l_Lean_Syntax_getArg(v_s_127_, v_head_130_);
v___x_133_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_setPath(v___x_132_, v_tail_131_, v_x_129_);
v___x_134_ = l_Lean_Syntax_setArg(v_s_127_, v_head_130_, v___x_133_);
return v___x_134_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_setPath___boxed(lean_object* v_s_135_, lean_object* v_x_136_, lean_object* v_x_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_setPath(v_s_135_, v_x_136_, v_x_137_);
lean_dec(v_x_137_);
lean_dec(v_x_136_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0(lean_object* v_as_142_, size_t v_sz_143_, size_t v_i_144_, lean_object* v_b_145_){
_start:
{
lean_object* v_a_147_; uint8_t v___x_151_; 
v___x_151_ = lean_usize_dec_lt(v_i_144_, v_sz_143_);
if (v___x_151_ == 0)
{
return v_b_145_;
}
else
{
lean_object* v_fst_152_; lean_object* v_snd_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_172_; 
v_fst_152_ = lean_ctor_get(v_b_145_, 0);
v_snd_153_ = lean_ctor_get(v_b_145_, 1);
v_isSharedCheck_172_ = !lean_is_exclusive(v_b_145_);
if (v_isSharedCheck_172_ == 0)
{
v___x_155_ = v_b_145_;
v_isShared_156_ = v_isSharedCheck_172_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_snd_153_);
lean_inc(v_fst_152_);
lean_dec(v_b_145_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_172_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v_a_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v_a_157_ = lean_array_uget_borrowed(v_as_142_, v_i_144_);
v___x_158_ = lean_unsigned_to_nat(1u);
v___x_159_ = l_Lean_Syntax_getArg(v_a_157_, v___x_158_);
v___x_160_ = l_Lean_Syntax_getId(v___x_159_);
lean_dec(v___x_159_);
v___x_161_ = l_Lean_Name_eraseMacroScopes(v___x_160_);
lean_dec(v___x_160_);
v___x_162_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0___closed__1));
v___x_163_ = lean_name_eq(v___x_161_, v___x_162_);
lean_dec(v___x_161_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; lean_object* v___x_166_; 
lean_inc(v_a_157_);
v___x_164_ = lean_array_push(v_snd_153_, v_a_157_);
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 1, v___x_164_);
v___x_166_ = v___x_155_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_fst_152_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v___x_164_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
v_a_147_ = v___x_166_;
goto v___jp_146_;
}
}
else
{
lean_object* v___x_168_; lean_object* v___x_170_; 
lean_inc(v_a_157_);
v___x_168_ = lean_array_push(v_fst_152_, v_a_157_);
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 0, v___x_168_);
v___x_170_ = v___x_155_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_168_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v_snd_153_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
v_a_147_ = v___x_170_;
goto v___jp_146_;
}
}
}
}
v___jp_146_:
{
size_t v___x_148_; size_t v___x_149_; 
v___x_148_ = ((size_t)1ULL);
v___x_149_ = lean_usize_add(v_i_144_, v___x_148_);
v_i_144_ = v___x_149_;
v_b_145_ = v_a_147_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0___boxed(lean_object* v_as_173_, lean_object* v_sz_174_, lean_object* v_i_175_, lean_object* v_b_176_){
_start:
{
size_t v_sz_boxed_177_; size_t v_i_boxed_178_; lean_object* v_res_179_; 
v_sz_boxed_177_ = lean_unbox_usize(v_sz_174_);
lean_dec(v_sz_174_);
v_i_boxed_178_ = lean_unbox_usize(v_i_175_);
lean_dec(v_i_175_);
v_res_179_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0(v_as_173_, v_sz_boxed_177_, v_i_boxed_178_, v_b_176_);
lean_dec_ref(v_as_173_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection(lean_object* v_v_186_, lean_object* v_a_187_, lean_object* v_a_188_){
_start:
{
lean_object* v___x_189_; 
lean_inc(v_v_186_);
v___x_189_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f(v_v_186_);
if (lean_obj_tag(v___x_189_) == 1)
{
lean_object* v_val_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_267_; 
v_val_190_ = lean_ctor_get(v___x_189_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_189_);
if (v_isSharedCheck_267_ == 0)
{
v___x_192_ = v___x_189_;
v_isShared_193_ = v_isSharedCheck_267_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_val_190_);
lean_dec(v___x_189_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_267_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v_optWd_194_; uint8_t v___x_195_; 
lean_inc(v_v_186_);
v_optWd_194_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_getPath(v_v_186_, v_val_190_);
v___x_195_ = l_Lean_Syntax_isNone(v_optWd_194_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; lean_object* v_wd_197_; lean_object* v___x_198_; lean_object* v_optWf_199_; uint8_t v___x_200_; 
v___x_196_ = lean_unsigned_to_nat(0u);
v_wd_197_ = l_Lean_Syntax_getArg(v_optWd_194_, v___x_196_);
lean_dec(v_optWd_194_);
v___x_198_ = lean_unsigned_to_nat(2u);
v_optWf_199_ = l_Lean_Syntax_getArg(v_wd_197_, v___x_198_);
v___x_200_ = l_Lean_Syntax_isNone(v_optWf_199_);
if (v___x_200_ == 0)
{
lean_object* v_wf_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; size_t v_sz_205_; size_t v___x_206_; lean_object* v___x_207_; lean_object* v_fst_208_; lean_object* v_snd_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_260_; 
v_wf_201_ = l_Lean_Syntax_getArg(v_optWf_199_, v___x_196_);
lean_dec(v_optWf_199_);
v___x_202_ = l_Lean_Syntax_getArg(v_wf_201_, v___x_198_);
v___x_203_ = l_Lean_Syntax_getArgs(v___x_202_);
lean_dec(v___x_202_);
v___x_204_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__0));
v_sz_205_ = lean_array_size(v___x_203_);
v___x_206_ = ((size_t)0ULL);
v___x_207_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0(v___x_203_, v_sz_205_, v___x_206_, v___x_204_);
lean_dec_ref(v___x_203_);
v_fst_208_ = lean_ctor_get(v___x_207_, 0);
v_snd_209_ = lean_ctor_get(v___x_207_, 1);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_260_ == 0)
{
v___x_211_ = v___x_207_;
v_isShared_212_ = v_isSharedCheck_260_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_snd_209_);
lean_inc(v_fst_208_);
lean_dec(v___x_207_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_260_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_213_ = lean_array_get_size(v_fst_208_);
v___x_214_ = lean_nat_dec_eq(v___x_213_, v___x_196_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; lean_object* v___y_217_; lean_object* v___x_240_; uint8_t v___x_241_; 
v___x_215_ = lean_box(0);
v___x_240_ = lean_unsigned_to_nat(1u);
v___x_241_ = lean_nat_dec_lt(v___x_240_, v___x_213_);
if (v___x_241_ == 0)
{
v___y_217_ = v_a_188_;
goto v___jp_216_;
}
else
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_242_ = lean_array_fget_borrowed(v_fst_208_, v___x_240_);
v___x_243_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__3));
v___x_244_ = l_Lean_Macro_throwErrorAt___redArg(v___x_242_, v___x_243_, v_a_187_, v_a_188_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v_a_245_; 
v_a_245_ = lean_ctor_get(v___x_244_, 1);
lean_inc(v_a_245_);
lean_dec_ref_known(v___x_244_, 2);
v___y_217_ = v_a_245_;
goto v___jp_216_;
}
else
{
lean_object* v_a_246_; lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
lean_del_object(v___x_211_);
lean_dec(v_snd_209_);
lean_dec(v_fst_208_);
lean_dec(v_wf_201_);
lean_dec(v_wd_197_);
lean_del_object(v___x_192_);
lean_dec(v_val_190_);
lean_dec(v_v_186_);
v_a_246_ = lean_ctor_get(v___x_244_, 0);
v_a_247_ = lean_ctor_get(v___x_244_, 1);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_254_ == 0)
{
v___x_249_ = v___x_244_;
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_inc(v_a_246_);
lean_dec(v___x_244_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_252_; 
if (v_isShared_250_ == 0)
{
v___x_252_ = v___x_249_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_a_246_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v_a_247_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
v___jp_216_:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v_wf_x27_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_226_; 
v___x_218_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__2));
v___x_219_ = lean_box(2);
v___x_220_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
lean_ctor_set(v___x_220_, 1, v___x_218_);
lean_ctor_set(v___x_220_, 2, v_snd_209_);
v_wf_x27_221_ = l_Lean_Syntax_setArg(v_wf_201_, v___x_198_, v___x_220_);
v___x_222_ = lean_array_get(v___x_215_, v_fst_208_, v___x_196_);
lean_dec(v_fst_208_);
v___x_223_ = lean_unsigned_to_nat(3u);
v___x_224_ = l_Lean_Syntax_getArg(v___x_222_, v___x_223_);
lean_dec(v___x_222_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 0, v___x_224_);
v___x_226_ = v___x_192_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_224_);
v___x_226_ = v_reuseFailAlloc_239_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_227_ = lean_unsigned_to_nat(1u);
v___x_228_ = lean_mk_empty_array_with_capacity(v___x_227_);
lean_inc_ref(v___x_228_);
v___x_229_ = lean_array_push(v___x_228_, v_wf_x27_221_);
v___x_230_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_230_, 0, v___x_219_);
lean_ctor_set(v___x_230_, 1, v___x_218_);
lean_ctor_set(v___x_230_, 2, v___x_229_);
v___x_231_ = l_Lean_Syntax_setArg(v_wd_197_, v___x_198_, v___x_230_);
v___x_232_ = lean_array_push(v___x_228_, v___x_231_);
v___x_233_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_233_, 0, v___x_219_);
lean_ctor_set(v___x_233_, 1, v___x_218_);
lean_ctor_set(v___x_233_, 2, v___x_232_);
v___x_234_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_setPath(v_v_186_, v_val_190_, v___x_233_);
lean_dec_ref_known(v___x_233_, 3);
lean_dec(v_val_190_);
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 1, v___x_234_);
lean_ctor_set(v___x_211_, 0, v___x_226_);
v___x_236_ = v___x_211_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_226_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v___x_234_);
v___x_236_ = v_reuseFailAlloc_238_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v___x_237_; 
v___x_237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
lean_ctor_set(v___x_237_, 1, v___y_217_);
return v___x_237_;
}
}
}
}
else
{
lean_object* v___x_255_; lean_object* v___x_257_; 
lean_dec(v_snd_209_);
lean_dec(v_fst_208_);
lean_dec(v_wf_201_);
lean_dec(v_wd_197_);
lean_del_object(v___x_192_);
lean_dec(v_val_190_);
v___x_255_ = lean_box(0);
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 1, v_v_186_);
lean_ctor_set(v___x_211_, 0, v___x_255_);
v___x_257_ = v___x_211_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_255_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v_v_186_);
v___x_257_ = v_reuseFailAlloc_259_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
lean_object* v___x_258_; 
v___x_258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
lean_ctor_set(v___x_258_, 1, v_a_188_);
return v___x_258_;
}
}
}
}
else
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
lean_dec(v_optWf_199_);
lean_dec(v_wd_197_);
lean_del_object(v___x_192_);
lean_dec(v_val_190_);
v___x_261_ = lean_box(0);
v___x_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
lean_ctor_set(v___x_262_, 1, v_v_186_);
v___x_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v_a_188_);
return v___x_263_;
}
}
else
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
lean_dec(v_optWd_194_);
lean_del_object(v___x_192_);
lean_dec(v_val_190_);
v___x_264_ = lean_box(0);
v___x_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set(v___x_265_, 1, v_v_186_);
v___x_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
lean_ctor_set(v___x_266_, 1, v_a_188_);
return v___x_266_;
}
}
}
else
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
lean_dec(v___x_189_);
v___x_268_ = lean_box(0);
v___x_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
lean_ctor_set(v___x_269_, 1, v_v_186_);
v___x_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
lean_ctor_set(v___x_270_, 1, v_a_188_);
return v___x_270_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___boxed(lean_object* v_v_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection(v_v_271_, v_a_272_, v_a_273_);
lean_dec_ref(v_a_272_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice(lean_object* v_val_285_){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_286_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__1));
v___x_287_ = l_Lean_Syntax_getArgs(v_val_285_);
v___x_288_ = lean_array_pop(v___x_287_);
v___x_289_ = lean_box(2);
v___x_290_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__2));
v___x_291_ = lean_array_push(v___x_288_, v___x_290_);
v___x_292_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_292_, 0, v___x_289_);
lean_ctor_set(v___x_292_, 1, v___x_286_);
lean_ctor_set(v___x_292_, 2, v___x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___boxed(lean_object* v_val_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice(v_val_293_);
lean_dec(v_val_293_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___lam__0(lean_object* v_____do__lift_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
uint8_t v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_298_ = 0;
v___x_299_ = l_Lean_SourceInfo_fromRef(v_____do__lift_295_, v___x_298_);
v___x_300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
lean_ctor_set(v___x_300_, 1, v___y_297_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___lam__0___boxed(lean_object* v_____do__lift_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_Elab_Tactic_Do_expandDefContract___lam__0(v_____do__lift_301_, v___y_302_, v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v_____do__lift_301_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__3(lean_object* v_as_305_, size_t v_i_306_, size_t v_stop_307_, lean_object* v_b_308_){
_start:
{
uint8_t v___x_309_; 
v___x_309_ = lean_usize_dec_eq(v_i_306_, v_stop_307_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; size_t v___x_313_; size_t v___x_314_; 
v___x_310_ = lean_array_uget_borrowed(v_as_305_, v_i_306_);
lean_inc(v___x_310_);
v___x_311_ = l_Lean_Elab_Tactic_Do_contractBinderIdents(v___x_310_);
v___x_312_ = l_Array_append___redArg(v_b_308_, v___x_311_);
lean_dec_ref(v___x_311_);
v___x_313_ = ((size_t)1ULL);
v___x_314_ = lean_usize_add(v_i_306_, v___x_313_);
v_i_306_ = v___x_314_;
v_b_308_ = v___x_312_;
goto _start;
}
else
{
return v_b_308_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__3___boxed(lean_object* v_as_316_, lean_object* v_i_317_, lean_object* v_stop_318_, lean_object* v_b_319_){
_start:
{
size_t v_i_boxed_320_; size_t v_stop_boxed_321_; lean_object* v_res_322_; 
v_i_boxed_320_ = lean_unbox_usize(v_i_317_);
lean_dec(v_i_317_);
v_stop_boxed_321_ = lean_unbox_usize(v_stop_318_);
lean_dec(v_stop_318_);
v_res_322_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__3(v_as_316_, v_i_boxed_320_, v_stop_boxed_321_, v_b_319_);
lean_dec_ref(v_as_316_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__0(size_t v_sz_323_, size_t v_i_324_, lean_object* v_bs_325_){
_start:
{
uint8_t v___x_326_; 
v___x_326_ = lean_usize_dec_lt(v_i_324_, v_sz_323_);
if (v___x_326_ == 0)
{
return v_bs_325_;
}
else
{
lean_object* v_v_327_; lean_object* v___x_328_; lean_object* v_bs_x27_329_; size_t v___x_330_; size_t v___x_331_; lean_object* v___x_332_; 
v_v_327_ = lean_array_uget(v_bs_325_, v_i_324_);
v___x_328_ = lean_unsigned_to_nat(0u);
v_bs_x27_329_ = lean_array_uset(v_bs_325_, v_i_324_, v___x_328_);
v___x_330_ = ((size_t)1ULL);
v___x_331_ = lean_usize_add(v_i_324_, v___x_330_);
v___x_332_ = lean_array_uset(v_bs_x27_329_, v_i_324_, v_v_327_);
v_i_324_ = v___x_331_;
v_bs_325_ = v___x_332_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__0___boxed(lean_object* v_sz_334_, lean_object* v_i_335_, lean_object* v_bs_336_){
_start:
{
size_t v_sz_boxed_337_; size_t v_i_boxed_338_; lean_object* v_res_339_; 
v_sz_boxed_337_ = lean_unbox_usize(v_sz_334_);
lean_dec(v_sz_334_);
v_i_boxed_338_ = lean_unbox_usize(v_i_335_);
lean_dec(v_i_335_);
v_res_339_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__0(v_sz_boxed_337_, v_i_boxed_338_, v_bs_336_);
return v_res_339_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__11(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__10));
v___x_368_ = l_Lean_mkCIdent(v___x_367_);
return v___x_368_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__20(void){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_386_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__19));
v___x_387_ = l_String_toRawSubstring_x27(v___x_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2(lean_object* v_as_441_, size_t v_i_442_, size_t v_stop_443_, lean_object* v_b_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
uint8_t v___x_447_; 
v___x_447_ = lean_usize_dec_eq(v_i_442_, v_stop_443_);
if (v___x_447_ == 0)
{
lean_object* v_quotContext_448_; lean_object* v_currMacroScope_449_; lean_object* v_ref_450_; size_t v___x_451_; size_t v___x_452_; lean_object* v___y_454_; lean_object* v___x_458_; lean_object* v___x_459_; uint8_t v___x_460_; 
v_quotContext_448_ = lean_ctor_get(v___y_445_, 1);
v_currMacroScope_449_ = lean_ctor_get(v___y_445_, 2);
v_ref_450_ = lean_ctor_get(v___y_445_, 5);
v___x_451_ = ((size_t)1ULL);
v___x_452_ = lean_usize_sub(v_i_442_, v___x_451_);
v___x_458_ = lean_array_uget_borrowed(v_as_441_, v___x_452_);
v___x_459_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__1));
lean_inc(v___x_458_);
v___x_460_ = l_Lean_Syntax_isOfKind(v___x_458_, v___x_459_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; 
lean_dec(v_b_444_);
v___x_461_ = l_Lean_Macro_throwUnsupported___redArg(v___y_446_);
v___y_454_ = v___x_461_;
goto v___jp_453_;
}
else
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_462_ = lean_unsigned_to_nat(1u);
v___x_463_ = l_Lean_Syntax_getArg(v___x_458_, v___x_462_);
v___x_464_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__3));
lean_inc(v___x_463_);
v___x_465_ = l_Lean_Syntax_isOfKind(v___x_463_, v___x_464_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; 
lean_dec(v___x_463_);
lean_dec(v_b_444_);
v___x_466_ = l_Lean_Macro_throwUnsupported___redArg(v___y_446_);
v___y_454_ = v___x_466_;
goto v___jp_453_;
}
else
{
lean_object* v_ref_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v_ref_467_ = l_Lean_replaceRef(v___x_458_, v_ref_450_);
v___x_468_ = l_Lean_SourceInfo_fromRef(v_ref_467_, v___x_447_);
lean_dec(v_ref_467_);
v___x_469_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__7));
v___x_470_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__11, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__11);
v___x_471_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__2));
v___x_472_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__13));
v___x_473_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__15));
v___x_474_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__16));
lean_inc_n(v___x_468_, 9);
v___x_475_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_468_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
v___x_476_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__18));
v___x_477_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__20, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__20_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__20);
v___x_478_ = lean_box(0);
lean_inc(v_currMacroScope_449_);
lean_inc(v_quotContext_448_);
v___x_479_ = l_Lean_addMacroScope(v_quotContext_448_, v___x_478_, v_currMacroScope_449_);
v___x_480_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__39));
v___x_481_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_481_, 0, v___x_468_);
lean_ctor_set(v___x_481_, 1, v___x_477_);
lean_ctor_set(v___x_481_, 2, v___x_479_);
lean_ctor_set(v___x_481_, 3, v___x_480_);
v___x_482_ = l_Lean_Syntax_node1(v___x_468_, v___x_476_, v___x_481_);
v___x_483_ = l_Lean_Syntax_node2(v___x_468_, v___x_473_, v___x_475_, v___x_482_);
v___x_484_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__40));
v___x_485_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__41));
v___x_486_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_468_);
lean_ctor_set(v___x_486_, 1, v___x_484_);
v___x_487_ = l_Lean_Syntax_node2(v___x_468_, v___x_485_, v___x_486_, v___x_463_);
v___x_488_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__42));
v___x_489_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_468_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
v___x_490_ = l_Lean_Syntax_node3(v___x_468_, v___x_472_, v___x_483_, v___x_487_, v___x_489_);
v___x_491_ = l_Lean_Syntax_node2(v___x_468_, v___x_471_, v___x_490_, v_b_444_);
v___x_492_ = l_Lean_Syntax_node2(v___x_468_, v___x_469_, v___x_470_, v___x_491_);
v_i_442_ = v___x_452_;
v_b_444_ = v___x_492_;
goto _start;
}
}
v___jp_453_:
{
if (lean_obj_tag(v___y_454_) == 0)
{
lean_object* v_a_455_; lean_object* v_a_456_; 
v_a_455_ = lean_ctor_get(v___y_454_, 0);
lean_inc(v_a_455_);
v_a_456_ = lean_ctor_get(v___y_454_, 1);
lean_inc(v_a_456_);
lean_dec_ref_known(v___y_454_, 2);
v_i_442_ = v___x_452_;
v_b_444_ = v_a_455_;
v___y_446_ = v_a_456_;
goto _start;
}
else
{
return v___y_454_;
}
}
}
else
{
lean_object* v___x_494_; 
v___x_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_494_, 0, v_b_444_);
lean_ctor_set(v___x_494_, 1, v___y_446_);
return v___x_494_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___boxed(lean_object* v_as_495_, lean_object* v_i_496_, lean_object* v_stop_497_, lean_object* v_b_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
size_t v_i_boxed_501_; size_t v_stop_boxed_502_; lean_object* v_res_503_; 
v_i_boxed_501_ = lean_unbox_usize(v_i_496_);
lean_dec(v_i_496_);
v_stop_boxed_502_ = lean_unbox_usize(v_stop_497_);
lean_dec(v_stop_497_);
v_res_503_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2(v_as_495_, v_i_boxed_501_, v_stop_boxed_502_, v_b_498_, v___y_499_, v___y_500_);
lean_dec_ref(v___y_499_);
lean_dec_ref(v_as_495_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__1(size_t v_sz_504_, size_t v_i_505_, lean_object* v_bs_506_){
_start:
{
uint8_t v___x_507_; 
v___x_507_ = lean_usize_dec_lt(v_i_505_, v_sz_504_);
if (v___x_507_ == 0)
{
return v_bs_506_;
}
else
{
lean_object* v_v_508_; lean_object* v___x_509_; lean_object* v_bs_x27_510_; size_t v___x_511_; size_t v___x_512_; lean_object* v___x_513_; 
v_v_508_ = lean_array_uget(v_bs_506_, v_i_505_);
v___x_509_ = lean_unsigned_to_nat(0u);
v_bs_x27_510_ = lean_array_uset(v_bs_506_, v_i_505_, v___x_509_);
v___x_511_ = ((size_t)1ULL);
v___x_512_ = lean_usize_add(v_i_505_, v___x_511_);
v___x_513_ = lean_array_uset(v_bs_x27_510_, v_i_505_, v_v_508_);
v_i_505_ = v___x_512_;
v_bs_506_ = v___x_513_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__1___boxed(lean_object* v_sz_515_, lean_object* v_i_516_, lean_object* v_bs_517_){
_start:
{
size_t v_sz_boxed_518_; size_t v_i_boxed_519_; lean_object* v_res_520_; 
v_sz_boxed_518_ = lean_unbox_usize(v_sz_515_);
lean_dec(v_sz_515_);
v_i_boxed_519_ = lean_unbox_usize(v_i_516_);
lean_dec(v_i_516_);
v_res_520_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__1(v_sz_boxed_518_, v_i_boxed_519_, v_bs_517_);
return v_res_520_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__5(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__4));
v___x_527_ = l_String_toRawSubstring_x27(v___x_526_);
return v___x_527_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__7(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__6));
v___x_530_ = l_String_toRawSubstring_x27(v___x_529_);
return v___x_530_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__49(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__48));
v___x_574_ = l_Lean_mkAtom(v___x_573_);
return v___x_574_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__53(void){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Array_mkArray0___redArg();
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_expandDefContract(lean_object* v_stx_628_, lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v_specTac_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; size_t v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v_a_869_; lean_object* v_a_870_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; size_t v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v_post_985_; lean_object* v___y_986_; lean_object* v_ref_987_; lean_object* v___y_988_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; size_t v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1037_; lean_object* v_post_1038_; lean_object* v___y_1039_; lean_object* v___y_1040_; lean_object* v___x_1042_; lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; size_t v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; lean_object* v___y_1057_; lean_object* v___y_1058_; uint8_t v___y_1059_; lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v_pre_1062_; lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1134_; size_t v___y_1135_; lean_object* v___y_1136_; lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; uint8_t v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v___y_1193_; uint8_t v___y_1194_; lean_object* v___y_1195_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v_decl_1207_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1268_; lean_object* v___y_1269_; lean_object* v___y_1270_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___x_1360_; uint8_t v___x_1361_; 
v___x_1042_ = lean_unsigned_to_nat(1u);
v_decl_1207_ = l_Lean_Syntax_getArg(v_stx_628_, v___x_1042_);
v___x_1360_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__77));
lean_inc(v_decl_1207_);
v___x_1361_ = l_Lean_Syntax_isOfKind(v_decl_1207_, v___x_1360_);
if (v___x_1361_ == 0)
{
lean_object* v___x_1362_; 
v___x_1362_ = l_Lean_Macro_throwUnsupported___redArg(v_a_630_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v_a_1363_; 
v_a_1363_ = lean_ctor_get(v___x_1362_, 1);
lean_inc(v_a_1363_);
lean_dec_ref_known(v___x_1362_, 2);
v___y_1343_ = v_a_629_;
v___y_1344_ = v_a_1363_;
goto v___jp_1342_;
}
else
{
lean_object* v_a_1364_; lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
lean_dec(v_decl_1207_);
lean_dec(v_stx_628_);
v_a_1364_ = lean_ctor_get(v___x_1362_, 0);
v_a_1365_ = lean_ctor_get(v___x_1362_, 1);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1362_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_inc(v_a_1364_);
lean_dec(v___x_1362_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1364_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v_a_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
else
{
v___y_1343_ = v_a_629_;
v___y_1344_ = v_a_630_;
goto v___jp_1342_;
}
v___jp_631_:
{
lean_object* v_quotContext_655_; lean_object* v_currMacroScope_656_; lean_object* v_ref_657_; lean_object* v___x_658_; lean_object* v_a_659_; lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_846_; 
v_quotContext_655_ = lean_ctor_get(v___y_653_, 1);
v_currMacroScope_656_ = lean_ctor_get(v___y_653_, 2);
v_ref_657_ = lean_ctor_get(v___y_653_, 5);
v___x_658_ = l_Lean_Elab_Tactic_Do_expandDefContract___lam__0(v_ref_657_, v___y_653_, v___y_654_);
v_a_659_ = lean_ctor_get(v___x_658_, 0);
v_a_660_ = lean_ctor_get(v___x_658_, 1);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_846_ == 0)
{
v___x_662_ = v___x_658_;
v_isShared_663_ = v_isSharedCheck_846_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_inc(v_a_659_);
lean_dec(v___x_658_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_846_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_844_; 
v___x_664_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__0));
v___x_665_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__0));
lean_inc_ref_n(v___y_649_, 30);
lean_inc_ref_n(v___y_634_, 32);
v___x_666_ = l_Lean_Name_mkStr4(v___y_634_, v___y_649_, v___x_664_, v___x_665_);
v___x_667_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__1));
v___x_668_ = l_Lean_Name_mkStr4(v___y_634_, v___y_649_, v___x_664_, v___x_667_);
lean_inc_n(v_a_659_, 76);
v___x_669_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_669_, 0, v_a_659_);
lean_ctor_set(v___x_669_, 1, v___x_667_);
v___x_670_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__2));
v___x_671_ = l_Lean_Name_mkStr4(v___y_634_, v___y_649_, v___x_664_, v___x_670_);
v___x_672_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__3));
v___x_673_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_673_, 0, v_a_659_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
v___x_674_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_expandDefContract___closed__5, &l_Lean_Elab_Tactic_Do_expandDefContract___closed__5_once, _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__5);
lean_inc_ref(v___y_640_);
lean_inc_ref(v___y_635_);
v___x_675_ = l_Lean_Name_mkStr2(v___y_635_, v___y_640_);
lean_inc_n(v_currMacroScope_656_, 2);
lean_inc(v___x_675_);
lean_inc_n(v_quotContext_655_, 2);
v___x_676_ = l_Lean_addMacroScope(v_quotContext_655_, v___x_675_, v_currMacroScope_656_);
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_675_);
v___x_678_ = lean_box(0);
v___x_679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_677_);
lean_ctor_set(v___x_679_, 1, v___x_678_);
v___x_680_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_680_, 0, v_a_659_);
lean_ctor_set(v___x_680_, 1, v___x_674_);
lean_ctor_set(v___x_680_, 2, v___x_676_);
lean_ctor_set(v___x_680_, 3, v___x_679_);
v___x_681_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_expandDefContract___closed__7, &l_Lean_Elab_Tactic_Do_expandDefContract___closed__7_once, _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__7);
lean_inc_ref(v___y_648_);
v___x_682_ = l_Lean_Name_mkStr2(v___y_634_, v___y_648_);
lean_inc(v___x_682_);
v___x_683_ = l_Lean_addMacroScope(v_quotContext_655_, v___x_682_, v_currMacroScope_656_);
v___x_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_684_, 0, v___x_682_);
v___x_685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_684_);
lean_ctor_set(v___x_685_, 1, v___x_678_);
v___x_686_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_686_, 0, v_a_659_);
lean_ctor_set(v___x_686_, 1, v___x_681_);
lean_ctor_set(v___x_686_, 2, v___x_683_);
lean_ctor_set(v___x_686_, 3, v___x_685_);
lean_inc_n(v___y_636_, 17);
v___x_687_ = l_Lean_Syntax_node2(v_a_659_, v___y_636_, v___x_680_, v___x_686_);
v___x_688_ = l_Lean_Syntax_node2(v_a_659_, v___x_671_, v___x_673_, v___x_687_);
v___x_689_ = l_Lean_Syntax_node2(v_a_659_, v___x_668_, v___x_669_, v___x_688_);
v___x_690_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_690_, 0, v_a_659_);
lean_ctor_set(v___x_690_, 1, v___x_665_);
v___x_691_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__8));
v___x_692_ = l_Lean_Name_mkStr4(v___y_634_, v___y_649_, v___x_664_, v___x_691_);
v___x_693_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__9));
v___x_694_ = l_Lean_Name_mkStr4(v___y_634_, v___y_649_, v___x_664_, v___x_693_);
lean_inc_ref(v___y_643_);
v___x_695_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_695_, 0, v_a_659_);
lean_ctor_set(v___x_695_, 1, v___y_636_);
lean_ctor_set(v___x_695_, 2, v___y_643_);
v___x_696_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__10));
lean_inc_ref_n(v___y_639_, 4);
v___x_697_ = l_Lean_Name_mkStr4(v___y_634_, v___y_649_, v___y_639_, v___x_696_);
v___x_698_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__11));
v___x_699_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_699_, 0, v_a_659_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
v___x_700_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__12));
v___x_701_ = l_Lean_Name_mkStr4(v___y_634_, v___y_649_, v___y_639_, v___x_700_);
v___x_702_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__13));
v___x_703_ = l_Lean_Name_mkStr4(v___y_634_, v___y_649_, v___y_639_, v___x_702_);
lean_inc_ref_n(v___x_695_, 24);
v___x_704_ = l_Lean_Syntax_node1(v_a_659_, v___x_703_, v___x_695_);
v___x_705_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__14));
lean_inc_ref_n(v___y_638_, 2);
v___x_706_ = l_Lean_Name_mkStr4(v___y_634_, v___y_649_, v___x_705_, v___y_638_);
v___x_707_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_707_, 0, v_a_659_);
lean_ctor_set(v___x_707_, 1, v___y_638_);
v___x_708_ = l_Lean_Syntax_node2(v_a_659_, v___x_706_, v___x_707_, v___x_695_);
v___x_709_ = l_Lean_Syntax_node2(v_a_659_, v___x_701_, v___x_704_, v___x_708_);
v___x_710_ = l_Lean_Syntax_node1(v_a_659_, v___y_636_, v___x_709_);
v___x_711_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__15));
v___x_712_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_712_, 0, v_a_659_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
lean_inc_ref(v___x_712_);
v___x_713_ = l_Lean_Syntax_node3(v_a_659_, v___x_697_, v___x_699_, v___x_710_, v___x_712_);
v___x_714_ = l_Lean_Syntax_node1(v_a_659_, v___y_636_, v___x_713_);
v___x_715_ = l_Lean_Syntax_node7(v_a_659_, v___x_694_, v___x_695_, v___x_714_, v___x_695_, v___x_695_, v___x_695_, v___x_695_, v___x_695_);
v___x_716_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__16));
v___x_717_ = l_Lean_Name_mkStr4(v___y_634_, v___y_649_, v___x_664_, v___x_716_);
v___x_718_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_718_, 0, v_a_659_);
lean_ctor_set(v___x_718_, 1, v___x_716_);
v___x_719_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__17));
v___x_720_ = l_Lean_Name_mkStr4(v___y_634_, v___y_649_, v___x_664_, v___x_719_);
v___x_721_ = lean_mk_empty_array_with_capacity(v___y_637_);
lean_inc_n(v___y_650_, 2);
v___x_722_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_722_, 0, v___y_650_);
lean_ctor_set(v___x_722_, 1, v___y_636_);
lean_ctor_set(v___x_722_, 2, v___x_721_);
v___x_723_ = lean_array_push(v___y_632_, v___y_644_);
v___x_724_ = lean_array_push(v___x_723_, v___x_722_);
v___x_725_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_725_, 0, v___y_650_);
lean_ctor_set(v___x_725_, 1, v___x_720_);
lean_ctor_set(v___x_725_, 2, v___x_724_);
v___x_726_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__18));
v___x_727_ = l_Lean_Name_mkStr4(v___y_634_, v___y_649_, v___x_664_, v___x_726_);
v___x_728_ = l_Array_append___redArg(v___y_643_, v___y_646_);
lean_dec_ref(v___y_646_);
v___x_729_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_729_, 0, v_a_659_);
lean_ctor_set(v___x_729_, 1, v___y_636_);
lean_ctor_set(v___x_729_, 2, v___x_728_);
v___x_730_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__19));
v___x_731_ = l_Lean_Name_mkStr4(v___y_634_, v___y_649_, v___y_639_, v___x_730_);
v___x_732_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__20));
v___x_733_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_733_, 0, v_a_659_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
v___x_734_ = l_Lean_Syntax_node2(v_a_659_, v___x_731_, v___x_733_, v___y_642_);
v___x_735_ = l_Lean_Syntax_node2(v_a_659_, v___x_727_, v___x_729_, v___x_734_);
v___x_736_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__1));
v___x_737_ = l_Lean_Name_mkStr4(v___y_634_, v___y_649_, v___x_664_, v___x_736_);
v___x_738_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__21));
v___x_739_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_739_, 0, v_a_659_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
v___x_740_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__22));
v___x_741_ = l_Lean_Name_mkStr4(v___y_634_, v___y_649_, v___y_639_, v___x_740_);
v___x_742_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__23));
v___x_743_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_743_, 0, v_a_659_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v___x_744_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__22));
v___x_745_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__24));
v___x_746_ = l_Lean_Name_mkStr4(v___y_634_, v___y_649_, v___x_744_, v___x_745_);
v___x_747_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__25));
v___x_748_ = l_Lean_Name_mkStr4(v___y_634_, v___y_649_, v___x_744_, v___x_747_);
v___x_749_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__26));
v___x_750_ = l_Lean_Name_mkStr4(v___y_634_, v___y_649_, v___x_744_, v___x_749_);
v___x_751_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_751_, 0, v_a_659_);
lean_ctor_set(v___x_751_, 1, v___x_749_);
v___x_752_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__27));
v___x_753_ = l_Lean_Name_mkStr4(v___y_634_, v___y_649_, v___x_744_, v___x_752_);
v___x_754_ = l_Lean_Syntax_node1(v_a_659_, v___x_753_, v___x_695_);
v___x_755_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__28));
v___x_756_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_756_, 0, v_a_659_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
v___x_757_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__29));
v___x_758_ = l_Lean_Name_mkStr4(v___y_634_, v___y_649_, v___x_744_, v___x_757_);
v___x_759_ = l_Lean_Syntax_node3(v_a_659_, v___x_758_, v___x_695_, v___x_695_, v___y_645_);
v___x_760_ = l_Lean_Syntax_node1(v_a_659_, v___y_636_, v___x_759_);
v___x_761_ = l_Lean_Syntax_node3(v_a_659_, v___y_636_, v___x_756_, v___x_760_, v___x_712_);
v___x_762_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__30));
v___x_763_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_763_, 0, v_a_659_);
lean_ctor_set(v___x_763_, 1, v___x_762_);
v___x_764_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__31));
v___x_765_ = l_Lean_Name_mkStr4(v___y_634_, v___y_649_, v___x_744_, v___x_764_);
v___x_766_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__32));
v___x_767_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__12));
v___x_768_ = l_Lean_Name_mkStr5(v___y_634_, v___y_649_, v___x_744_, v___x_766_, v___x_767_);
v___x_769_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__16));
v___x_770_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_770_, 0, v_a_659_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
v___x_771_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__33));
v___x_772_ = l_Lean_Name_mkStr5(v___y_634_, v___y_649_, v___x_744_, v___x_766_, v___x_771_);
v___x_773_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__34));
v___x_774_ = l_Lean_Name_mkStr5(v___y_634_, v___y_649_, v___x_744_, v___x_766_, v___x_773_);
v___x_775_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__35));
v___x_776_ = l_Lean_Name_mkStr5(v___y_634_, v___y_649_, v___x_744_, v___x_766_, v___x_775_);
v___x_777_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__36));
v___x_778_ = l_Lean_Name_mkStr5(v___y_634_, v___y_649_, v___x_744_, v___x_766_, v___x_777_);
v___x_779_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__37));
v___x_780_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_780_, 0, v_a_659_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
v___x_781_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__38));
v___x_782_ = l_Lean_Name_mkStr5(v___y_634_, v___y_649_, v___x_744_, v___x_766_, v___x_781_);
v___x_783_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_783_, 0, v_a_659_);
lean_ctor_set(v___x_783_, 1, v___x_781_);
v___x_784_ = l_Lean_Syntax_node4(v_a_659_, v___x_782_, v___x_783_, v___x_695_, v___x_695_, v___x_695_);
lean_inc(v___x_776_);
v___x_785_ = l_Lean_Syntax_node2(v_a_659_, v___x_776_, v___x_784_, v___x_695_);
v___x_786_ = l_Lean_Syntax_node1(v_a_659_, v___y_636_, v___x_785_);
lean_inc(v___x_774_);
v___x_787_ = l_Lean_Syntax_node1(v_a_659_, v___x_774_, v___x_786_);
lean_inc(v___x_772_);
v___x_788_ = l_Lean_Syntax_node1(v_a_659_, v___x_772_, v___x_787_);
v___x_789_ = l_Lean_Syntax_node2(v_a_659_, v___x_778_, v___x_780_, v___x_788_);
v___x_790_ = l_Lean_Syntax_node2(v_a_659_, v___x_776_, v___x_789_, v___x_695_);
v___x_791_ = l_Lean_Syntax_node1(v_a_659_, v___y_636_, v___x_790_);
v___x_792_ = l_Lean_Syntax_node1(v_a_659_, v___x_774_, v___x_791_);
v___x_793_ = l_Lean_Syntax_node1(v_a_659_, v___x_772_, v___x_792_);
v___x_794_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__42));
v___x_795_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_795_, 0, v_a_659_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
v___x_796_ = l_Lean_Syntax_node3(v_a_659_, v___x_768_, v___x_770_, v___x_793_, v___x_795_);
v___x_797_ = l_Lean_Syntax_node1(v_a_659_, v___x_765_, v___x_796_);
v___x_798_ = l_Lean_Syntax_node2(v_a_659_, v___y_636_, v___x_763_, v___x_797_);
v___x_799_ = l_Lean_Syntax_node8(v_a_659_, v___x_750_, v___x_751_, v___x_754_, v___x_761_, v___x_695_, v___x_695_, v___x_695_, v___x_695_, v___x_798_);
v___x_800_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__39));
v___x_801_ = l_Lean_Name_mkStr4(v___y_634_, v___y_649_, v___x_744_, v___x_800_);
v___x_802_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_802_, 0, v_a_659_);
lean_ctor_set(v___x_802_, 1, v___x_800_);
v___x_803_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__41));
v___x_804_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__42));
v___x_805_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_805_, 0, v_a_659_);
lean_ctor_set(v___x_805_, 1, v___x_804_);
v___x_806_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__43));
v___x_807_ = l_Lean_Name_mkStr4(v___y_634_, v___y_649_, v___x_744_, v___x_806_);
v___x_808_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_808_, 0, v_a_659_);
lean_ctor_set(v___x_808_, 1, v___x_806_);
v___x_809_ = l_Lean_Syntax_node1(v_a_659_, v___x_807_, v___x_808_);
v___x_810_ = l_Lean_Syntax_node1(v_a_659_, v___y_636_, v___x_809_);
lean_inc_n(v___x_748_, 2);
v___x_811_ = l_Lean_Syntax_node1(v_a_659_, v___x_748_, v___x_810_);
lean_inc_n(v___x_746_, 2);
v___x_812_ = l_Lean_Syntax_node1(v_a_659_, v___x_746_, v___x_811_);
lean_inc_ref(v___x_805_);
v___x_813_ = l_Lean_Syntax_node2(v_a_659_, v___x_803_, v___x_805_, v___x_812_);
v___x_814_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__44));
v___x_815_ = l_Lean_Name_mkStr4(v___y_634_, v___y_649_, v___x_744_, v___x_814_);
v___x_816_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_816_, 0, v_a_659_);
lean_ctor_set(v___x_816_, 1, v___x_814_);
v___x_817_ = l_Lean_Syntax_node1(v_a_659_, v___y_636_, v___y_641_);
v___x_818_ = l_Lean_Syntax_node2(v_a_659_, v___x_815_, v___x_816_, v___x_817_);
v___x_819_ = l_Lean_Syntax_node1(v_a_659_, v___y_636_, v___x_818_);
v___x_820_ = l_Lean_Syntax_node1(v_a_659_, v___x_748_, v___x_819_);
v___x_821_ = l_Lean_Syntax_node1(v_a_659_, v___x_746_, v___x_820_);
v___x_822_ = l_Lean_Syntax_node2(v_a_659_, v___x_803_, v___x_805_, v___x_821_);
v___x_823_ = l_Lean_Syntax_node2(v_a_659_, v___y_636_, v___x_813_, v___x_822_);
v___x_824_ = l_Lean_Syntax_node2(v_a_659_, v___x_801_, v___x_802_, v___x_823_);
v___x_825_ = l_Lean_Syntax_node5(v_a_659_, v___y_636_, v___x_799_, v___x_695_, v_specTac_652_, v___x_695_, v___x_824_);
v___x_826_ = l_Lean_Syntax_node1(v_a_659_, v___x_748_, v___x_825_);
v___x_827_ = l_Lean_Syntax_node1(v_a_659_, v___x_746_, v___x_826_);
v___x_828_ = l_Lean_Syntax_node2(v_a_659_, v___x_741_, v___x_743_, v___x_827_);
v___x_829_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__45));
v___x_830_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__46));
v___x_831_ = l_Lean_Name_mkStr4(v___y_634_, v___y_649_, v___x_829_, v___x_830_);
v___x_832_ = l_Lean_Syntax_node2(v_a_659_, v___x_831_, v___x_695_, v___x_695_);
v___x_833_ = l_Lean_Syntax_node4(v_a_659_, v___x_737_, v___x_739_, v___x_828_, v___x_832_, v___x_695_);
v___x_834_ = l_Lean_Syntax_node4(v_a_659_, v___x_717_, v___x_718_, v___x_725_, v___x_735_, v___x_833_);
v___x_835_ = l_Lean_Syntax_node2(v_a_659_, v___x_692_, v___x_715_, v___x_834_);
v___x_836_ = l_Lean_Syntax_node3(v_a_659_, v___x_666_, v___x_689_, v___x_690_, v___x_835_);
v___x_837_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice(v___y_647_);
lean_dec(v___y_647_);
v___x_838_ = lean_mk_empty_array_with_capacity(v___y_651_);
v___x_839_ = lean_array_push(v___x_838_, v___x_837_);
v___x_840_ = lean_array_push(v___x_839_, v___y_633_);
v___x_841_ = lean_array_push(v___x_840_, v___x_836_);
v___x_842_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_842_, 0, v___y_650_);
lean_ctor_set(v___x_842_, 1, v___y_636_);
lean_ctor_set(v___x_842_, 2, v___x_841_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 0, v___x_842_);
v___x_844_ = v___x_662_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_842_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v_a_660_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
v___jp_847_:
{
lean_object* v___x_871_; lean_object* v_a_872_; lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_966_; 
v___x_871_ = l_Lean_Elab_Tactic_Do_expandDefContract___lam__0(v___y_851_, v___y_848_, v_a_870_);
v_a_872_ = lean_ctor_get(v___x_871_, 0);
v_a_873_ = lean_ctor_get(v___x_871_, 1);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_966_ == 0)
{
v___x_875_ = v___x_871_;
v_isShared_876_ = v_isSharedCheck_966_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_inc(v_a_872_);
lean_dec(v___x_871_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_966_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_891_; 
v___x_877_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1));
v___x_878_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__2));
v___x_879_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__47));
lean_inc_ref(v___y_852_);
v___x_880_ = l_Lean_Name_mkStr4(v___y_852_, v___x_877_, v___x_878_, v___x_879_);
v___x_881_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_expandDefContract___closed__49, &l_Lean_Elab_Tactic_Do_expandDefContract___closed__49_once, _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__49);
v___x_882_ = lean_mk_empty_array_with_capacity(v___y_867_);
lean_inc_ref(v___x_882_);
v___x_883_ = lean_array_push(v___x_882_, v___x_881_);
v___x_884_ = lean_array_push(v___x_883_, v_a_869_);
v___x_885_ = lean_box(2);
v___x_886_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
lean_ctor_set(v___x_886_, 1, v___x_880_);
lean_ctor_set(v___x_886_, 2, v___x_884_);
v___x_887_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__50));
lean_inc_ref(v___y_857_);
lean_inc_ref(v___y_853_);
v___x_888_ = l_Lean_Name_mkStr3(v___y_853_, v___y_857_, v___x_887_);
v___x_889_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__51));
lean_inc(v_a_872_);
if (v_isShared_876_ == 0)
{
lean_ctor_set_tag(v___x_875_, 2);
lean_ctor_set(v___x_875_, 1, v___x_889_);
v___x_891_ = v___x_875_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_a_872_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v___x_889_);
v___x_891_ = v_reuseFailAlloc_965_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; size_t v_sz_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_892_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__52));
lean_inc_n(v_a_872_, 5);
v___x_893_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_893_, 0, v_a_872_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
v___x_894_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__2));
v___x_895_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_expandDefContract___closed__53, &l_Lean_Elab_Tactic_Do_expandDefContract___closed__53_once, _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__53);
v___x_896_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_896_, 0, v_a_872_);
lean_ctor_set(v___x_896_, 1, v___x_894_);
lean_ctor_set(v___x_896_, 2, v___x_895_);
v___x_897_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__6));
lean_inc_ref(v___y_852_);
v___x_898_ = l_Lean_Name_mkStr4(v___y_852_, v___x_877_, v___x_878_, v___x_897_);
v_sz_899_ = lean_array_size(v___y_861_);
v___x_900_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__1(v_sz_899_, v___y_858_, v___y_861_);
v___x_901_ = l_Array_append___redArg(v___x_895_, v___x_900_);
lean_dec_ref(v___x_900_);
v___x_902_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_902_, 0, v_a_872_);
lean_ctor_set(v___x_902_, 1, v___x_894_);
lean_ctor_set(v___x_902_, 2, v___x_901_);
lean_inc(v___y_863_);
v___x_903_ = l_Lean_Syntax_node2(v_a_872_, v___x_898_, v___y_863_, v___x_902_);
v___x_904_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__54));
v___x_905_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_905_, 0, v_a_872_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___x_906_ = lean_unsigned_to_nat(10u);
v___x_907_ = lean_mk_empty_array_with_capacity(v___x_906_);
lean_inc_ref(v___x_891_);
v___x_908_ = lean_array_push(v___x_907_, v___x_891_);
v___x_909_ = lean_array_push(v___x_908_, v___y_849_);
lean_inc_ref(v___x_893_);
v___x_910_ = lean_array_push(v___x_909_, v___x_893_);
v___x_911_ = lean_array_push(v___x_910_, v___x_896_);
v___x_912_ = lean_array_push(v___x_911_, v___x_903_);
v___x_913_ = lean_array_push(v___x_912_, v___x_891_);
v___x_914_ = lean_array_push(v___x_913_, v___y_856_);
v___x_915_ = lean_array_push(v___x_914_, v___x_905_);
v___x_916_ = lean_array_push(v___x_915_, v___x_886_);
v___x_917_ = lean_array_push(v___x_916_, v___x_893_);
v___x_918_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_918_, 0, v_a_872_);
lean_ctor_set(v___x_918_, 1, v___x_888_);
lean_ctor_set(v___x_918_, 2, v___x_917_);
if (lean_obj_tag(v___y_860_) == 0)
{
lean_object* v___x_919_; lean_object* v_a_920_; lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_939_; 
v___x_919_ = l_Lean_Elab_Tactic_Do_expandDefContract___lam__0(v___y_851_, v___y_848_, v_a_873_);
v_a_920_ = lean_ctor_get(v___x_919_, 0);
v_a_921_ = lean_ctor_get(v___x_919_, 1);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_939_ == 0)
{
v___x_923_ = v___x_919_;
v_isShared_924_ = v_isSharedCheck_939_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_inc(v_a_920_);
lean_dec(v___x_919_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_939_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_925_; uint8_t v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_936_; 
v___x_925_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__55));
v___x_926_ = 1;
v___x_927_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_862_, v___x_926_);
v___x_928_ = lean_string_append(v___x_925_, v___x_927_);
lean_dec_ref(v___x_927_);
v___x_929_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__56));
v___x_930_ = lean_string_append(v___x_928_, v___x_929_);
v___x_931_ = l_Lean_Syntax_mkStrLit(v___x_930_, v___x_885_);
v___x_932_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__22));
v___x_933_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__57));
lean_inc_ref(v___y_852_);
v___x_934_ = l_Lean_Name_mkStr4(v___y_852_, v___x_877_, v___x_932_, v___x_933_);
lean_inc(v_a_920_);
if (v_isShared_924_ == 0)
{
lean_ctor_set_tag(v___x_923_, 2);
lean_ctor_set(v___x_923_, 1, v___x_933_);
v___x_936_ = v___x_923_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_a_920_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v___x_933_);
v___x_936_ = v_reuseFailAlloc_938_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
lean_object* v___x_937_; 
v___x_937_ = l_Lean_Syntax_node1(v_a_920_, v___x_934_, v___x_936_);
v___y_632_ = v___x_882_;
v___y_633_ = v___y_850_;
v___y_634_ = v___y_852_;
v___y_635_ = v___y_853_;
v___y_636_ = v___x_894_;
v___y_637_ = v___y_854_;
v___y_638_ = v___y_855_;
v___y_639_ = v___x_878_;
v___y_640_ = v___y_857_;
v___y_641_ = v___x_931_;
v___y_642_ = v___x_918_;
v___y_643_ = v___x_895_;
v___y_644_ = v___y_859_;
v___y_645_ = v___y_863_;
v___y_646_ = v___y_864_;
v___y_647_ = v___y_865_;
v___y_648_ = v___y_866_;
v___y_649_ = v___x_877_;
v___y_650_ = v___x_885_;
v___y_651_ = v___y_868_;
v_specTac_652_ = v___x_937_;
v___y_653_ = v___y_848_;
v___y_654_ = v_a_921_;
goto v___jp_631_;
}
}
}
else
{
lean_object* v_val_940_; lean_object* v___x_941_; lean_object* v_a_942_; lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_964_; 
v_val_940_ = lean_ctor_get(v___y_860_, 0);
lean_inc(v_val_940_);
lean_dec_ref_known(v___y_860_, 1);
v___x_941_ = l_Lean_Elab_Tactic_Do_expandDefContract___lam__0(v___y_851_, v___y_848_, v_a_873_);
v_a_942_ = lean_ctor_get(v___x_941_, 0);
v_a_943_ = lean_ctor_get(v___x_941_, 1);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_964_ == 0)
{
v___x_945_ = v___x_941_;
v_isShared_946_ = v_isSharedCheck_964_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_inc(v_a_942_);
lean_dec(v___x_941_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_964_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
uint8_t v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_959_; 
v___x_947_ = 1;
v___x_948_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__55));
v___x_949_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_862_, v___x_947_);
v___x_950_ = lean_string_append(v___x_948_, v___x_949_);
lean_dec_ref(v___x_949_);
v___x_951_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__58));
v___x_952_ = lean_string_append(v___x_950_, v___x_951_);
v___x_953_ = l_Lean_Syntax_mkStrLit(v___x_952_, v___x_885_);
v___x_954_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__22));
v___x_955_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__12));
lean_inc_ref(v___y_852_);
v___x_956_ = l_Lean_Name_mkStr4(v___y_852_, v___x_877_, v___x_954_, v___x_955_);
v___x_957_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__16));
lean_inc(v_a_942_);
if (v_isShared_946_ == 0)
{
lean_ctor_set_tag(v___x_945_, 2);
lean_ctor_set(v___x_945_, 1, v___x_957_);
v___x_959_ = v___x_945_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_942_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v___x_957_);
v___x_959_ = v_reuseFailAlloc_963_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_960_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__42));
lean_inc(v_a_942_);
v___x_961_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_961_, 0, v_a_942_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
v___x_962_ = l_Lean_Syntax_node3(v_a_942_, v___x_956_, v___x_959_, v_val_940_, v___x_961_);
v___y_632_ = v___x_882_;
v___y_633_ = v___y_850_;
v___y_634_ = v___y_852_;
v___y_635_ = v___y_853_;
v___y_636_ = v___x_894_;
v___y_637_ = v___y_854_;
v___y_638_ = v___y_855_;
v___y_639_ = v___x_878_;
v___y_640_ = v___y_857_;
v___y_641_ = v___x_953_;
v___y_642_ = v___x_918_;
v___y_643_ = v___x_895_;
v___y_644_ = v___y_859_;
v___y_645_ = v___y_863_;
v___y_646_ = v___y_864_;
v___y_647_ = v___y_865_;
v___y_648_ = v___y_866_;
v___y_649_ = v___x_877_;
v___y_650_ = v___x_885_;
v___y_651_ = v___y_868_;
v_specTac_652_ = v___x_962_;
v___y_653_ = v___y_848_;
v___y_654_ = v_a_943_;
goto v___jp_631_;
}
}
}
}
}
}
v___jp_967_:
{
lean_object* v___x_989_; lean_object* v_a_990_; lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1019_; 
v___x_989_ = l_Lean_Elab_Tactic_Do_expandDefContract___lam__0(v_ref_987_, v___y_986_, v___y_988_);
v_a_990_ = lean_ctor_get(v___x_989_, 0);
v_a_991_ = lean_ctor_get(v___x_989_, 1);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_993_ = v___x_989_;
v_isShared_994_ = v_isSharedCheck_1019_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_inc(v_a_990_);
lean_dec(v___x_989_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1019_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_1000_; 
v___x_995_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0));
v___x_996_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__26));
v___x_997_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__60));
v___x_998_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__61));
lean_inc(v_a_990_);
if (v_isShared_994_ == 0)
{
lean_ctor_set_tag(v___x_993_, 2);
lean_ctor_set(v___x_993_, 1, v___x_998_);
v___x_1000_ = v___x_993_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_a_990_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v___x_998_);
v___x_1000_ = v_reuseFailAlloc_1018_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; uint8_t v___x_1004_; 
v___x_1001_ = l_Lean_Syntax_node1(v_a_990_, v___x_997_, v___x_1000_);
v___x_1002_ = l_Lean_Syntax_getArgs(v___y_968_);
lean_dec(v___y_968_);
v___x_1003_ = lean_array_get_size(v___x_1002_);
v___x_1004_ = lean_nat_dec_lt(v___y_972_, v___x_1003_);
if (v___x_1004_ == 0)
{
lean_dec_ref(v___x_1002_);
v___y_848_ = v___y_986_;
v___y_849_ = v___y_969_;
v___y_850_ = v___y_970_;
v___y_851_ = v_ref_987_;
v___y_852_ = v___x_995_;
v___y_853_ = v___y_971_;
v___y_854_ = v___y_972_;
v___y_855_ = v___y_973_;
v___y_856_ = v_post_985_;
v___y_857_ = v___y_974_;
v___y_858_ = v___y_975_;
v___y_859_ = v___y_976_;
v___y_860_ = v___y_977_;
v___y_861_ = v___y_978_;
v___y_862_ = v___y_979_;
v___y_863_ = v___y_980_;
v___y_864_ = v___y_981_;
v___y_865_ = v___y_982_;
v___y_866_ = v___x_996_;
v___y_867_ = v___y_983_;
v___y_868_ = v___y_984_;
v_a_869_ = v___x_1001_;
v_a_870_ = v_a_991_;
goto v___jp_847_;
}
else
{
size_t v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = lean_usize_of_nat(v___x_1003_);
v___x_1006_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2(v___x_1002_, v___x_1005_, v___y_975_, v___x_1001_, v___y_986_, v_a_991_);
lean_dec_ref(v___x_1002_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; lean_object* v_a_1008_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_a_1007_);
v_a_1008_ = lean_ctor_get(v___x_1006_, 1);
lean_inc(v_a_1008_);
lean_dec_ref_known(v___x_1006_, 2);
v___y_848_ = v___y_986_;
v___y_849_ = v___y_969_;
v___y_850_ = v___y_970_;
v___y_851_ = v_ref_987_;
v___y_852_ = v___x_995_;
v___y_853_ = v___y_971_;
v___y_854_ = v___y_972_;
v___y_855_ = v___y_973_;
v___y_856_ = v_post_985_;
v___y_857_ = v___y_974_;
v___y_858_ = v___y_975_;
v___y_859_ = v___y_976_;
v___y_860_ = v___y_977_;
v___y_861_ = v___y_978_;
v___y_862_ = v___y_979_;
v___y_863_ = v___y_980_;
v___y_864_ = v___y_981_;
v___y_865_ = v___y_982_;
v___y_866_ = v___x_996_;
v___y_867_ = v___y_983_;
v___y_868_ = v___y_984_;
v_a_869_ = v_a_1007_;
v_a_870_ = v_a_1008_;
goto v___jp_847_;
}
else
{
lean_object* v_a_1009_; lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
lean_dec(v_post_985_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec(v___y_976_);
lean_dec(v___y_970_);
lean_dec(v___y_969_);
v_a_1009_ = lean_ctor_get(v___x_1006_, 0);
v_a_1010_ = lean_ctor_get(v___x_1006_, 1);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_1006_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_inc(v_a_1009_);
lean_dec(v___x_1006_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1009_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
}
}
}
v___jp_1020_:
{
lean_object* v_ref_1041_; 
v_ref_1041_ = lean_ctor_get(v___y_1039_, 5);
v___y_968_ = v___y_1021_;
v___y_969_ = v___y_1022_;
v___y_970_ = v___y_1023_;
v___y_971_ = v___y_1024_;
v___y_972_ = v___y_1025_;
v___y_973_ = v___y_1026_;
v___y_974_ = v___y_1027_;
v___y_975_ = v___y_1028_;
v___y_976_ = v___y_1029_;
v___y_977_ = v___y_1030_;
v___y_978_ = v___y_1031_;
v___y_979_ = v___y_1032_;
v___y_980_ = v___y_1033_;
v___y_981_ = v___y_1034_;
v___y_982_ = v___y_1035_;
v___y_983_ = v___y_1036_;
v___y_984_ = v___y_1037_;
v_post_985_ = v_post_1038_;
v___y_986_ = v___y_1039_;
v_ref_987_ = v_ref_1041_;
v___y_988_ = v___y_1040_;
goto v___jp_967_;
}
v___jp_1043_:
{
uint8_t v___x_1065_; 
v___x_1065_ = l_Lean_Syntax_isNone(v___y_1048_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1066_; lean_object* v___x_1067_; uint8_t v___x_1068_; 
v___x_1066_ = l_Lean_Syntax_getArg(v___y_1048_, v___y_1047_);
lean_dec(v___y_1048_);
v___x_1067_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__63));
lean_inc(v___x_1066_);
v___x_1068_ = l_Lean_Syntax_isOfKind(v___x_1066_, v___x_1067_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; 
lean_dec(v___x_1066_);
v___x_1069_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1064_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v_a_1071_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_a_1070_);
v_a_1071_ = lean_ctor_get(v___x_1069_, 1);
lean_inc(v_a_1071_);
lean_dec_ref_known(v___x_1069_, 2);
v___y_1021_ = v___y_1044_;
v___y_1022_ = v_pre_1062_;
v___y_1023_ = v___y_1045_;
v___y_1024_ = v___y_1046_;
v___y_1025_ = v___y_1047_;
v___y_1026_ = v___y_1049_;
v___y_1027_ = v___y_1050_;
v___y_1028_ = v___y_1051_;
v___y_1029_ = v___y_1052_;
v___y_1030_ = v___y_1053_;
v___y_1031_ = v___y_1054_;
v___y_1032_ = v___y_1055_;
v___y_1033_ = v___y_1056_;
v___y_1034_ = v___y_1057_;
v___y_1035_ = v___y_1058_;
v___y_1036_ = v___y_1060_;
v___y_1037_ = v___y_1061_;
v_post_1038_ = v_a_1070_;
v___y_1039_ = v___y_1063_;
v___y_1040_ = v_a_1071_;
goto v___jp_1020_;
}
else
{
lean_object* v_a_1072_; lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
lean_dec(v_pre_1062_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec(v___y_1045_);
lean_dec(v___y_1044_);
v_a_1072_ = lean_ctor_get(v___x_1069_, 0);
v_a_1073_ = lean_ctor_get(v___x_1069_, 1);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_1069_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_inc(v_a_1072_);
lean_dec(v___x_1069_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1072_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v_a_1073_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
else
{
lean_object* v___x_1081_; lean_object* v___x_1082_; uint8_t v___x_1083_; 
v___x_1081_ = l_Lean_Syntax_getArg(v___x_1066_, v___x_1042_);
lean_dec(v___x_1066_);
v___x_1082_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__3));
lean_inc(v___x_1081_);
v___x_1083_ = l_Lean_Syntax_isOfKind(v___x_1081_, v___x_1082_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1084_; 
lean_dec(v___x_1081_);
v___x_1084_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1064_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v_a_1086_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1085_);
v_a_1086_ = lean_ctor_get(v___x_1084_, 1);
lean_inc(v_a_1086_);
lean_dec_ref_known(v___x_1084_, 2);
v___y_1021_ = v___y_1044_;
v___y_1022_ = v_pre_1062_;
v___y_1023_ = v___y_1045_;
v___y_1024_ = v___y_1046_;
v___y_1025_ = v___y_1047_;
v___y_1026_ = v___y_1049_;
v___y_1027_ = v___y_1050_;
v___y_1028_ = v___y_1051_;
v___y_1029_ = v___y_1052_;
v___y_1030_ = v___y_1053_;
v___y_1031_ = v___y_1054_;
v___y_1032_ = v___y_1055_;
v___y_1033_ = v___y_1056_;
v___y_1034_ = v___y_1057_;
v___y_1035_ = v___y_1058_;
v___y_1036_ = v___y_1060_;
v___y_1037_ = v___y_1061_;
v_post_1038_ = v_a_1085_;
v___y_1039_ = v___y_1063_;
v___y_1040_ = v_a_1086_;
goto v___jp_1020_;
}
else
{
lean_object* v_a_1087_; lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
lean_dec(v_pre_1062_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec(v___y_1045_);
lean_dec(v___y_1044_);
v_a_1087_ = lean_ctor_get(v___x_1084_, 0);
v_a_1088_ = lean_ctor_get(v___x_1084_, 1);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1084_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_inc(v_a_1087_);
lean_dec(v___x_1084_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1087_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
else
{
lean_object* v_ref_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v_ref_1096_ = lean_ctor_get(v___y_1063_, 5);
v___x_1097_ = l_Lean_SourceInfo_fromRef(v_ref_1096_, v___x_1065_);
v___x_1098_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__40));
v___x_1099_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__41));
lean_inc(v___x_1097_);
v___x_1100_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1097_);
lean_ctor_set(v___x_1100_, 1, v___x_1098_);
v___x_1101_ = l_Lean_Syntax_node2(v___x_1097_, v___x_1099_, v___x_1100_, v___x_1081_);
v___y_968_ = v___y_1044_;
v___y_969_ = v_pre_1062_;
v___y_970_ = v___y_1045_;
v___y_971_ = v___y_1046_;
v___y_972_ = v___y_1047_;
v___y_973_ = v___y_1049_;
v___y_974_ = v___y_1050_;
v___y_975_ = v___y_1051_;
v___y_976_ = v___y_1052_;
v___y_977_ = v___y_1053_;
v___y_978_ = v___y_1054_;
v___y_979_ = v___y_1055_;
v___y_980_ = v___y_1056_;
v___y_981_ = v___y_1057_;
v___y_982_ = v___y_1058_;
v___y_983_ = v___y_1060_;
v___y_984_ = v___y_1061_;
v_post_985_ = v___x_1101_;
v___y_986_ = v___y_1063_;
v_ref_987_ = v_ref_1096_;
v___y_988_ = v___y_1064_;
goto v___jp_967_;
}
}
}
else
{
lean_object* v_ref_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
lean_dec(v___y_1048_);
v_ref_1102_ = lean_ctor_get(v___y_1063_, 5);
v___x_1103_ = l_Lean_SourceInfo_fromRef(v_ref_1102_, v___y_1059_);
v___x_1104_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__40));
v___x_1105_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__41));
lean_inc_n(v___x_1103_, 9);
v___x_1106_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1103_);
lean_ctor_set(v___x_1106_, 1, v___x_1104_);
v___x_1107_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__3));
v___x_1108_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__2));
v___x_1109_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__65));
v___x_1110_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__66));
v___x_1111_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1103_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
v___x_1112_ = l_Lean_Syntax_node1(v___x_1103_, v___x_1109_, v___x_1111_);
v___x_1113_ = l_Lean_Syntax_node1(v___x_1103_, v___x_1108_, v___x_1112_);
v___x_1114_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_expandDefContract___closed__53, &l_Lean_Elab_Tactic_Do_expandDefContract___closed__53_once, _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__53);
v___x_1115_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1103_);
lean_ctor_set(v___x_1115_, 1, v___x_1108_);
lean_ctor_set(v___x_1115_, 2, v___x_1114_);
v___x_1116_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__67));
v___x_1117_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1103_);
lean_ctor_set(v___x_1117_, 1, v___x_1116_);
v___x_1118_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__69));
v___x_1119_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__70));
v___x_1120_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1103_);
lean_ctor_set(v___x_1120_, 1, v___x_1119_);
v___x_1121_ = l_Lean_Syntax_node1(v___x_1103_, v___x_1118_, v___x_1120_);
v___x_1122_ = l_Lean_Syntax_node4(v___x_1103_, v___x_1107_, v___x_1113_, v___x_1115_, v___x_1117_, v___x_1121_);
v___x_1123_ = l_Lean_Syntax_node2(v___x_1103_, v___x_1105_, v___x_1106_, v___x_1122_);
v___y_968_ = v___y_1044_;
v___y_969_ = v_pre_1062_;
v___y_970_ = v___y_1045_;
v___y_971_ = v___y_1046_;
v___y_972_ = v___y_1047_;
v___y_973_ = v___y_1049_;
v___y_974_ = v___y_1050_;
v___y_975_ = v___y_1051_;
v___y_976_ = v___y_1052_;
v___y_977_ = v___y_1053_;
v___y_978_ = v___y_1054_;
v___y_979_ = v___y_1055_;
v___y_980_ = v___y_1056_;
v___y_981_ = v___y_1057_;
v___y_982_ = v___y_1058_;
v___y_983_ = v___y_1060_;
v___y_984_ = v___y_1061_;
v_post_985_ = v___x_1123_;
v___y_986_ = v___y_1063_;
v_ref_987_ = v_ref_1102_;
v___y_988_ = v___y_1064_;
goto v___jp_967_;
}
}
v___jp_1124_:
{
uint8_t v___x_1146_; 
v___x_1146_ = l_Lean_Syntax_isNone(v___y_1128_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; lean_object* v___x_1148_; uint8_t v___x_1149_; 
v___x_1147_ = l_Lean_Syntax_getArg(v___y_1128_, v___y_1131_);
lean_dec(v___y_1128_);
v___x_1148_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__72));
lean_inc(v___x_1147_);
v___x_1149_ = l_Lean_Syntax_isOfKind(v___x_1147_, v___x_1148_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; 
lean_dec(v___x_1147_);
v___x_1150_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1130_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v_a_1151_; lean_object* v_a_1152_; 
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
lean_inc(v_a_1151_);
v_a_1152_ = lean_ctor_get(v___x_1150_, 1);
lean_inc(v_a_1152_);
lean_dec_ref_known(v___x_1150_, 2);
v___y_1044_ = v___y_1125_;
v___y_1045_ = v___y_1126_;
v___y_1046_ = v___y_1129_;
v___y_1047_ = v___y_1131_;
v___y_1048_ = v___y_1132_;
v___y_1049_ = v___y_1133_;
v___y_1050_ = v___y_1134_;
v___y_1051_ = v___y_1135_;
v___y_1052_ = v___y_1136_;
v___y_1053_ = v___y_1137_;
v___y_1054_ = v___y_1145_;
v___y_1055_ = v___y_1138_;
v___y_1056_ = v___y_1139_;
v___y_1057_ = v___y_1140_;
v___y_1058_ = v___y_1141_;
v___y_1059_ = v___y_1143_;
v___y_1060_ = v___y_1142_;
v___y_1061_ = v___y_1144_;
v_pre_1062_ = v_a_1151_;
v___y_1063_ = v___y_1127_;
v___y_1064_ = v_a_1152_;
goto v___jp_1043_;
}
else
{
lean_object* v_a_1153_; lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
lean_dec_ref(v___y_1145_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1139_);
lean_dec(v___y_1138_);
lean_dec(v___y_1137_);
lean_dec(v___y_1136_);
lean_dec(v___y_1132_);
lean_dec(v___y_1126_);
lean_dec(v___y_1125_);
v_a_1153_ = lean_ctor_get(v___x_1150_, 0);
v_a_1154_ = lean_ctor_get(v___x_1150_, 1);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1156_ = v___x_1150_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_inc(v_a_1153_);
lean_dec(v___x_1150_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1153_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v_a_1154_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
else
{
lean_object* v___x_1162_; lean_object* v___x_1163_; uint8_t v___x_1164_; 
v___x_1162_ = l_Lean_Syntax_getArg(v___x_1147_, v___x_1042_);
lean_dec(v___x_1147_);
v___x_1163_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__3));
lean_inc(v___x_1162_);
v___x_1164_ = l_Lean_Syntax_isOfKind(v___x_1162_, v___x_1163_);
if (v___x_1164_ == 0)
{
v___y_1044_ = v___y_1125_;
v___y_1045_ = v___y_1126_;
v___y_1046_ = v___y_1129_;
v___y_1047_ = v___y_1131_;
v___y_1048_ = v___y_1132_;
v___y_1049_ = v___y_1133_;
v___y_1050_ = v___y_1134_;
v___y_1051_ = v___y_1135_;
v___y_1052_ = v___y_1136_;
v___y_1053_ = v___y_1137_;
v___y_1054_ = v___y_1145_;
v___y_1055_ = v___y_1138_;
v___y_1056_ = v___y_1139_;
v___y_1057_ = v___y_1140_;
v___y_1058_ = v___y_1141_;
v___y_1059_ = v___y_1143_;
v___y_1060_ = v___y_1142_;
v___y_1061_ = v___y_1144_;
v_pre_1062_ = v___x_1162_;
v___y_1063_ = v___y_1127_;
v___y_1064_ = v___y_1130_;
goto v___jp_1043_;
}
else
{
lean_object* v_ref_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v_ref_1165_ = lean_ctor_get(v___y_1127_, 5);
v___x_1166_ = l_Lean_SourceInfo_fromRef(v_ref_1165_, v___x_1146_);
v___x_1167_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__40));
v___x_1168_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__41));
lean_inc(v___x_1166_);
v___x_1169_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1166_);
lean_ctor_set(v___x_1169_, 1, v___x_1167_);
v___x_1170_ = l_Lean_Syntax_node2(v___x_1166_, v___x_1168_, v___x_1169_, v___x_1162_);
v___y_1044_ = v___y_1125_;
v___y_1045_ = v___y_1126_;
v___y_1046_ = v___y_1129_;
v___y_1047_ = v___y_1131_;
v___y_1048_ = v___y_1132_;
v___y_1049_ = v___y_1133_;
v___y_1050_ = v___y_1134_;
v___y_1051_ = v___y_1135_;
v___y_1052_ = v___y_1136_;
v___y_1053_ = v___y_1137_;
v___y_1054_ = v___y_1145_;
v___y_1055_ = v___y_1138_;
v___y_1056_ = v___y_1139_;
v___y_1057_ = v___y_1140_;
v___y_1058_ = v___y_1141_;
v___y_1059_ = v___y_1143_;
v___y_1060_ = v___y_1142_;
v___y_1061_ = v___y_1144_;
v_pre_1062_ = v___x_1170_;
v___y_1063_ = v___y_1127_;
v___y_1064_ = v___y_1130_;
goto v___jp_1043_;
}
}
}
else
{
lean_object* v_ref_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
lean_dec(v___y_1128_);
v_ref_1171_ = lean_ctor_get(v___y_1127_, 5);
v___x_1172_ = l_Lean_SourceInfo_fromRef(v_ref_1171_, v___y_1143_);
v___x_1173_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__69));
v___x_1174_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__70));
lean_inc(v___x_1172_);
v___x_1175_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1172_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
v___x_1176_ = l_Lean_Syntax_node1(v___x_1172_, v___x_1173_, v___x_1175_);
v___y_1044_ = v___y_1125_;
v___y_1045_ = v___y_1126_;
v___y_1046_ = v___y_1129_;
v___y_1047_ = v___y_1131_;
v___y_1048_ = v___y_1132_;
v___y_1049_ = v___y_1133_;
v___y_1050_ = v___y_1134_;
v___y_1051_ = v___y_1135_;
v___y_1052_ = v___y_1136_;
v___y_1053_ = v___y_1137_;
v___y_1054_ = v___y_1145_;
v___y_1055_ = v___y_1138_;
v___y_1056_ = v___y_1139_;
v___y_1057_ = v___y_1140_;
v___y_1058_ = v___y_1141_;
v___y_1059_ = v___y_1143_;
v___y_1060_ = v___y_1142_;
v___y_1061_ = v___y_1144_;
v_pre_1062_ = v___x_1176_;
v___y_1063_ = v___y_1127_;
v___y_1064_ = v___y_1130_;
goto v___jp_1043_;
}
}
v___jp_1177_:
{
lean_object* v___x_1198_; size_t v_sz_1199_; size_t v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; uint8_t v___x_1204_; 
lean_inc_ref(v___y_1183_);
v___x_1198_ = l_Array_append___redArg(v___y_1183_, v___y_1197_);
lean_dec_ref(v___y_1197_);
v_sz_1199_ = lean_array_size(v___x_1198_);
v___x_1200_ = ((size_t)0ULL);
v___x_1201_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__0(v_sz_1199_, v___x_1200_, v___x_1198_);
v___x_1202_ = lean_mk_empty_array_with_capacity(v___y_1185_);
v___x_1203_ = lean_array_get_size(v___y_1183_);
v___x_1204_ = lean_nat_dec_lt(v___y_1185_, v___x_1203_);
if (v___x_1204_ == 0)
{
lean_dec_ref(v___y_1183_);
v___y_1125_ = v___y_1178_;
v___y_1126_ = v___y_1179_;
v___y_1127_ = v___y_1180_;
v___y_1128_ = v___y_1181_;
v___y_1129_ = v___y_1182_;
v___y_1130_ = v___y_1184_;
v___y_1131_ = v___y_1185_;
v___y_1132_ = v___y_1186_;
v___y_1133_ = v___y_1187_;
v___y_1134_ = v___y_1188_;
v___y_1135_ = v___x_1200_;
v___y_1136_ = v___y_1189_;
v___y_1137_ = v___y_1190_;
v___y_1138_ = v___y_1191_;
v___y_1139_ = v___y_1192_;
v___y_1140_ = v___x_1201_;
v___y_1141_ = v___y_1193_;
v___y_1142_ = v___y_1195_;
v___y_1143_ = v___y_1194_;
v___y_1144_ = v___y_1196_;
v___y_1145_ = v___x_1202_;
goto v___jp_1124_;
}
else
{
size_t v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = lean_usize_of_nat(v___x_1203_);
v___x_1206_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__3(v___y_1183_, v___x_1200_, v___x_1205_, v___x_1202_);
lean_dec_ref(v___y_1183_);
v___y_1125_ = v___y_1178_;
v___y_1126_ = v___y_1179_;
v___y_1127_ = v___y_1180_;
v___y_1128_ = v___y_1181_;
v___y_1129_ = v___y_1182_;
v___y_1130_ = v___y_1184_;
v___y_1131_ = v___y_1185_;
v___y_1132_ = v___y_1186_;
v___y_1133_ = v___y_1187_;
v___y_1134_ = v___y_1188_;
v___y_1135_ = v___x_1200_;
v___y_1136_ = v___y_1189_;
v___y_1137_ = v___y_1190_;
v___y_1138_ = v___y_1191_;
v___y_1139_ = v___y_1192_;
v___y_1140_ = v___x_1201_;
v___y_1141_ = v___y_1193_;
v___y_1142_ = v___y_1195_;
v___y_1143_ = v___y_1194_;
v___y_1144_ = v___y_1196_;
v___y_1145_ = v___x_1206_;
goto v___jp_1124_;
}
}
v___jp_1208_:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; uint8_t v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1223_ = l_Lean_Syntax_getArg(v_decl_1207_, v___y_1219_);
v___x_1224_ = l_Lean_Syntax_getArg(v_decl_1207_, v___x_1042_);
lean_dec(v_decl_1207_);
v___x_1225_ = l_Lean_Syntax_getArg(v___x_1224_, v___y_1216_);
lean_dec(v___x_1224_);
v___x_1226_ = l_Lean_TSyntax_getId(v___x_1225_);
v___x_1227_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0___closed__0));
v___x_1228_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0___closed__1));
lean_inc(v___x_1226_);
v___x_1229_ = l_Lean_Name_append(v___x_1226_, v___x_1228_);
v___x_1230_ = 0;
v___x_1231_ = l_Lean_mkIdentFrom(v___x_1225_, v___x_1229_, v___x_1230_);
v___x_1232_ = l_Lean_Syntax_getArg(v___x_1223_, v___y_1216_);
lean_dec(v___x_1223_);
v___x_1233_ = l_Lean_Syntax_getArgs(v___x_1232_);
lean_dec(v___x_1232_);
v___x_1234_ = l_Lean_Syntax_isNone(v___y_1213_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1235_ = l_Lean_Syntax_getArg(v___y_1213_, v___y_1216_);
lean_dec(v___y_1213_);
v___x_1236_ = l_Lean_Syntax_getArg(v___x_1235_, v___x_1042_);
lean_dec(v___x_1235_);
v___x_1237_ = l_Lean_Syntax_getArgs(v___x_1236_);
lean_dec(v___x_1236_);
v___y_1178_ = v___y_1210_;
v___y_1179_ = v___y_1211_;
v___y_1180_ = v___y_1221_;
v___y_1181_ = v___y_1215_;
v___y_1182_ = v___y_1214_;
v___y_1183_ = v___x_1233_;
v___y_1184_ = v___y_1222_;
v___y_1185_ = v___y_1216_;
v___y_1186_ = v___y_1217_;
v___y_1187_ = v___x_1227_;
v___y_1188_ = v___y_1209_;
v___y_1189_ = v___x_1231_;
v___y_1190_ = v___y_1212_;
v___y_1191_ = v___x_1226_;
v___y_1192_ = v___x_1225_;
v___y_1193_ = v___y_1218_;
v___y_1194_ = v___x_1230_;
v___y_1195_ = v___y_1219_;
v___y_1196_ = v___y_1220_;
v___y_1197_ = v___x_1237_;
goto v___jp_1177_;
}
else
{
lean_object* v___x_1238_; 
lean_dec(v___y_1213_);
v___x_1238_ = lean_mk_empty_array_with_capacity(v___y_1216_);
v___y_1178_ = v___y_1210_;
v___y_1179_ = v___y_1211_;
v___y_1180_ = v___y_1221_;
v___y_1181_ = v___y_1215_;
v___y_1182_ = v___y_1214_;
v___y_1183_ = v___x_1233_;
v___y_1184_ = v___y_1222_;
v___y_1185_ = v___y_1216_;
v___y_1186_ = v___y_1217_;
v___y_1187_ = v___x_1227_;
v___y_1188_ = v___y_1209_;
v___y_1189_ = v___x_1231_;
v___y_1190_ = v___y_1212_;
v___y_1191_ = v___x_1226_;
v___y_1192_ = v___x_1225_;
v___y_1193_ = v___y_1218_;
v___y_1194_ = v___x_1230_;
v___y_1195_ = v___y_1219_;
v___y_1196_ = v___y_1220_;
v___y_1197_ = v___x_1238_;
goto v___jp_1177_;
}
}
v___jp_1239_:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__73));
v___x_1256_ = l_Lean_Macro_throwErrorAt___redArg(v___y_1254_, v___x_1255_, v___y_1250_, v___y_1247_);
lean_dec(v___y_1254_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; 
v_a_1257_ = lean_ctor_get(v___x_1256_, 1);
lean_inc(v_a_1257_);
lean_dec_ref_known(v___x_1256_, 2);
v___y_1209_ = v___y_1246_;
v___y_1210_ = v___y_1240_;
v___y_1211_ = v___y_1241_;
v___y_1212_ = v___y_1248_;
v___y_1213_ = v___y_1249_;
v___y_1214_ = v___y_1242_;
v___y_1215_ = v___y_1243_;
v___y_1216_ = v___y_1244_;
v___y_1217_ = v___y_1245_;
v___y_1218_ = v___y_1251_;
v___y_1219_ = v___y_1252_;
v___y_1220_ = v___y_1253_;
v___y_1221_ = v___y_1250_;
v___y_1222_ = v_a_1257_;
goto v___jp_1208_;
}
else
{
lean_object* v_a_1258_; lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
lean_dec(v___y_1251_);
lean_dec(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec(v___y_1245_);
lean_dec(v___y_1243_);
lean_dec(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec(v_decl_1207_);
v_a_1258_ = lean_ctor_get(v___x_1256_, 0);
v_a_1259_ = lean_ctor_get(v___x_1256_, 1);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1261_ = v___x_1256_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_inc(v_a_1258_);
lean_dec(v___x_1256_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1258_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v_a_1259_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
v___jp_1267_:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1278_ = lean_unsigned_to_nat(4u);
v___x_1279_ = l_Lean_Syntax_getArg(v___y_1273_, v___x_1278_);
v___x_1280_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection(v___x_1279_, v___y_1276_, v___y_1277_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v_a_1282_; lean_object* v_fst_1283_; lean_object* v_snd_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1281_);
v_a_1282_ = lean_ctor_get(v___x_1280_, 1);
lean_inc(v_a_1282_);
lean_dec_ref_known(v___x_1280_, 2);
v_fst_1283_ = lean_ctor_get(v_a_1281_, 0);
lean_inc(v_fst_1283_);
v_snd_1284_ = lean_ctor_get(v_a_1281_, 1);
lean_inc(v_snd_1284_);
lean_dec(v_a_1281_);
v___x_1285_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__4));
v___x_1286_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__5));
v___x_1287_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__75));
v___x_1288_ = l_Lean_Macro_hasDecl(v___x_1287_, v___y_1276_, v_a_1282_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v_a_1289_; lean_object* v_a_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; uint8_t v___x_1293_; 
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_a_1289_);
v_a_1290_ = lean_ctor_get(v___x_1288_, 1);
lean_inc(v_a_1290_);
lean_dec_ref_known(v___x_1288_, 2);
lean_inc(v_decl_1207_);
v___x_1291_ = l_Lean_Syntax_setArg(v_decl_1207_, v___y_1275_, v_snd_1284_);
v___x_1292_ = l_Lean_Syntax_setArg(v_stx_628_, v___x_1042_, v___x_1291_);
v___x_1293_ = lean_unbox(v_a_1289_);
lean_dec(v_a_1289_);
if (v___x_1293_ == 0)
{
uint8_t v___x_1294_; 
v___x_1294_ = l_Lean_Syntax_isNone(v___y_1270_);
if (v___x_1294_ == 0)
{
lean_inc(v___y_1270_);
v___y_1240_ = v___y_1268_;
v___y_1241_ = v___x_1292_;
v___y_1242_ = v___x_1285_;
v___y_1243_ = v___y_1269_;
v___y_1244_ = v___y_1271_;
v___y_1245_ = v___y_1272_;
v___y_1246_ = v___x_1286_;
v___y_1247_ = v_a_1290_;
v___y_1248_ = v_fst_1283_;
v___y_1249_ = v___y_1270_;
v___y_1250_ = v___y_1276_;
v___y_1251_ = v___y_1273_;
v___y_1252_ = v___y_1274_;
v___y_1253_ = v___y_1275_;
v___y_1254_ = v___y_1270_;
goto v___jp_1239_;
}
else
{
uint8_t v___x_1295_; 
v___x_1295_ = l_Lean_Syntax_isNone(v___y_1269_);
if (v___x_1295_ == 0)
{
lean_inc(v___y_1269_);
v___y_1240_ = v___y_1268_;
v___y_1241_ = v___x_1292_;
v___y_1242_ = v___x_1285_;
v___y_1243_ = v___y_1269_;
v___y_1244_ = v___y_1271_;
v___y_1245_ = v___y_1272_;
v___y_1246_ = v___x_1286_;
v___y_1247_ = v_a_1290_;
v___y_1248_ = v_fst_1283_;
v___y_1249_ = v___y_1270_;
v___y_1250_ = v___y_1276_;
v___y_1251_ = v___y_1273_;
v___y_1252_ = v___y_1274_;
v___y_1253_ = v___y_1275_;
v___y_1254_ = v___y_1269_;
goto v___jp_1239_;
}
else
{
uint8_t v___x_1296_; 
v___x_1296_ = l_Lean_Syntax_isNone(v___y_1272_);
if (v___x_1296_ == 0)
{
lean_inc(v___y_1272_);
v___y_1240_ = v___y_1268_;
v___y_1241_ = v___x_1292_;
v___y_1242_ = v___x_1285_;
v___y_1243_ = v___y_1269_;
v___y_1244_ = v___y_1271_;
v___y_1245_ = v___y_1272_;
v___y_1246_ = v___x_1286_;
v___y_1247_ = v_a_1290_;
v___y_1248_ = v_fst_1283_;
v___y_1249_ = v___y_1270_;
v___y_1250_ = v___y_1276_;
v___y_1251_ = v___y_1273_;
v___y_1252_ = v___y_1274_;
v___y_1253_ = v___y_1275_;
v___y_1254_ = v___y_1272_;
goto v___jp_1239_;
}
else
{
lean_inc(v___y_1268_);
v___y_1240_ = v___y_1268_;
v___y_1241_ = v___x_1292_;
v___y_1242_ = v___x_1285_;
v___y_1243_ = v___y_1269_;
v___y_1244_ = v___y_1271_;
v___y_1245_ = v___y_1272_;
v___y_1246_ = v___x_1286_;
v___y_1247_ = v_a_1290_;
v___y_1248_ = v_fst_1283_;
v___y_1249_ = v___y_1270_;
v___y_1250_ = v___y_1276_;
v___y_1251_ = v___y_1273_;
v___y_1252_ = v___y_1274_;
v___y_1253_ = v___y_1275_;
v___y_1254_ = v___y_1268_;
goto v___jp_1239_;
}
}
}
}
else
{
v___y_1209_ = v___x_1286_;
v___y_1210_ = v___y_1268_;
v___y_1211_ = v___x_1292_;
v___y_1212_ = v_fst_1283_;
v___y_1213_ = v___y_1270_;
v___y_1214_ = v___x_1285_;
v___y_1215_ = v___y_1269_;
v___y_1216_ = v___y_1271_;
v___y_1217_ = v___y_1272_;
v___y_1218_ = v___y_1273_;
v___y_1219_ = v___y_1274_;
v___y_1220_ = v___y_1275_;
v___y_1221_ = v___y_1276_;
v___y_1222_ = v_a_1290_;
goto v___jp_1208_;
}
}
else
{
lean_object* v_a_1297_; lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
lean_dec(v_snd_1284_);
lean_dec(v_fst_1283_);
lean_dec(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec(v_decl_1207_);
lean_dec(v_stx_628_);
v_a_1297_ = lean_ctor_get(v___x_1288_, 0);
v_a_1298_ = lean_ctor_get(v___x_1288_, 1);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1288_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_inc(v_a_1297_);
lean_dec(v___x_1288_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1297_);
lean_ctor_set(v_reuseFailAlloc_1304_, 1, v_a_1298_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
}
else
{
lean_object* v_a_1306_; lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
lean_dec(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec(v_decl_1207_);
lean_dec(v_stx_628_);
v_a_1306_ = lean_ctor_get(v___x_1280_, 0);
v_a_1307_ = lean_ctor_get(v___x_1280_, 1);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v___x_1280_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_inc(v_a_1306_);
lean_dec(v___x_1280_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1306_);
lean_ctor_set(v_reuseFailAlloc_1313_, 1, v_a_1307_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
v___jp_1315_:
{
lean_object* v___x_1320_; lean_object* v_givenStx_1321_; lean_object* v_requiresStx_1322_; lean_object* v___x_1323_; lean_object* v_ensuresStx_1324_; lean_object* v_throwsStx_1325_; uint8_t v___x_1326_; 
v___x_1320_ = lean_unsigned_to_nat(0u);
v_givenStx_1321_ = l_Lean_Syntax_getArg(v___y_1316_, v___x_1320_);
v_requiresStx_1322_ = l_Lean_Syntax_getArg(v___y_1316_, v___x_1042_);
v___x_1323_ = lean_unsigned_to_nat(2u);
v_ensuresStx_1324_ = l_Lean_Syntax_getArg(v___y_1316_, v___x_1323_);
v_throwsStx_1325_ = l_Lean_Syntax_getArg(v___y_1316_, v___y_1317_);
v___x_1326_ = l_Lean_Syntax_isNone(v_givenStx_1321_);
if (v___x_1326_ == 0)
{
v___y_1268_ = v_throwsStx_1325_;
v___y_1269_ = v_requiresStx_1322_;
v___y_1270_ = v_givenStx_1321_;
v___y_1271_ = v___x_1320_;
v___y_1272_ = v_ensuresStx_1324_;
v___y_1273_ = v___y_1316_;
v___y_1274_ = v___x_1323_;
v___y_1275_ = v___y_1317_;
v___y_1276_ = v___y_1318_;
v___y_1277_ = v___y_1319_;
goto v___jp_1267_;
}
else
{
uint8_t v___x_1327_; 
v___x_1327_ = l_Lean_Syntax_isNone(v_requiresStx_1322_);
if (v___x_1327_ == 0)
{
v___y_1268_ = v_throwsStx_1325_;
v___y_1269_ = v_requiresStx_1322_;
v___y_1270_ = v_givenStx_1321_;
v___y_1271_ = v___x_1320_;
v___y_1272_ = v_ensuresStx_1324_;
v___y_1273_ = v___y_1316_;
v___y_1274_ = v___x_1323_;
v___y_1275_ = v___y_1317_;
v___y_1276_ = v___y_1318_;
v___y_1277_ = v___y_1319_;
goto v___jp_1267_;
}
else
{
uint8_t v___x_1328_; 
v___x_1328_ = l_Lean_Syntax_isNone(v_ensuresStx_1324_);
if (v___x_1328_ == 0)
{
v___y_1268_ = v_throwsStx_1325_;
v___y_1269_ = v_requiresStx_1322_;
v___y_1270_ = v_givenStx_1321_;
v___y_1271_ = v___x_1320_;
v___y_1272_ = v_ensuresStx_1324_;
v___y_1273_ = v___y_1316_;
v___y_1274_ = v___x_1323_;
v___y_1275_ = v___y_1317_;
v___y_1276_ = v___y_1318_;
v___y_1277_ = v___y_1319_;
goto v___jp_1267_;
}
else
{
lean_object* v___x_1329_; uint8_t v___x_1330_; 
v___x_1329_ = l_Lean_Syntax_getNumArgs(v_throwsStx_1325_);
v___x_1330_ = lean_nat_dec_eq(v___x_1329_, v___x_1320_);
lean_dec(v___x_1329_);
if (v___x_1330_ == 0)
{
v___y_1268_ = v_throwsStx_1325_;
v___y_1269_ = v_requiresStx_1322_;
v___y_1270_ = v_givenStx_1321_;
v___y_1271_ = v___x_1320_;
v___y_1272_ = v_ensuresStx_1324_;
v___y_1273_ = v___y_1316_;
v___y_1274_ = v___x_1323_;
v___y_1275_ = v___y_1317_;
v___y_1276_ = v___y_1318_;
v___y_1277_ = v___y_1319_;
goto v___jp_1267_;
}
else
{
lean_object* v___x_1331_; 
v___x_1331_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1319_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v_a_1332_; 
v_a_1332_ = lean_ctor_get(v___x_1331_, 1);
lean_inc(v_a_1332_);
lean_dec_ref_known(v___x_1331_, 2);
v___y_1268_ = v_throwsStx_1325_;
v___y_1269_ = v_requiresStx_1322_;
v___y_1270_ = v_givenStx_1321_;
v___y_1271_ = v___x_1320_;
v___y_1272_ = v_ensuresStx_1324_;
v___y_1273_ = v___y_1316_;
v___y_1274_ = v___x_1323_;
v___y_1275_ = v___y_1317_;
v___y_1276_ = v___y_1318_;
v___y_1277_ = v_a_1332_;
goto v___jp_1267_;
}
else
{
lean_object* v_a_1333_; lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1341_; 
lean_dec(v_throwsStx_1325_);
lean_dec(v_ensuresStx_1324_);
lean_dec(v_requiresStx_1322_);
lean_dec(v_givenStx_1321_);
lean_dec(v___y_1316_);
lean_dec(v_decl_1207_);
lean_dec(v_stx_628_);
v_a_1333_ = lean_ctor_get(v___x_1331_, 0);
v_a_1334_ = lean_ctor_get(v___x_1331_, 1);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1336_ = v___x_1331_;
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_inc(v_a_1333_);
lean_dec(v___x_1331_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1339_; 
if (v_isShared_1337_ == 0)
{
v___x_1339_ = v___x_1336_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_a_1333_);
lean_ctor_set(v_reuseFailAlloc_1340_, 1, v_a_1334_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
}
}
}
}
v___jp_1342_:
{
lean_object* v___x_1345_; lean_object* v_val_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; 
v___x_1345_ = lean_unsigned_to_nat(3u);
v_val_1346_ = l_Lean_Syntax_getArg(v_decl_1207_, v___x_1345_);
v___x_1347_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__1));
lean_inc(v_val_1346_);
v___x_1348_ = l_Lean_Syntax_isOfKind(v_val_1346_, v___x_1347_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1349_; 
v___x_1349_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1344_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 1);
lean_inc(v_a_1350_);
lean_dec_ref_known(v___x_1349_, 2);
v___y_1316_ = v_val_1346_;
v___y_1317_ = v___x_1345_;
v___y_1318_ = v___y_1343_;
v___y_1319_ = v_a_1350_;
goto v___jp_1315_;
}
else
{
lean_object* v_a_1351_; lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
lean_dec(v_val_1346_);
lean_dec(v_decl_1207_);
lean_dec(v_stx_628_);
v_a_1351_ = lean_ctor_get(v___x_1349_, 0);
v_a_1352_ = lean_ctor_get(v___x_1349_, 1);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1354_ = v___x_1349_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_inc(v_a_1351_);
lean_dec(v___x_1349_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1351_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v_a_1352_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
else
{
v___y_1316_ = v_val_1346_;
v___y_1317_ = v___x_1345_;
v___y_1318_ = v___y_1343_;
v___y_1319_ = v___y_1344_;
goto v___jp_1315_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___boxed(lean_object* v_stx_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l_Lean_Elab_Tactic_Do_expandDefContract(v_stx_1373_, v_a_1374_, v_a_1375_);
lean_dec_ref(v_a_1374_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1(){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1390_ = l_Lean_Elab_macroAttribute;
v___x_1391_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__0));
v___x_1392_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__2));
v___x_1393_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_expandDefContract___boxed), 3, 0);
v___x_1394_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1390_, v___x_1391_, v___x_1392_, v___x_1393_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___boxed(lean_object* v_a_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1();
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3(){
_start:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1399_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__2));
v___x_1400_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3___closed__0));
v___x_1401_ = l_Lean_addBuiltinDocString(v___x_1399_, v___x_1400_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3___boxed(lean_object* v_a_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3();
return v_res_1403_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1404_; 
v___x_1404_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1404_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1405_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0);
v___x_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1405_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg(){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__1);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___boxed(lean_object* v___dummy_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg();
return v_res_1410_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg();
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0(lean_object* v_00_u03b2_1412_){
_start:
{
lean_object* v___x_1413_; 
v___x_1413_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___closed__0);
return v___x_1413_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0);
v___x_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1414_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___redArg(){
_start:
{
lean_object* v___x_1417_; 
v___x_1417_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___redArg___closed__0);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___redArg___boxed(lean_object* v___dummy_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___redArg();
return v_res_1419_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___redArg();
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1(lean_object* v_00_u03b2_1421_){
_start:
{
lean_object* v___x_1422_; 
v___x_1422_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___closed__0);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__2___redArg(lean_object* v_as_1423_, size_t v_sz_1424_, size_t v_i_1425_, lean_object* v_b_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
uint8_t v___x_1432_; 
v___x_1432_ = lean_usize_dec_lt(v_i_1425_, v_sz_1424_);
if (v___x_1432_ == 0)
{
lean_object* v___x_1433_; 
v___x_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1433_, 0, v_b_1426_);
return v___x_1433_;
}
else
{
lean_object* v_a_1434_; uint8_t v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
v_a_1434_ = lean_array_uget_borrowed(v_as_1423_, v_i_1425_);
v___x_1435_ = 0;
v___x_1436_ = lean_unsigned_to_nat(1000u);
lean_inc(v_a_1434_);
v___x_1437_ = l_Lean_Meta_SimpTheorems_addConst(v_b_1426_, v_a_1434_, v___x_1432_, v___x_1435_, v___x_1436_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; size_t v___x_1439_; size_t v___x_1440_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc(v_a_1438_);
lean_dec_ref_known(v___x_1437_, 1);
v___x_1439_ = ((size_t)1ULL);
v___x_1440_ = lean_usize_add(v_i_1425_, v___x_1439_);
v_i_1425_ = v___x_1440_;
v_b_1426_ = v_a_1438_;
goto _start;
}
else
{
return v___x_1437_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__2___redArg___boxed(lean_object* v_as_1442_, lean_object* v_sz_1443_, lean_object* v_i_1444_, lean_object* v_b_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
size_t v_sz_boxed_1451_; size_t v_i_boxed_1452_; lean_object* v_res_1453_; 
v_sz_boxed_1451_ = lean_unbox_usize(v_sz_1443_);
lean_dec(v_sz_1443_);
v_i_boxed_1452_ = lean_unbox_usize(v_i_1444_);
lean_dec(v_i_1444_);
v_res_1453_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__2___redArg(v_as_1442_, v_sz_boxed_1451_, v_i_boxed_1452_, v_b_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec_ref(v_as_1442_);
return v_res_1453_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__0(void){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Lean_Meta_DiscrTree_empty___redArg();
return v___x_1454_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__1(void){
_start:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1455_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0);
v___x_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1455_);
return v___x_1456_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__2(void){
_start:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v_thms_1461_; 
v___x_1457_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__1, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__1);
v___x_1458_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___closed__0);
v___x_1459_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___closed__0);
v___x_1460_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__0, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__0);
v_thms_1461_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_thms_1461_, 0, v___x_1460_);
lean_ctor_set(v_thms_1461_, 1, v___x_1460_);
lean_ctor_set(v_thms_1461_, 2, v___x_1459_);
lean_ctor_set(v_thms_1461_, 3, v___x_1458_);
lean_ctor_set(v_thms_1461_, 4, v___x_1459_);
lean_ctor_set(v_thms_1461_, 5, v___x_1457_);
return v_thms_1461_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__5(void){
_start:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1471_ = lean_unsigned_to_nat(0u);
v___x_1472_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__1, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__1);
v___x_1473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
lean_ctor_set(v___x_1473_, 1, v___x_1471_);
return v___x_1473_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__6(void){
_start:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1474_ = lean_unsigned_to_nat(32u);
v___x_1475_ = lean_mk_empty_array_with_capacity(v___x_1474_);
v___x_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1475_);
return v___x_1476_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__7(void){
_start:
{
size_t v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1477_ = ((size_t)5ULL);
v___x_1478_ = lean_unsigned_to_nat(0u);
v___x_1479_ = lean_unsigned_to_nat(32u);
v___x_1480_ = lean_mk_empty_array_with_capacity(v___x_1479_);
v___x_1481_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__6, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__6);
v___x_1482_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
lean_ctor_set(v___x_1482_, 1, v___x_1480_);
lean_ctor_set(v___x_1482_, 2, v___x_1478_);
lean_ctor_set(v___x_1482_, 3, v___x_1478_);
lean_ctor_set_usize(v___x_1482_, 4, v___x_1477_);
return v___x_1482_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__8(void){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1483_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__7, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__7);
v___x_1484_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__1, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__1);
v___x_1485_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1484_);
lean_ctor_set(v___x_1485_, 1, v___x_1484_);
lean_ctor_set(v___x_1485_, 2, v___x_1484_);
lean_ctor_set(v___x_1485_, 3, v___x_1483_);
return v___x_1485_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__9(void){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1486_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__8, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__8_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__8);
v___x_1487_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__5, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__5);
v___x_1488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1487_);
lean_ctor_set(v___x_1488_, 1, v___x_1486_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith(lean_object* v_names_1489_, lean_object* v_e_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_){
_start:
{
lean_object* v_thms_1498_; size_t v_sz_1499_; size_t v___x_1500_; lean_object* v___x_1501_; 
v_thms_1498_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__2, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__2);
v_sz_1499_ = lean_array_size(v_names_1489_);
v___x_1500_ = ((size_t)0ULL);
v___x_1501_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__2___redArg(v_names_1489_, v_sz_1499_, v___x_1500_, v_thms_1498_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v_a_1502_; lean_object* v___x_1503_; 
v_a_1502_ = lean_ctor_get(v___x_1501_, 0);
lean_inc(v_a_1502_);
lean_dec_ref_known(v___x_1501_, 1);
v___x_1503_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_1496_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
lean_inc(v_a_1504_);
lean_dec_ref_known(v___x_1503_, 1);
v___x_1505_ = lean_box(0);
v___x_1506_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3));
v___x_1507_ = lean_unsigned_to_nat(1u);
v___x_1508_ = lean_mk_empty_array_with_capacity(v___x_1507_);
v___x_1509_ = lean_array_push(v___x_1508_, v_a_1502_);
v___x_1510_ = l_Lean_Options_empty;
v___x_1511_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1506_, v___x_1509_, v_a_1504_, v___x_1510_, v_a_1493_, v_a_1495_, v_a_1496_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v_a_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc(v_a_1512_);
lean_dec_ref_known(v___x_1511_, 1);
v___x_1513_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__4));
v___x_1514_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__9, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__9);
v___x_1515_ = l_Lean_Meta_simp(v_e_1490_, v_a_1512_, v___x_1513_, v___x_1505_, v___x_1514_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1525_; 
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1518_ = v___x_1515_;
v_isShared_1519_ = v_isSharedCheck_1525_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v___x_1515_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1525_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v_fst_1520_; lean_object* v_expr_1521_; lean_object* v___x_1523_; 
v_fst_1520_ = lean_ctor_get(v_a_1516_, 0);
lean_inc(v_fst_1520_);
lean_dec(v_a_1516_);
v_expr_1521_ = lean_ctor_get(v_fst_1520_, 0);
lean_inc_ref(v_expr_1521_);
lean_dec(v_fst_1520_);
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 0, v_expr_1521_);
v___x_1523_ = v___x_1518_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_expr_1521_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
else
{
lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1533_; 
v_a_1526_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1528_ = v___x_1515_;
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_dec(v___x_1515_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1531_; 
if (v_isShared_1529_ == 0)
{
v___x_1531_ = v___x_1528_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_a_1526_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
}
else
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1541_; 
lean_dec_ref(v_e_1490_);
v_a_1534_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1536_ = v___x_1511_;
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1511_);
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
else
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1549_; 
lean_dec(v_a_1502_);
lean_dec_ref(v_e_1490_);
v_a_1542_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1544_ = v___x_1503_;
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1503_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1547_; 
if (v_isShared_1545_ == 0)
{
v___x_1547_ = v___x_1544_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_a_1542_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
}
else
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1557_; 
lean_dec_ref(v_e_1490_);
v_a_1550_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1552_ = v___x_1501_;
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1501_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
if (v_isShared_1553_ == 0)
{
v___x_1555_ = v___x_1552_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_a_1550_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___boxed(lean_object* v_names_1558_, lean_object* v_e_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith(v_names_1558_, v_e_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_);
lean_dec(v_a_1565_);
lean_dec_ref(v_a_1564_);
lean_dec(v_a_1563_);
lean_dec_ref(v_a_1562_);
lean_dec(v_a_1561_);
lean_dec_ref(v_a_1560_);
lean_dec_ref(v_names_1558_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__2(lean_object* v_as_1568_, size_t v_sz_1569_, size_t v_i_1570_, lean_object* v_b_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__2___redArg(v_as_1568_, v_sz_1569_, v_i_1570_, v_b_1571_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__2___boxed(lean_object* v_as_1580_, lean_object* v_sz_1581_, lean_object* v_i_1582_, lean_object* v_b_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
size_t v_sz_boxed_1591_; size_t v_i_boxed_1592_; lean_object* v_res_1593_; 
v_sz_boxed_1591_ = lean_unbox_usize(v_sz_1581_);
lean_dec(v_sz_1581_);
v_i_boxed_1592_ = lean_unbox_usize(v_i_1582_);
lean_dec(v_i_1582_);
v_res_1593_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__2(v_as_1580_, v_sz_boxed_1591_, v_i_boxed_1592_, v_b_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec_ref(v_as_1580_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0___redArg(lean_object* v_e_1594_, lean_object* v___y_1595_){
_start:
{
uint8_t v___x_1597_; 
v___x_1597_ = l_Lean_Expr_hasMVar(v_e_1594_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; 
v___x_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1598_, 0, v_e_1594_);
return v___x_1598_;
}
else
{
lean_object* v___x_1599_; lean_object* v_mctx_1600_; lean_object* v___x_1601_; lean_object* v_fst_1602_; lean_object* v_snd_1603_; lean_object* v___x_1604_; lean_object* v_cache_1605_; lean_object* v_zetaDeltaFVarIds_1606_; lean_object* v_postponed_1607_; lean_object* v_diag_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1617_; 
v___x_1599_ = lean_st_ref_get(v___y_1595_);
v_mctx_1600_ = lean_ctor_get(v___x_1599_, 0);
lean_inc_ref(v_mctx_1600_);
lean_dec(v___x_1599_);
v___x_1601_ = l_Lean_instantiateMVarsCore(v_mctx_1600_, v_e_1594_);
v_fst_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_fst_1602_);
v_snd_1603_ = lean_ctor_get(v___x_1601_, 1);
lean_inc(v_snd_1603_);
lean_dec_ref(v___x_1601_);
v___x_1604_ = lean_st_ref_take(v___y_1595_);
v_cache_1605_ = lean_ctor_get(v___x_1604_, 1);
v_zetaDeltaFVarIds_1606_ = lean_ctor_get(v___x_1604_, 2);
v_postponed_1607_ = lean_ctor_get(v___x_1604_, 3);
v_diag_1608_ = lean_ctor_get(v___x_1604_, 4);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1617_ == 0)
{
lean_object* v_unused_1618_; 
v_unused_1618_ = lean_ctor_get(v___x_1604_, 0);
lean_dec(v_unused_1618_);
v___x_1610_ = v___x_1604_;
v_isShared_1611_ = v_isSharedCheck_1617_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_diag_1608_);
lean_inc(v_postponed_1607_);
lean_inc(v_zetaDeltaFVarIds_1606_);
lean_inc(v_cache_1605_);
lean_dec(v___x_1604_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1617_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1613_; 
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 0, v_snd_1603_);
v___x_1613_ = v___x_1610_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_snd_1603_);
lean_ctor_set(v_reuseFailAlloc_1616_, 1, v_cache_1605_);
lean_ctor_set(v_reuseFailAlloc_1616_, 2, v_zetaDeltaFVarIds_1606_);
lean_ctor_set(v_reuseFailAlloc_1616_, 3, v_postponed_1607_);
lean_ctor_set(v_reuseFailAlloc_1616_, 4, v_diag_1608_);
v___x_1613_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1614_ = lean_st_ref_put(v___y_1595_, v___x_1613_);
v___x_1615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1615_, 0, v_fst_1602_);
return v___x_1615_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0___redArg___boxed(lean_object* v_e_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0___redArg(v_e_1619_, v___y_1620_);
lean_dec(v___y_1620_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0(lean_object* v_e_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0___redArg(v_e_1623_, v___y_1627_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0___boxed(lean_object* v_e_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0(v_e_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__0(lean_object* v_e_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v___x_1654_; uint8_t v___x_1655_; 
v___x_1654_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__10));
v___x_1655_ = l_Lean_Expr_isAppOf(v_e_1643_, v___x_1654_);
if (v___x_1655_ == 0)
{
lean_dec_ref(v_e_1643_);
goto v___jp_1651_;
}
else
{
lean_object* v___x_1656_; 
v___x_1656_ = l_Lean_Meta_unfoldProjInst_x3f(v_e_1643_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1672_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1659_ = v___x_1656_;
v_isShared_1660_ = v_isSharedCheck_1672_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1656_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1672_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
if (lean_obj_tag(v_a_1657_) == 1)
{
lean_object* v_val_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1671_; 
v_val_1661_ = lean_ctor_get(v_a_1657_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v_a_1657_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1663_ = v_a_1657_;
v_isShared_1664_ = v_isSharedCheck_1671_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_val_1661_);
lean_dec(v_a_1657_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1671_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_val_1661_);
v___x_1666_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
lean_object* v___x_1668_; 
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 0, v___x_1666_);
v___x_1668_ = v___x_1659_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v___x_1666_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
else
{
lean_del_object(v___x_1659_);
lean_dec(v_a_1657_);
goto v___jp_1651_;
}
}
}
else
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
v_a_1673_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1675_ = v___x_1656_;
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1656_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1676_ == 0)
{
v___x_1678_ = v___x_1675_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1673_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
}
v___jp_1651_:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1652_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__0___closed__0));
v___x_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
return v___x_1653_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__0___boxed(lean_object* v_e_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__0(v_e_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__1(lean_object* v_x_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1698_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__0___closed__0));
v___x_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1698_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__1___boxed(lean_object* v_x_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__1(v_x_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec_ref(v_x_1700_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___lam__0(lean_object* v_00_u03b1_1709_, lean_object* v_x_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1718_ = lean_apply_1(v_x_1710_, lean_box(0));
v___x_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1718_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___lam__0___boxed(lean_object* v_00_u03b1_1720_, lean_object* v_x_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___lam__0(v_00_u03b1_1720_, v_x_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
return v_res_1729_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__3(void){
_start:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1735_ = l_Lean_maxRecDepthErrorMessage;
v___x_1736_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1735_);
return v___x_1736_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__4(void){
_start:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1737_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__3);
v___x_1738_ = l_Lean_MessageData_ofFormat(v___x_1737_);
return v___x_1738_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__5(void){
_start:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1739_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__4);
v___x_1740_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__2));
v___x_1741_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1740_);
lean_ctor_set(v___x_1741_, 1, v___x_1739_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg(lean_object* v_ref_1742_){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1744_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__5);
v___x_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1745_, 0, v_ref_1742_);
lean_ctor_set(v___x_1745_, 1, v___x_1744_);
v___x_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1745_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___boxed(lean_object* v_ref_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_1747_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10___redArg(lean_object* v_x_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
lean_object* v___y_1760_; lean_object* v_toCold_1769_; lean_object* v_currRecDepth_1770_; lean_object* v_ref_1771_; uint16_t v_optionFlags_1772_; uint8_t v_suppressElabErrors_1773_; uint8_t v_isRecordingDeps_1774_; lean_object* v_maxRecDepth_1780_; lean_object* v___x_1781_; uint8_t v___x_1782_; 
v_toCold_1769_ = lean_ctor_get(v___y_1756_, 0);
v_currRecDepth_1770_ = lean_ctor_get(v___y_1756_, 1);
v_ref_1771_ = lean_ctor_get(v___y_1756_, 2);
v_optionFlags_1772_ = lean_ctor_get_uint16(v___y_1756_, sizeof(void*)*3);
v_suppressElabErrors_1773_ = lean_ctor_get_uint8(v___y_1756_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1774_ = lean_ctor_get_uint8(v___y_1756_, sizeof(void*)*3 + 3);
v_maxRecDepth_1780_ = lean_ctor_get(v_toCold_1769_, 3);
v___x_1781_ = lean_unsigned_to_nat(0u);
v___x_1782_ = lean_nat_dec_eq(v_maxRecDepth_1780_, v___x_1781_);
if (v___x_1782_ == 0)
{
uint8_t v___x_1783_; 
v___x_1783_ = lean_nat_dec_eq(v_currRecDepth_1770_, v_maxRecDepth_1780_);
if (v___x_1783_ == 0)
{
goto v___jp_1775_;
}
else
{
lean_object* v___x_1784_; 
lean_dec_ref(v_x_1750_);
lean_inc(v_ref_1771_);
v___x_1784_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_1771_);
v___y_1760_ = v___x_1784_;
goto v___jp_1759_;
}
}
else
{
goto v___jp_1775_;
}
v___jp_1759_:
{
if (lean_obj_tag(v___y_1760_) == 0)
{
return v___y_1760_;
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
v_a_1761_ = lean_ctor_get(v___y_1760_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___y_1760_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___y_1760_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___y_1760_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
v___jp_1775_:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1776_ = lean_unsigned_to_nat(1u);
v___x_1777_ = lean_nat_add(v_currRecDepth_1770_, v___x_1776_);
lean_inc(v_ref_1771_);
lean_inc_ref(v_toCold_1769_);
v___x_1778_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1778_, 0, v_toCold_1769_);
lean_ctor_set(v___x_1778_, 1, v___x_1777_);
lean_ctor_set(v___x_1778_, 2, v_ref_1771_);
lean_ctor_set_uint16(v___x_1778_, sizeof(void*)*3, v_optionFlags_1772_);
lean_ctor_set_uint8(v___x_1778_, sizeof(void*)*3 + 2, v_suppressElabErrors_1773_);
lean_ctor_set_uint8(v___x_1778_, sizeof(void*)*3 + 3, v_isRecordingDeps_1774_);
lean_inc(v___y_1757_);
lean_inc(v___y_1755_);
lean_inc_ref(v___y_1754_);
lean_inc(v___y_1753_);
lean_inc_ref(v___y_1752_);
lean_inc(v___y_1751_);
v___x_1779_ = lean_apply_8(v_x_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___x_1778_, v___y_1757_, lean_box(0));
v___y_1760_ = v___x_1779_;
goto v___jp_1759_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10___redArg___boxed(lean_object* v_x_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10___redArg(v_x_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v___y_1786_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__2(lean_object* v___x_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
lean_object* v___x_1803_; 
v___x_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1795_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__2___boxed(lean_object* v___x_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__2(v___x_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(lean_object* v_k_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v_b_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v___x_1823_; 
lean_inc(v___y_1821_);
lean_inc_ref(v___y_1820_);
lean_inc(v___y_1819_);
lean_inc_ref(v___y_1818_);
lean_inc(v___y_1816_);
lean_inc_ref(v___y_1815_);
lean_inc(v___y_1814_);
v___x_1823_ = lean_apply_9(v_k_1813_, v_b_1817_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, lean_box(0));
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed(lean_object* v_k_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v_b_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(v_k_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v_b_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v___y_1825_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg(lean_object* v_name_1835_, uint8_t v_bi_1836_, lean_object* v_type_1837_, lean_object* v_k_1838_, uint8_t v_kind_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
lean_object* v___f_1848_; lean_object* v___x_1849_; 
lean_inc(v___y_1842_);
lean_inc_ref(v___y_1841_);
lean_inc(v___y_1840_);
v___f_1848_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1848_, 0, v_k_1838_);
lean_closure_set(v___f_1848_, 1, v___y_1840_);
lean_closure_set(v___f_1848_, 2, v___y_1841_);
lean_closure_set(v___f_1848_, 3, v___y_1842_);
v___x_1849_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1835_, v_bi_1836_, v_type_1837_, v___f_1848_, v_kind_1839_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
if (lean_obj_tag(v___x_1849_) == 0)
{
return v___x_1849_;
}
else
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1857_; 
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1852_ = v___x_1849_;
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1849_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1855_; 
if (v_isShared_1853_ == 0)
{
v___x_1855_ = v___x_1852_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_a_1850_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg___boxed(lean_object* v_name_1858_, lean_object* v_bi_1859_, lean_object* v_type_1860_, lean_object* v_k_1861_, lean_object* v_kind_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
uint8_t v_bi_boxed_1871_; uint8_t v_kind_boxed_1872_; lean_object* v_res_1873_; 
v_bi_boxed_1871_ = lean_unbox(v_bi_1859_);
v_kind_boxed_1872_ = lean_unbox(v_kind_1862_);
v_res_1873_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg(v_name_1858_, v_bi_boxed_1871_, v_type_1860_, v_k_1861_, v_kind_boxed_1872_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11___redArg(lean_object* v_name_1874_, lean_object* v_type_1875_, lean_object* v_val_1876_, lean_object* v_k_1877_, uint8_t v_nondep_1878_, uint8_t v_kind_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
lean_object* v___f_1888_; lean_object* v___x_1889_; 
lean_inc(v___y_1882_);
lean_inc_ref(v___y_1881_);
lean_inc(v___y_1880_);
v___f_1888_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1888_, 0, v_k_1877_);
lean_closure_set(v___f_1888_, 1, v___y_1880_);
lean_closure_set(v___f_1888_, 2, v___y_1881_);
lean_closure_set(v___f_1888_, 3, v___y_1882_);
v___x_1889_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1874_, v_type_1875_, v_val_1876_, v___f_1888_, v_nondep_1878_, v_kind_1879_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
if (lean_obj_tag(v___x_1889_) == 0)
{
return v___x_1889_;
}
else
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
v_a_1890_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1889_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1889_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1890_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11___redArg___boxed(lean_object* v_name_1898_, lean_object* v_type_1899_, lean_object* v_val_1900_, lean_object* v_k_1901_, lean_object* v_nondep_1902_, lean_object* v_kind_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
uint8_t v_nondep_boxed_1912_; uint8_t v_kind_boxed_1913_; lean_object* v_res_1914_; 
v_nondep_boxed_1912_ = lean_unbox(v_nondep_1902_);
v_kind_boxed_1913_ = lean_unbox(v_kind_1903_);
v_res_1914_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11___redArg(v_name_1898_, v_type_1899_, v_val_1900_, v_k_1901_, v_nondep_boxed_1912_, v_kind_boxed_1913_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1904_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5_spec__6___redArg(lean_object* v_a_1915_, lean_object* v_x_1916_){
_start:
{
if (lean_obj_tag(v_x_1916_) == 0)
{
lean_object* v___x_1917_; 
v___x_1917_ = lean_box(0);
return v___x_1917_;
}
else
{
lean_object* v_key_1918_; lean_object* v_value_1919_; lean_object* v_tail_1920_; uint8_t v___x_1921_; 
v_key_1918_ = lean_ctor_get(v_x_1916_, 0);
v_value_1919_ = lean_ctor_get(v_x_1916_, 1);
v_tail_1920_ = lean_ctor_get(v_x_1916_, 2);
v___x_1921_ = l_Lean_ExprStructEq_beq(v_key_1918_, v_a_1915_);
if (v___x_1921_ == 0)
{
v_x_1916_ = v_tail_1920_;
goto _start;
}
else
{
lean_object* v___x_1923_; 
lean_inc(v_value_1919_);
v___x_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1923_, 0, v_value_1919_);
return v___x_1923_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object* v_a_1924_, lean_object* v_x_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5_spec__6___redArg(v_a_1924_, v_x_1925_);
lean_dec(v_x_1925_);
lean_dec_ref(v_a_1924_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5___redArg(lean_object* v_m_1927_, lean_object* v_a_1928_){
_start:
{
lean_object* v_buckets_1929_; lean_object* v___x_1930_; uint64_t v___x_1931_; uint64_t v___x_1932_; uint64_t v___x_1933_; uint64_t v_fold_1934_; uint64_t v___x_1935_; uint64_t v___x_1936_; uint64_t v___x_1937_; size_t v___x_1938_; size_t v___x_1939_; size_t v___x_1940_; size_t v___x_1941_; size_t v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v_buckets_1929_ = lean_ctor_get(v_m_1927_, 1);
v___x_1930_ = lean_array_get_size(v_buckets_1929_);
v___x_1931_ = l_Lean_ExprStructEq_hash(v_a_1928_);
v___x_1932_ = 32ULL;
v___x_1933_ = lean_uint64_shift_right(v___x_1931_, v___x_1932_);
v_fold_1934_ = lean_uint64_xor(v___x_1931_, v___x_1933_);
v___x_1935_ = 16ULL;
v___x_1936_ = lean_uint64_shift_right(v_fold_1934_, v___x_1935_);
v___x_1937_ = lean_uint64_xor(v_fold_1934_, v___x_1936_);
v___x_1938_ = lean_uint64_to_usize(v___x_1937_);
v___x_1939_ = lean_usize_of_nat(v___x_1930_);
v___x_1940_ = ((size_t)1ULL);
v___x_1941_ = lean_usize_sub(v___x_1939_, v___x_1940_);
v___x_1942_ = lean_usize_land(v___x_1938_, v___x_1941_);
v___x_1943_ = lean_array_uget_borrowed(v_buckets_1929_, v___x_1942_);
v___x_1944_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5_spec__6___redArg(v_a_1928_, v___x_1943_);
return v___x_1944_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5___redArg___boxed(lean_object* v_m_1945_, lean_object* v_a_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5___redArg(v_m_1945_, v_a_1946_);
lean_dec_ref(v_a_1946_);
lean_dec_ref(v_m_1945_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_1948_, lean_object* v_x_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1957_ = lean_apply_1(v_x_1949_, lean_box(0));
v___x_1958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1957_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_1959_, lean_object* v_x_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__0(v_00_u03b1_1959_, v_x_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__18___redArg(lean_object* v_a_1969_, lean_object* v_b_1970_, lean_object* v_x_1971_){
_start:
{
if (lean_obj_tag(v_x_1971_) == 0)
{
lean_dec(v_b_1970_);
lean_dec_ref(v_a_1969_);
return v_x_1971_;
}
else
{
lean_object* v_key_1972_; lean_object* v_value_1973_; lean_object* v_tail_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1986_; 
v_key_1972_ = lean_ctor_get(v_x_1971_, 0);
v_value_1973_ = lean_ctor_get(v_x_1971_, 1);
v_tail_1974_ = lean_ctor_get(v_x_1971_, 2);
v_isSharedCheck_1986_ = !lean_is_exclusive(v_x_1971_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1976_ = v_x_1971_;
v_isShared_1977_ = v_isSharedCheck_1986_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_tail_1974_);
lean_inc(v_value_1973_);
lean_inc(v_key_1972_);
lean_dec(v_x_1971_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1986_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
uint8_t v___x_1978_; 
v___x_1978_ = l_Lean_ExprStructEq_beq(v_key_1972_, v_a_1969_);
if (v___x_1978_ == 0)
{
lean_object* v___x_1979_; lean_object* v___x_1981_; 
v___x_1979_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__18___redArg(v_a_1969_, v_b_1970_, v_tail_1974_);
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 2, v___x_1979_);
v___x_1981_ = v___x_1976_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_key_1972_);
lean_ctor_set(v_reuseFailAlloc_1982_, 1, v_value_1973_);
lean_ctor_set(v_reuseFailAlloc_1982_, 2, v___x_1979_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
else
{
lean_object* v___x_1984_; 
lean_dec(v_value_1973_);
lean_dec(v_key_1972_);
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 1, v_b_1970_);
lean_ctor_set(v___x_1976_, 0, v_a_1969_);
v___x_1984_ = v___x_1976_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_a_1969_);
lean_ctor_set(v_reuseFailAlloc_1985_, 1, v_b_1970_);
lean_ctor_set(v_reuseFailAlloc_1985_, 2, v_tail_1974_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16___redArg(lean_object* v_a_1987_, lean_object* v_x_1988_){
_start:
{
if (lean_obj_tag(v_x_1988_) == 0)
{
uint8_t v___x_1989_; 
v___x_1989_ = 0;
return v___x_1989_;
}
else
{
lean_object* v_key_1990_; lean_object* v_tail_1991_; uint8_t v___x_1992_; 
v_key_1990_ = lean_ctor_get(v_x_1988_, 0);
v_tail_1991_ = lean_ctor_get(v_x_1988_, 2);
v___x_1992_ = l_Lean_ExprStructEq_beq(v_key_1990_, v_a_1987_);
if (v___x_1992_ == 0)
{
v_x_1988_ = v_tail_1991_;
goto _start;
}
else
{
return v___x_1992_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16___redArg___boxed(lean_object* v_a_1994_, lean_object* v_x_1995_){
_start:
{
uint8_t v_res_1996_; lean_object* v_r_1997_; 
v_res_1996_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16___redArg(v_a_1994_, v_x_1995_);
lean_dec(v_x_1995_);
lean_dec_ref(v_a_1994_);
v_r_1997_ = lean_box(v_res_1996_);
return v_r_1997_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(lean_object* v_x_1998_, lean_object* v_x_1999_){
_start:
{
if (lean_obj_tag(v_x_1999_) == 0)
{
return v_x_1998_;
}
else
{
lean_object* v_key_2000_; lean_object* v_value_2001_; lean_object* v_tail_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2025_; 
v_key_2000_ = lean_ctor_get(v_x_1999_, 0);
v_value_2001_ = lean_ctor_get(v_x_1999_, 1);
v_tail_2002_ = lean_ctor_get(v_x_1999_, 2);
v_isSharedCheck_2025_ = !lean_is_exclusive(v_x_1999_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2004_ = v_x_1999_;
v_isShared_2005_ = v_isSharedCheck_2025_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_tail_2002_);
lean_inc(v_value_2001_);
lean_inc(v_key_2000_);
lean_dec(v_x_1999_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2025_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2006_; uint64_t v___x_2007_; uint64_t v___x_2008_; uint64_t v___x_2009_; uint64_t v_fold_2010_; uint64_t v___x_2011_; uint64_t v___x_2012_; uint64_t v___x_2013_; size_t v___x_2014_; size_t v___x_2015_; size_t v___x_2016_; size_t v___x_2017_; size_t v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2021_; 
v___x_2006_ = lean_array_get_size(v_x_1998_);
v___x_2007_ = l_Lean_ExprStructEq_hash(v_key_2000_);
v___x_2008_ = 32ULL;
v___x_2009_ = lean_uint64_shift_right(v___x_2007_, v___x_2008_);
v_fold_2010_ = lean_uint64_xor(v___x_2007_, v___x_2009_);
v___x_2011_ = 16ULL;
v___x_2012_ = lean_uint64_shift_right(v_fold_2010_, v___x_2011_);
v___x_2013_ = lean_uint64_xor(v_fold_2010_, v___x_2012_);
v___x_2014_ = lean_uint64_to_usize(v___x_2013_);
v___x_2015_ = lean_usize_of_nat(v___x_2006_);
v___x_2016_ = ((size_t)1ULL);
v___x_2017_ = lean_usize_sub(v___x_2015_, v___x_2016_);
v___x_2018_ = lean_usize_land(v___x_2014_, v___x_2017_);
v___x_2019_ = lean_array_uget_borrowed(v_x_1998_, v___x_2018_);
lean_inc(v___x_2019_);
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 2, v___x_2019_);
v___x_2021_ = v___x_2004_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_key_2000_);
lean_ctor_set(v_reuseFailAlloc_2024_, 1, v_value_2001_);
lean_ctor_set(v_reuseFailAlloc_2024_, 2, v___x_2019_);
v___x_2021_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
lean_object* v___x_2022_; 
v___x_2022_ = lean_array_uset(v_x_1998_, v___x_2018_, v___x_2021_);
v_x_1998_ = v___x_2022_;
v_x_1999_ = v_tail_2002_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(lean_object* v_i_2026_, lean_object* v_source_2027_, lean_object* v_target_2028_){
_start:
{
lean_object* v___x_2029_; uint8_t v___x_2030_; 
v___x_2029_ = lean_array_get_size(v_source_2027_);
v___x_2030_ = lean_nat_dec_lt(v_i_2026_, v___x_2029_);
if (v___x_2030_ == 0)
{
lean_dec_ref(v_source_2027_);
lean_dec(v_i_2026_);
return v_target_2028_;
}
else
{
lean_object* v_es_2031_; lean_object* v___x_2032_; lean_object* v_source_2033_; lean_object* v_target_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v_es_2031_ = lean_array_fget(v_source_2027_, v_i_2026_);
v___x_2032_ = lean_box(0);
v_source_2033_ = lean_array_fset(v_source_2027_, v_i_2026_, v___x_2032_);
v_target_2034_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_target_2028_, v_es_2031_);
v___x_2035_ = lean_unsigned_to_nat(1u);
v___x_2036_ = lean_nat_add(v_i_2026_, v___x_2035_);
lean_dec(v_i_2026_);
v_i_2026_ = v___x_2036_;
v_source_2027_ = v_source_2033_;
v_target_2028_ = v_target_2034_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17___redArg(lean_object* v_data_2038_){
_start:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v_nbuckets_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2039_ = lean_array_get_size(v_data_2038_);
v___x_2040_ = lean_unsigned_to_nat(2u);
v_nbuckets_2041_ = lean_nat_mul(v___x_2039_, v___x_2040_);
v___x_2042_ = lean_unsigned_to_nat(0u);
v___x_2043_ = lean_box(0);
v___x_2044_ = lean_mk_array(v_nbuckets_2041_, v___x_2043_);
v___x_2045_ = lean_array_propagate_mark(v_data_2038_, v___x_2044_);
v___x_2046_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v___x_2042_, v_data_2038_, v___x_2045_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11___redArg(lean_object* v_m_2047_, lean_object* v_a_2048_, lean_object* v_b_2049_){
_start:
{
lean_object* v_size_2050_; lean_object* v_buckets_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2094_; 
v_size_2050_ = lean_ctor_get(v_m_2047_, 0);
v_buckets_2051_ = lean_ctor_get(v_m_2047_, 1);
v_isSharedCheck_2094_ = !lean_is_exclusive(v_m_2047_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2053_ = v_m_2047_;
v_isShared_2054_ = v_isSharedCheck_2094_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_buckets_2051_);
lean_inc(v_size_2050_);
lean_dec(v_m_2047_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2094_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2055_; uint64_t v___x_2056_; uint64_t v___x_2057_; uint64_t v___x_2058_; uint64_t v_fold_2059_; uint64_t v___x_2060_; uint64_t v___x_2061_; uint64_t v___x_2062_; size_t v___x_2063_; size_t v___x_2064_; size_t v___x_2065_; size_t v___x_2066_; size_t v___x_2067_; lean_object* v_bkt_2068_; uint8_t v___x_2069_; 
v___x_2055_ = lean_array_get_size(v_buckets_2051_);
v___x_2056_ = l_Lean_ExprStructEq_hash(v_a_2048_);
v___x_2057_ = 32ULL;
v___x_2058_ = lean_uint64_shift_right(v___x_2056_, v___x_2057_);
v_fold_2059_ = lean_uint64_xor(v___x_2056_, v___x_2058_);
v___x_2060_ = 16ULL;
v___x_2061_ = lean_uint64_shift_right(v_fold_2059_, v___x_2060_);
v___x_2062_ = lean_uint64_xor(v_fold_2059_, v___x_2061_);
v___x_2063_ = lean_uint64_to_usize(v___x_2062_);
v___x_2064_ = lean_usize_of_nat(v___x_2055_);
v___x_2065_ = ((size_t)1ULL);
v___x_2066_ = lean_usize_sub(v___x_2064_, v___x_2065_);
v___x_2067_ = lean_usize_land(v___x_2063_, v___x_2066_);
v_bkt_2068_ = lean_array_uget_borrowed(v_buckets_2051_, v___x_2067_);
v___x_2069_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2048_, v_bkt_2068_);
if (v___x_2069_ == 0)
{
lean_object* v___x_2070_; lean_object* v_size_x27_2071_; lean_object* v___x_2072_; lean_object* v_buckets_x27_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; uint8_t v___x_2079_; 
v___x_2070_ = lean_unsigned_to_nat(1u);
v_size_x27_2071_ = lean_nat_add(v_size_2050_, v___x_2070_);
lean_dec(v_size_2050_);
lean_inc(v_bkt_2068_);
v___x_2072_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2072_, 0, v_a_2048_);
lean_ctor_set(v___x_2072_, 1, v_b_2049_);
lean_ctor_set(v___x_2072_, 2, v_bkt_2068_);
v_buckets_x27_2073_ = lean_array_uset(v_buckets_2051_, v___x_2067_, v___x_2072_);
v___x_2074_ = lean_unsigned_to_nat(4u);
v___x_2075_ = lean_nat_mul(v_size_x27_2071_, v___x_2074_);
v___x_2076_ = lean_unsigned_to_nat(3u);
v___x_2077_ = lean_nat_div(v___x_2075_, v___x_2076_);
lean_dec(v___x_2075_);
v___x_2078_ = lean_array_get_size(v_buckets_x27_2073_);
v___x_2079_ = lean_nat_dec_le(v___x_2077_, v___x_2078_);
lean_dec(v___x_2077_);
if (v___x_2079_ == 0)
{
lean_object* v_val_2080_; lean_object* v___x_2082_; 
v_val_2080_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17___redArg(v_buckets_x27_2073_);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 1, v_val_2080_);
lean_ctor_set(v___x_2053_, 0, v_size_x27_2071_);
v___x_2082_ = v___x_2053_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_size_x27_2071_);
lean_ctor_set(v_reuseFailAlloc_2083_, 1, v_val_2080_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
else
{
lean_object* v___x_2085_; 
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 1, v_buckets_x27_2073_);
lean_ctor_set(v___x_2053_, 0, v_size_x27_2071_);
v___x_2085_ = v___x_2053_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_size_x27_2071_);
lean_ctor_set(v_reuseFailAlloc_2086_, 1, v_buckets_x27_2073_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
else
{
lean_object* v___x_2087_; lean_object* v_buckets_x27_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2092_; 
lean_inc(v_bkt_2068_);
v___x_2087_ = lean_box(0);
v_buckets_x27_2088_ = lean_array_uset(v_buckets_2051_, v___x_2067_, v___x_2087_);
v___x_2089_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__18___redArg(v_a_2048_, v_b_2049_, v_bkt_2068_);
v___x_2090_ = lean_array_uset(v_buckets_x27_2088_, v___x_2067_, v___x_2089_);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 1, v___x_2090_);
v___x_2092_ = v___x_2053_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_size_2050_);
lean_ctor_set(v_reuseFailAlloc_2093_, 1, v___x_2090_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__2(lean_object* v_a_2095_, lean_object* v_e_2096_, lean_object* v_a_2097_){
_start:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2099_ = lean_st_ref_take(v_a_2095_);
v___x_2100_ = lean_box(0);
v___x_2101_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11___redArg(v___x_2099_, v_e_2096_, v_a_2097_);
v___x_2102_ = lean_st_ref_put(v_a_2095_, v___x_2101_);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__2___boxed(lean_object* v_a_2103_, lean_object* v_e_2104_, lean_object* v_a_2105_, lean_object* v___y_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__2(v_a_2103_, v_e_2104_, v_a_2105_);
lean_dec(v_a_2103_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6___lam__0___boxed(lean_object* v_fvars_2108_, lean_object* v_pre_2109_, lean_object* v_post_2110_, lean_object* v_usedLetOnly_2111_, lean_object* v_skipConstInApp_2112_, lean_object* v_skipInstances_2113_, lean_object* v_body_2114_, lean_object* v_x_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
uint8_t v_usedLetOnly_boxed_2124_; uint8_t v_skipConstInApp_boxed_2125_; uint8_t v_skipInstances_boxed_2126_; lean_object* v_res_2127_; 
v_usedLetOnly_boxed_2124_ = lean_unbox(v_usedLetOnly_2111_);
v_skipConstInApp_boxed_2125_ = lean_unbox(v_skipConstInApp_2112_);
v_skipInstances_boxed_2126_ = lean_unbox(v_skipInstances_2113_);
v_res_2127_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6___lam__0(v_fvars_2108_, v_pre_2109_, v_post_2110_, v_usedLetOnly_boxed_2124_, v_skipConstInApp_boxed_2125_, v_skipInstances_boxed_2126_, v_body_2114_, v_x_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec(v___y_2116_);
return v_res_2127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7___lam__0(lean_object* v_fvars_2131_, lean_object* v_pre_2132_, lean_object* v_post_2133_, uint8_t v_usedLetOnly_2134_, uint8_t v_skipConstInApp_2135_, uint8_t v_skipInstances_2136_, lean_object* v_body_2137_, lean_object* v_x_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_){
_start:
{
lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2147_ = lean_array_push(v_fvars_2131_, v_x_2138_);
v___x_2148_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7(v_pre_2132_, v_post_2133_, v_usedLetOnly_2134_, v_skipConstInApp_2135_, v_skipInstances_2136_, v___x_2147_, v_body_2137_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7___lam__0___boxed(lean_object* v_fvars_2149_, lean_object* v_pre_2150_, lean_object* v_post_2151_, lean_object* v_usedLetOnly_2152_, lean_object* v_skipConstInApp_2153_, lean_object* v_skipInstances_2154_, lean_object* v_body_2155_, lean_object* v_x_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
uint8_t v_usedLetOnly_boxed_2165_; uint8_t v_skipConstInApp_boxed_2166_; uint8_t v_skipInstances_boxed_2167_; lean_object* v_res_2168_; 
v_usedLetOnly_boxed_2165_ = lean_unbox(v_usedLetOnly_2152_);
v_skipConstInApp_boxed_2166_ = lean_unbox(v_skipConstInApp_2153_);
v_skipInstances_boxed_2167_ = lean_unbox(v_skipInstances_2154_);
v_res_2168_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7___lam__0(v_fvars_2149_, v_pre_2150_, v_post_2151_, v_usedLetOnly_boxed_2165_, v_skipConstInApp_boxed_2166_, v_skipInstances_boxed_2167_, v_body_2155_, v_x_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec(v___y_2157_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(lean_object* v_pre_2169_, lean_object* v_post_2170_, uint8_t v_usedLetOnly_2171_, uint8_t v_skipConstInApp_2172_, uint8_t v_skipInstances_2173_, lean_object* v_e_2174_, lean_object* v_a_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
lean_object* v___x_2183_; 
lean_inc_ref(v_post_2170_);
lean_inc(v___y_2181_);
lean_inc_ref(v___y_2180_);
lean_inc(v___y_2179_);
lean_inc_ref(v___y_2178_);
lean_inc(v___y_2177_);
lean_inc_ref(v___y_2176_);
lean_inc_ref(v_e_2174_);
v___x_2183_ = lean_apply_8(v_post_2170_, v_e_2174_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, lean_box(0));
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2202_; 
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2186_ = v___x_2183_;
v_isShared_2187_ = v_isSharedCheck_2202_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2183_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2202_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
switch(lean_obj_tag(v_a_2184_))
{
case 0:
{
lean_object* v_e_2188_; lean_object* v___x_2190_; 
lean_dec_ref(v_e_2174_);
lean_dec_ref(v_post_2170_);
lean_dec_ref(v_pre_2169_);
v_e_2188_ = lean_ctor_get(v_a_2184_, 0);
lean_inc_ref(v_e_2188_);
lean_dec_ref_known(v_a_2184_, 1);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 0, v_e_2188_);
v___x_2190_ = v___x_2186_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_e_2188_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
case 1:
{
lean_object* v_e_2192_; lean_object* v___x_2193_; 
lean_del_object(v___x_2186_);
lean_dec_ref(v_e_2174_);
v_e_2192_ = lean_ctor_get(v_a_2184_, 0);
lean_inc_ref(v_e_2192_);
lean_dec_ref_known(v_a_2184_, 1);
v___x_2193_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2169_, v_post_2170_, v_usedLetOnly_2171_, v_skipConstInApp_2172_, v_skipInstances_2173_, v_e_2192_, v_a_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
return v___x_2193_;
}
default: 
{
lean_object* v_e_x3f_2194_; 
lean_dec_ref(v_post_2170_);
lean_dec_ref(v_pre_2169_);
v_e_x3f_2194_ = lean_ctor_get(v_a_2184_, 0);
lean_inc(v_e_x3f_2194_);
lean_dec_ref_known(v_a_2184_, 1);
if (lean_obj_tag(v_e_x3f_2194_) == 0)
{
lean_object* v___x_2196_; 
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 0, v_e_2174_);
v___x_2196_ = v___x_2186_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_e_2174_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
else
{
lean_object* v_val_2198_; lean_object* v___x_2200_; 
lean_dec_ref(v_e_2174_);
v_val_2198_ = lean_ctor_get(v_e_x3f_2194_, 0);
lean_inc(v_val_2198_);
lean_dec_ref_known(v_e_x3f_2194_, 1);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 0, v_val_2198_);
v___x_2200_ = v___x_2186_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_val_2198_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
}
}
}
else
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2210_; 
lean_dec_ref(v_e_2174_);
lean_dec_ref(v_post_2170_);
lean_dec_ref(v_pre_2169_);
v_a_2203_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2205_ = v___x_2183_;
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___x_2183_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2208_; 
if (v_isShared_2206_ == 0)
{
v___x_2208_ = v___x_2205_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_a_2203_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7(lean_object* v_pre_2211_, lean_object* v_post_2212_, uint8_t v_usedLetOnly_2213_, uint8_t v_skipConstInApp_2214_, uint8_t v_skipInstances_2215_, lean_object* v_fvars_2216_, lean_object* v_e_2217_, lean_object* v_a_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
if (lean_obj_tag(v_e_2217_) == 6)
{
lean_object* v_binderName_2226_; lean_object* v_binderType_2227_; lean_object* v_body_2228_; uint8_t v_binderInfo_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___f_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v_binderName_2226_ = lean_ctor_get(v_e_2217_, 0);
lean_inc(v_binderName_2226_);
v_binderType_2227_ = lean_ctor_get(v_e_2217_, 1);
lean_inc_ref(v_binderType_2227_);
v_body_2228_ = lean_ctor_get(v_e_2217_, 2);
lean_inc_ref(v_body_2228_);
v_binderInfo_2229_ = lean_ctor_get_uint8(v_e_2217_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2217_, 3);
v___x_2230_ = lean_box(v_usedLetOnly_2213_);
v___x_2231_ = lean_box(v_skipConstInApp_2214_);
v___x_2232_ = lean_box(v_skipInstances_2215_);
lean_inc_ref(v_post_2212_);
lean_inc_ref(v_pre_2211_);
lean_inc_ref(v_fvars_2216_);
v___f_2233_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7___lam__0___boxed), 16, 7);
lean_closure_set(v___f_2233_, 0, v_fvars_2216_);
lean_closure_set(v___f_2233_, 1, v_pre_2211_);
lean_closure_set(v___f_2233_, 2, v_post_2212_);
lean_closure_set(v___f_2233_, 3, v___x_2230_);
lean_closure_set(v___f_2233_, 4, v___x_2231_);
lean_closure_set(v___f_2233_, 5, v___x_2232_);
lean_closure_set(v___f_2233_, 6, v_body_2228_);
v___x_2234_ = lean_expr_instantiate_rev(v_binderType_2227_, v_fvars_2216_);
lean_dec_ref(v_fvars_2216_);
lean_dec_ref(v_binderType_2227_);
v___x_2235_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2211_, v_post_2212_, v_usedLetOnly_2213_, v_skipConstInApp_2214_, v_skipInstances_2215_, v___x_2234_, v_a_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; uint8_t v___x_2237_; lean_object* v___x_2238_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_a_2236_);
lean_dec_ref_known(v___x_2235_, 1);
v___x_2237_ = 0;
v___x_2238_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_2226_, v_binderInfo_2229_, v_a_2236_, v___f_2233_, v___x_2237_, v_a_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
return v___x_2238_;
}
else
{
lean_dec_ref(v___f_2233_);
lean_dec(v_binderName_2226_);
return v___x_2235_;
}
}
else
{
lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2239_ = lean_expr_instantiate_rev(v_e_2217_, v_fvars_2216_);
lean_dec_ref(v_e_2217_);
lean_inc_ref(v_post_2212_);
lean_inc_ref(v_pre_2211_);
v___x_2240_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2211_, v_post_2212_, v_usedLetOnly_2213_, v_skipConstInApp_2214_, v_skipInstances_2215_, v___x_2239_, v_a_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2241_; uint8_t v___x_2242_; uint8_t v___x_2243_; uint8_t v___x_2244_; lean_object* v___x_2245_; 
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
lean_inc(v_a_2241_);
lean_dec_ref_known(v___x_2240_, 1);
v___x_2242_ = 0;
v___x_2243_ = 1;
v___x_2244_ = 1;
v___x_2245_ = l_Lean_Meta_mkLambdaFVars(v_fvars_2216_, v_a_2241_, v___x_2242_, v_usedLetOnly_2213_, v___x_2242_, v___x_2243_, v___x_2244_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
lean_dec_ref(v_fvars_2216_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v_a_2246_; lean_object* v___x_2247_; 
v_a_2246_ = lean_ctor_get(v___x_2245_, 0);
lean_inc(v_a_2246_);
lean_dec_ref_known(v___x_2245_, 1);
v___x_2247_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2211_, v_post_2212_, v_usedLetOnly_2213_, v_skipConstInApp_2214_, v_skipInstances_2215_, v_a_2246_, v_a_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
return v___x_2247_;
}
else
{
lean_dec_ref(v_post_2212_);
lean_dec_ref(v_pre_2211_);
return v___x_2245_;
}
}
else
{
lean_dec_ref(v_fvars_2216_);
lean_dec_ref(v_post_2212_);
lean_dec_ref(v_pre_2211_);
return v___x_2240_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8___lam__0(lean_object* v_fvars_2248_, lean_object* v_pre_2249_, lean_object* v_post_2250_, uint8_t v_usedLetOnly_2251_, uint8_t v_skipConstInApp_2252_, uint8_t v_skipInstances_2253_, lean_object* v_body_2254_, lean_object* v_x_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2264_ = lean_array_push(v_fvars_2248_, v_x_2255_);
v___x_2265_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8(v_pre_2249_, v_post_2250_, v_usedLetOnly_2251_, v_skipConstInApp_2252_, v_skipInstances_2253_, v___x_2264_, v_body_2254_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8___lam__0___boxed(lean_object* v_fvars_2266_, lean_object* v_pre_2267_, lean_object* v_post_2268_, lean_object* v_usedLetOnly_2269_, lean_object* v_skipConstInApp_2270_, lean_object* v_skipInstances_2271_, lean_object* v_body_2272_, lean_object* v_x_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
uint8_t v_usedLetOnly_boxed_2282_; uint8_t v_skipConstInApp_boxed_2283_; uint8_t v_skipInstances_boxed_2284_; lean_object* v_res_2285_; 
v_usedLetOnly_boxed_2282_ = lean_unbox(v_usedLetOnly_2269_);
v_skipConstInApp_boxed_2283_ = lean_unbox(v_skipConstInApp_2270_);
v_skipInstances_boxed_2284_ = lean_unbox(v_skipInstances_2271_);
v_res_2285_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8___lam__0(v_fvars_2266_, v_pre_2267_, v_post_2268_, v_usedLetOnly_boxed_2282_, v_skipConstInApp_boxed_2283_, v_skipInstances_boxed_2284_, v_body_2272_, v_x_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8(lean_object* v_pre_2286_, lean_object* v_post_2287_, uint8_t v_usedLetOnly_2288_, uint8_t v_skipConstInApp_2289_, uint8_t v_skipInstances_2290_, lean_object* v_fvars_2291_, lean_object* v_e_2292_, lean_object* v_a_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
if (lean_obj_tag(v_e_2292_) == 8)
{
lean_object* v_declName_2301_; lean_object* v_type_2302_; lean_object* v_value_2303_; lean_object* v_body_2304_; uint8_t v_nondep_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___f_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v_declName_2301_ = lean_ctor_get(v_e_2292_, 0);
lean_inc(v_declName_2301_);
v_type_2302_ = lean_ctor_get(v_e_2292_, 1);
lean_inc_ref(v_type_2302_);
v_value_2303_ = lean_ctor_get(v_e_2292_, 2);
lean_inc_ref(v_value_2303_);
v_body_2304_ = lean_ctor_get(v_e_2292_, 3);
lean_inc_ref(v_body_2304_);
v_nondep_2305_ = lean_ctor_get_uint8(v_e_2292_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2292_, 4);
v___x_2306_ = lean_box(v_usedLetOnly_2288_);
v___x_2307_ = lean_box(v_skipConstInApp_2289_);
v___x_2308_ = lean_box(v_skipInstances_2290_);
lean_inc_ref_n(v_post_2287_, 2);
lean_inc_ref_n(v_pre_2286_, 2);
lean_inc_ref(v_fvars_2291_);
v___f_2309_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8___lam__0___boxed), 16, 7);
lean_closure_set(v___f_2309_, 0, v_fvars_2291_);
lean_closure_set(v___f_2309_, 1, v_pre_2286_);
lean_closure_set(v___f_2309_, 2, v_post_2287_);
lean_closure_set(v___f_2309_, 3, v___x_2306_);
lean_closure_set(v___f_2309_, 4, v___x_2307_);
lean_closure_set(v___f_2309_, 5, v___x_2308_);
lean_closure_set(v___f_2309_, 6, v_body_2304_);
v___x_2310_ = lean_expr_instantiate_rev(v_type_2302_, v_fvars_2291_);
lean_dec_ref(v_type_2302_);
v___x_2311_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2286_, v_post_2287_, v_usedLetOnly_2288_, v_skipConstInApp_2289_, v_skipInstances_2290_, v___x_2310_, v_a_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v_a_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
lean_inc(v_a_2312_);
lean_dec_ref_known(v___x_2311_, 1);
v___x_2313_ = lean_expr_instantiate_rev(v_value_2303_, v_fvars_2291_);
lean_dec_ref(v_fvars_2291_);
lean_dec_ref(v_value_2303_);
v___x_2314_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2286_, v_post_2287_, v_usedLetOnly_2288_, v_skipConstInApp_2289_, v_skipInstances_2290_, v___x_2313_, v_a_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v_a_2315_; uint8_t v___x_2316_; lean_object* v___x_2317_; 
v_a_2315_ = lean_ctor_get(v___x_2314_, 0);
lean_inc(v_a_2315_);
lean_dec_ref_known(v___x_2314_, 1);
v___x_2316_ = 0;
v___x_2317_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11___redArg(v_declName_2301_, v_a_2312_, v_a_2315_, v___f_2309_, v_nondep_2305_, v___x_2316_, v_a_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
return v___x_2317_;
}
else
{
lean_dec(v_a_2312_);
lean_dec_ref(v___f_2309_);
lean_dec(v_declName_2301_);
return v___x_2314_;
}
}
else
{
lean_dec_ref(v___f_2309_);
lean_dec_ref(v_value_2303_);
lean_dec(v_declName_2301_);
lean_dec_ref(v_fvars_2291_);
lean_dec_ref(v_post_2287_);
lean_dec_ref(v_pre_2286_);
return v___x_2311_;
}
}
else
{
lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2318_ = lean_expr_instantiate_rev(v_e_2292_, v_fvars_2291_);
lean_dec_ref(v_e_2292_);
lean_inc_ref(v_post_2287_);
lean_inc_ref(v_pre_2286_);
v___x_2319_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2286_, v_post_2287_, v_usedLetOnly_2288_, v_skipConstInApp_2289_, v_skipInstances_2290_, v___x_2318_, v_a_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v_a_2320_; uint8_t v___x_2321_; uint8_t v___x_2322_; lean_object* v___x_2323_; 
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
lean_inc(v_a_2320_);
lean_dec_ref_known(v___x_2319_, 1);
v___x_2321_ = 0;
v___x_2322_ = 1;
v___x_2323_ = l_Lean_Meta_mkLetFVars(v_fvars_2291_, v_a_2320_, v_usedLetOnly_2288_, v___x_2321_, v___x_2322_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
lean_dec_ref(v_fvars_2291_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; lean_object* v___x_2325_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_a_2324_);
lean_dec_ref_known(v___x_2323_, 1);
v___x_2325_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2286_, v_post_2287_, v_usedLetOnly_2288_, v_skipConstInApp_2289_, v_skipInstances_2290_, v_a_2324_, v_a_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
return v___x_2325_;
}
else
{
lean_dec_ref(v_post_2287_);
lean_dec_ref(v_pre_2286_);
return v___x_2323_;
}
}
else
{
lean_dec_ref(v_fvars_2291_);
lean_dec_ref(v_post_2287_);
lean_dec_ref(v_pre_2286_);
return v___x_2319_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2326_; lean_object* v_dummy_2327_; 
v___x_2326_ = lean_box(0);
v_dummy_2327_ = l_Lean_Expr_sort___override(v___x_2326_);
return v_dummy_2327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__2(lean_object* v_pre_2328_, lean_object* v_post_2329_, uint8_t v_usedLetOnly_2330_, uint8_t v_skipConstInApp_2331_, uint8_t v_skipInstances_2332_, size_t v_sz_2333_, size_t v_i_2334_, lean_object* v_bs_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_){
_start:
{
uint8_t v___x_2344_; 
v___x_2344_ = lean_usize_dec_lt(v_i_2334_, v_sz_2333_);
if (v___x_2344_ == 0)
{
lean_object* v___x_2345_; 
lean_dec_ref(v_post_2329_);
lean_dec_ref(v_pre_2328_);
v___x_2345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2345_, 0, v_bs_2335_);
return v___x_2345_;
}
else
{
lean_object* v_v_2346_; lean_object* v___x_2347_; lean_object* v_bs_x27_2348_; lean_object* v___x_2349_; 
v_v_2346_ = lean_array_uget(v_bs_2335_, v_i_2334_);
v___x_2347_ = lean_unsigned_to_nat(0u);
v_bs_x27_2348_ = lean_array_uset(v_bs_2335_, v_i_2334_, v___x_2347_);
lean_inc_ref(v_post_2329_);
lean_inc_ref(v_pre_2328_);
v___x_2349_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2328_, v_post_2329_, v_usedLetOnly_2330_, v_skipConstInApp_2331_, v_skipInstances_2332_, v_v_2346_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_a_2350_; size_t v___x_2351_; size_t v___x_2352_; lean_object* v___x_2353_; 
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
lean_inc(v_a_2350_);
lean_dec_ref_known(v___x_2349_, 1);
v___x_2351_ = ((size_t)1ULL);
v___x_2352_ = lean_usize_add(v_i_2334_, v___x_2351_);
v___x_2353_ = lean_array_uset(v_bs_x27_2348_, v_i_2334_, v_a_2350_);
v_i_2334_ = v___x_2352_;
v_bs_2335_ = v___x_2353_;
goto _start;
}
else
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
lean_dec_ref(v_bs_x27_2348_);
lean_dec_ref(v_post_2329_);
lean_dec_ref(v_pre_2328_);
v_a_2355_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___x_2349_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2349_);
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
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__0(lean_object* v_pre_2363_, lean_object* v_post_2364_, uint8_t v_usedLetOnly_2365_, uint8_t v_skipConstInApp_2366_, uint8_t v_skipInstances_2367_, lean_object* v___x_2368_, lean_object* v___y_2369_, lean_object* v_b_2370_, lean_object* v_a_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_){
_start:
{
lean_object* v___x_2379_; 
v___x_2379_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2363_, v_post_2364_, v_usedLetOnly_2365_, v_skipConstInApp_2366_, v_skipInstances_2367_, v___x_2368_, v___y_2369_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_);
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2389_; 
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2382_ = v___x_2379_;
v_isShared_2383_ = v_isSharedCheck_2389_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2379_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2389_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2387_; 
v___x_2384_ = lean_array_fset(v_b_2370_, v_a_2371_, v_a_2380_);
v___x_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2384_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 0, v___x_2385_);
v___x_2387_ = v___x_2382_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2385_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
else
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2397_; 
lean_dec_ref(v_b_2370_);
v_a_2390_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2392_ = v___x_2379_;
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2379_);
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
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__0___boxed(lean_object* v_pre_2398_, lean_object* v_post_2399_, lean_object* v_usedLetOnly_2400_, lean_object* v_skipConstInApp_2401_, lean_object* v_skipInstances_2402_, lean_object* v___x_2403_, lean_object* v___y_2404_, lean_object* v_b_2405_, lean_object* v_a_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
uint8_t v_usedLetOnly_boxed_2414_; uint8_t v_skipConstInApp_boxed_2415_; uint8_t v_skipInstances_boxed_2416_; lean_object* v_res_2417_; 
v_usedLetOnly_boxed_2414_ = lean_unbox(v_usedLetOnly_2400_);
v_skipConstInApp_boxed_2415_ = lean_unbox(v_skipConstInApp_2401_);
v_skipInstances_boxed_2416_ = lean_unbox(v_skipInstances_2402_);
v_res_2417_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__0(v_pre_2398_, v_post_2399_, v_usedLetOnly_boxed_2414_, v_skipConstInApp_boxed_2415_, v_skipInstances_boxed_2416_, v___x_2403_, v___y_2404_, v_b_2405_, v_a_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec(v_a_2406_);
lean_dec(v___y_2404_);
return v_res_2417_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg(lean_object* v_upperBound_2418_, lean_object* v___x_2419_, lean_object* v_pre_2420_, lean_object* v_post_2421_, uint8_t v_usedLetOnly_2422_, uint8_t v_skipConstInApp_2423_, uint8_t v_skipInstances_2424_, lean_object* v_a_2425_, lean_object* v_b_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
lean_object* v___y_2436_; uint8_t v___x_2459_; 
v___x_2459_ = lean_nat_dec_lt(v_a_2425_, v_upperBound_2418_);
if (v___x_2459_ == 0)
{
lean_object* v___x_2460_; 
lean_dec(v_a_2425_);
lean_dec_ref(v_post_2421_);
lean_dec_ref(v_pre_2420_);
v___x_2460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2460_, 0, v_b_2426_);
return v___x_2460_;
}
else
{
lean_object* v___x_2461_; lean_object* v___x_2462_; uint8_t v___x_2463_; 
v___x_2461_ = lean_array_fget_borrowed(v_b_2426_, v_a_2425_);
v___x_2462_ = lean_array_get_size(v___x_2419_);
v___x_2463_ = lean_nat_dec_lt(v_a_2425_, v___x_2462_);
if (v___x_2463_ == 0)
{
lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___f_2467_; 
lean_inc(v___x_2461_);
v___x_2464_ = lean_box(v_usedLetOnly_2422_);
v___x_2465_ = lean_box(v_skipConstInApp_2423_);
v___x_2466_ = lean_box(v_skipInstances_2424_);
lean_inc(v_a_2425_);
lean_inc(v___y_2427_);
lean_inc_ref(v_post_2421_);
lean_inc_ref(v_pre_2420_);
v___f_2467_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 16, 9);
lean_closure_set(v___f_2467_, 0, v_pre_2420_);
lean_closure_set(v___f_2467_, 1, v_post_2421_);
lean_closure_set(v___f_2467_, 2, v___x_2464_);
lean_closure_set(v___f_2467_, 3, v___x_2465_);
lean_closure_set(v___f_2467_, 4, v___x_2466_);
lean_closure_set(v___f_2467_, 5, v___x_2461_);
lean_closure_set(v___f_2467_, 6, v___y_2427_);
lean_closure_set(v___f_2467_, 7, v_b_2426_);
lean_closure_set(v___f_2467_, 8, v_a_2425_);
v___y_2436_ = v___f_2467_;
goto v___jp_2435_;
}
else
{
lean_object* v___x_2468_; uint8_t v_isInstance_2469_; 
v___x_2468_ = lean_array_fget_borrowed(v___x_2419_, v_a_2425_);
v_isInstance_2469_ = lean_ctor_get_uint8(v___x_2468_, sizeof(void*)*1 + 4);
if (v_isInstance_2469_ == 0)
{
lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___f_2473_; 
lean_inc(v___x_2461_);
v___x_2470_ = lean_box(v_usedLetOnly_2422_);
v___x_2471_ = lean_box(v_skipConstInApp_2423_);
v___x_2472_ = lean_box(v_skipInstances_2424_);
lean_inc(v_a_2425_);
lean_inc(v___y_2427_);
lean_inc_ref(v_post_2421_);
lean_inc_ref(v_pre_2420_);
v___f_2473_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 16, 9);
lean_closure_set(v___f_2473_, 0, v_pre_2420_);
lean_closure_set(v___f_2473_, 1, v_post_2421_);
lean_closure_set(v___f_2473_, 2, v___x_2470_);
lean_closure_set(v___f_2473_, 3, v___x_2471_);
lean_closure_set(v___f_2473_, 4, v___x_2472_);
lean_closure_set(v___f_2473_, 5, v___x_2461_);
lean_closure_set(v___f_2473_, 6, v___y_2427_);
lean_closure_set(v___f_2473_, 7, v_b_2426_);
lean_closure_set(v___f_2473_, 8, v_a_2425_);
v___y_2436_ = v___f_2473_;
goto v___jp_2435_;
}
else
{
lean_object* v___x_2474_; lean_object* v___f_2475_; 
v___x_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2474_, 0, v_b_2426_);
v___f_2475_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__2___boxed), 8, 1);
lean_closure_set(v___f_2475_, 0, v___x_2474_);
v___y_2436_ = v___f_2475_;
goto v___jp_2435_;
}
}
}
v___jp_2435_:
{
lean_object* v___x_2437_; 
lean_inc(v___y_2433_);
lean_inc_ref(v___y_2432_);
lean_inc(v___y_2431_);
lean_inc_ref(v___y_2430_);
lean_inc(v___y_2429_);
lean_inc_ref(v___y_2428_);
v___x_2437_ = lean_apply_7(v___y_2436_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, lean_box(0));
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_a_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2450_; 
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2440_ = v___x_2437_;
v_isShared_2441_ = v_isSharedCheck_2450_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_a_2438_);
lean_dec(v___x_2437_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2450_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
if (lean_obj_tag(v_a_2438_) == 0)
{
lean_object* v_a_2442_; lean_object* v___x_2444_; 
lean_dec(v_a_2425_);
lean_dec_ref(v_post_2421_);
lean_dec_ref(v_pre_2420_);
v_a_2442_ = lean_ctor_get(v_a_2438_, 0);
lean_inc(v_a_2442_);
lean_dec_ref_known(v_a_2438_, 1);
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 0, v_a_2442_);
v___x_2444_ = v___x_2440_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_a_2442_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
else
{
lean_object* v_a_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
lean_del_object(v___x_2440_);
v_a_2446_ = lean_ctor_get(v_a_2438_, 0);
lean_inc(v_a_2446_);
lean_dec_ref_known(v_a_2438_, 1);
v___x_2447_ = lean_unsigned_to_nat(1u);
v___x_2448_ = lean_nat_add(v_a_2425_, v___x_2447_);
lean_dec(v_a_2425_);
v_a_2425_ = v___x_2448_;
v_b_2426_ = v_a_2446_;
goto _start;
}
}
}
else
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2458_; 
lean_dec(v_a_2425_);
lean_dec_ref(v_post_2421_);
lean_dec_ref(v_pre_2420_);
v_a_2451_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2453_ = v___x_2437_;
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2437_);
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
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__9(uint8_t v_skipInstances_2476_, lean_object* v_pre_2477_, lean_object* v_post_2478_, uint8_t v_usedLetOnly_2479_, uint8_t v_skipConstInApp_2480_, lean_object* v_x_2481_, lean_object* v_x_2482_, lean_object* v_x_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
lean_object* v_f_2493_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; 
if (lean_obj_tag(v_x_2481_) == 5)
{
lean_object* v_fn_2543_; lean_object* v_arg_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v_fn_2543_ = lean_ctor_get(v_x_2481_, 0);
lean_inc_ref(v_fn_2543_);
v_arg_2544_ = lean_ctor_get(v_x_2481_, 1);
lean_inc_ref(v_arg_2544_);
lean_dec_ref_known(v_x_2481_, 2);
v___x_2545_ = lean_array_set(v_x_2482_, v_x_2483_, v_arg_2544_);
v___x_2546_ = lean_unsigned_to_nat(1u);
v___x_2547_ = lean_nat_sub(v_x_2483_, v___x_2546_);
lean_dec(v_x_2483_);
v_x_2481_ = v_fn_2543_;
v_x_2482_ = v___x_2545_;
v_x_2483_ = v___x_2547_;
goto _start;
}
else
{
lean_dec(v_x_2483_);
if (v_skipConstInApp_2480_ == 0)
{
goto v___jp_2540_;
}
else
{
uint8_t v___x_2549_; 
v___x_2549_ = l_Lean_Expr_isConst(v_x_2481_);
if (v___x_2549_ == 0)
{
goto v___jp_2540_;
}
else
{
v_f_2493_ = v_x_2481_;
v___y_2494_ = v___y_2484_;
v___y_2495_ = v___y_2485_;
v___y_2496_ = v___y_2486_;
v___y_2497_ = v___y_2487_;
v___y_2498_ = v___y_2488_;
v___y_2499_ = v___y_2489_;
v___y_2500_ = v___y_2490_;
goto v___jp_2492_;
}
}
}
v___jp_2492_:
{
if (v_skipInstances_2476_ == 0)
{
size_t v_sz_2501_; size_t v___x_2502_; lean_object* v___x_2503_; 
v_sz_2501_ = lean_array_size(v_x_2482_);
v___x_2502_ = ((size_t)0ULL);
lean_inc_ref(v_post_2478_);
lean_inc_ref(v_pre_2477_);
v___x_2503_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__2(v_pre_2477_, v_post_2478_, v_usedLetOnly_2479_, v_skipConstInApp_2480_, v_skipInstances_2476_, v_sz_2501_, v___x_2502_, v_x_2482_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2503_) == 0)
{
lean_object* v_a_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
v_a_2504_ = lean_ctor_get(v___x_2503_, 0);
lean_inc(v_a_2504_);
lean_dec_ref_known(v___x_2503_, 1);
v___x_2505_ = l_Lean_mkAppN(v_f_2493_, v_a_2504_);
lean_dec(v_a_2504_);
v___x_2506_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2477_, v_post_2478_, v_usedLetOnly_2479_, v_skipConstInApp_2480_, v_skipInstances_2476_, v___x_2505_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
return v___x_2506_;
}
else
{
lean_object* v_a_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2514_; 
lean_dec_ref(v_f_2493_);
lean_dec_ref(v_post_2478_);
lean_dec_ref(v_pre_2477_);
v_a_2507_ = lean_ctor_get(v___x_2503_, 0);
v_isSharedCheck_2514_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2509_ = v___x_2503_;
v_isShared_2510_ = v_isSharedCheck_2514_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_a_2507_);
lean_dec(v___x_2503_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2514_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v___x_2512_; 
if (v_isShared_2510_ == 0)
{
v___x_2512_ = v___x_2509_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v_a_2507_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
}
}
}
}
else
{
lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2515_ = lean_array_get_size(v_x_2482_);
lean_inc_ref(v_f_2493_);
v___x_2516_ = l_Lean_Meta_getFunInfoNArgs(v_f_2493_, v___x_2515_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_object* v_a_2517_; lean_object* v_paramInfo_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
v_a_2517_ = lean_ctor_get(v___x_2516_, 0);
lean_inc(v_a_2517_);
lean_dec_ref_known(v___x_2516_, 1);
v_paramInfo_2518_ = lean_ctor_get(v_a_2517_, 0);
lean_inc_ref(v_paramInfo_2518_);
lean_dec(v_a_2517_);
v___x_2519_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_2478_);
lean_inc_ref(v_pre_2477_);
v___x_2520_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg(v___x_2515_, v_paramInfo_2518_, v_pre_2477_, v_post_2478_, v_usedLetOnly_2479_, v_skipConstInApp_2480_, v_skipInstances_2476_, v___x_2519_, v_x_2482_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
lean_dec_ref(v_paramInfo_2518_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v_a_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
v_a_2521_ = lean_ctor_get(v___x_2520_, 0);
lean_inc(v_a_2521_);
lean_dec_ref_known(v___x_2520_, 1);
v___x_2522_ = l_Lean_mkAppN(v_f_2493_, v_a_2521_);
lean_dec(v_a_2521_);
v___x_2523_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2477_, v_post_2478_, v_usedLetOnly_2479_, v_skipConstInApp_2480_, v_skipInstances_2476_, v___x_2522_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
return v___x_2523_;
}
else
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
lean_dec_ref(v_f_2493_);
lean_dec_ref(v_post_2478_);
lean_dec_ref(v_pre_2477_);
v_a_2524_ = lean_ctor_get(v___x_2520_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2526_ = v___x_2520_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2520_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2524_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
else
{
lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2539_; 
lean_dec_ref(v_f_2493_);
lean_dec_ref(v_x_2482_);
lean_dec_ref(v_post_2478_);
lean_dec_ref(v_pre_2477_);
v_a_2532_ = lean_ctor_get(v___x_2516_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2516_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2534_ = v___x_2516_;
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2516_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2537_; 
if (v_isShared_2535_ == 0)
{
v___x_2537_ = v___x_2534_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_a_2532_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
}
}
v___jp_2540_:
{
lean_object* v___x_2541_; 
lean_inc_ref(v_post_2478_);
lean_inc_ref(v_pre_2477_);
v___x_2541_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2477_, v_post_2478_, v_usedLetOnly_2479_, v_skipConstInApp_2480_, v_skipInstances_2476_, v_x_2481_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v_a_2542_; 
v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
lean_inc(v_a_2542_);
lean_dec_ref_known(v___x_2541_, 1);
v_f_2493_ = v_a_2542_;
v___y_2494_ = v___y_2484_;
v___y_2495_ = v___y_2485_;
v___y_2496_ = v___y_2486_;
v___y_2497_ = v___y_2487_;
v___y_2498_ = v___y_2488_;
v___y_2499_ = v___y_2489_;
v___y_2500_ = v___y_2490_;
goto v___jp_2492_;
}
else
{
lean_dec_ref(v_x_2482_);
lean_dec_ref(v_post_2478_);
lean_dec_ref(v_pre_2477_);
return v___x_2541_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1(lean_object* v___x_2550_, lean_object* v_pre_2551_, lean_object* v_e_2552_, lean_object* v_post_2553_, uint8_t v_usedLetOnly_2554_, uint8_t v_skipConstInApp_2555_, uint8_t v_skipInstances_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_){
_start:
{
lean_object* v___x_2565_; 
v___x_2565_ = l_Lean_Core_checkSystem(v___x_2550_, v___y_2562_, v___y_2563_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v___x_2566_; 
lean_dec_ref_known(v___x_2565_, 1);
lean_inc_ref(v_pre_2551_);
lean_inc(v___y_2563_);
lean_inc_ref(v___y_2562_);
lean_inc(v___y_2561_);
lean_inc_ref(v___y_2560_);
lean_inc(v___y_2559_);
lean_inc_ref(v___y_2558_);
lean_inc_ref(v_e_2552_);
v___x_2566_ = lean_apply_8(v_pre_2551_, v_e_2552_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_, lean_box(0));
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2615_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2569_ = v___x_2566_;
v_isShared_2570_ = v_isSharedCheck_2615_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2566_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2615_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___y_2572_; 
switch(lean_obj_tag(v_a_2567_))
{
case 0:
{
lean_object* v_e_2607_; lean_object* v___x_2609_; 
lean_dec_ref(v_post_2553_);
lean_dec_ref(v_e_2552_);
lean_dec_ref(v_pre_2551_);
v_e_2607_ = lean_ctor_get(v_a_2567_, 0);
lean_inc_ref(v_e_2607_);
lean_dec_ref_known(v_a_2567_, 1);
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 0, v_e_2607_);
v___x_2609_ = v___x_2569_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_e_2607_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
case 1:
{
lean_object* v_e_2611_; lean_object* v___x_2612_; 
lean_del_object(v___x_2569_);
lean_dec_ref(v_e_2552_);
v_e_2611_ = lean_ctor_get(v_a_2567_, 0);
lean_inc_ref(v_e_2611_);
lean_dec_ref_known(v_a_2567_, 1);
v___x_2612_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2551_, v_post_2553_, v_usedLetOnly_2554_, v_skipConstInApp_2555_, v_skipInstances_2556_, v_e_2611_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_);
return v___x_2612_;
}
default: 
{
lean_object* v_e_x3f_2613_; 
lean_del_object(v___x_2569_);
v_e_x3f_2613_ = lean_ctor_get(v_a_2567_, 0);
lean_inc(v_e_x3f_2613_);
lean_dec_ref_known(v_a_2567_, 1);
if (lean_obj_tag(v_e_x3f_2613_) == 0)
{
v___y_2572_ = v_e_2552_;
goto v___jp_2571_;
}
else
{
lean_object* v_val_2614_; 
lean_dec_ref(v_e_2552_);
v_val_2614_ = lean_ctor_get(v_e_x3f_2613_, 0);
lean_inc(v_val_2614_);
lean_dec_ref_known(v_e_x3f_2613_, 1);
v___y_2572_ = v_val_2614_;
goto v___jp_2571_;
}
}
}
v___jp_2571_:
{
switch(lean_obj_tag(v___y_2572_))
{
case 7:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2573_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___closed__0));
v___x_2574_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6(v_pre_2551_, v_post_2553_, v_usedLetOnly_2554_, v_skipConstInApp_2555_, v_skipInstances_2556_, v___x_2573_, v___y_2572_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_);
return v___x_2574_;
}
case 6:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2575_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___closed__0));
v___x_2576_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7(v_pre_2551_, v_post_2553_, v_usedLetOnly_2554_, v_skipConstInApp_2555_, v_skipInstances_2556_, v___x_2575_, v___y_2572_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_);
return v___x_2576_;
}
case 8:
{
lean_object* v___x_2577_; lean_object* v___x_2578_; 
v___x_2577_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___closed__0));
v___x_2578_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8(v_pre_2551_, v_post_2553_, v_usedLetOnly_2554_, v_skipConstInApp_2555_, v_skipInstances_2556_, v___x_2577_, v___y_2572_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_);
return v___x_2578_;
}
case 5:
{
lean_object* v_dummy_2579_; lean_object* v_nargs_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
v_dummy_2579_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___closed__1);
v_nargs_2580_ = l_Lean_Expr_getAppNumArgs(v___y_2572_);
lean_inc(v_nargs_2580_);
v___x_2581_ = lean_mk_array(v_nargs_2580_, v_dummy_2579_);
v___x_2582_ = lean_unsigned_to_nat(1u);
v___x_2583_ = lean_nat_sub(v_nargs_2580_, v___x_2582_);
lean_dec(v_nargs_2580_);
v___x_2584_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__9(v_skipInstances_2556_, v_pre_2551_, v_post_2553_, v_usedLetOnly_2554_, v_skipConstInApp_2555_, v___y_2572_, v___x_2581_, v___x_2583_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_);
return v___x_2584_;
}
case 10:
{
lean_object* v_data_2585_; lean_object* v_expr_2586_; lean_object* v___x_2587_; 
v_data_2585_ = lean_ctor_get(v___y_2572_, 0);
v_expr_2586_ = lean_ctor_get(v___y_2572_, 1);
lean_inc_ref(v_expr_2586_);
lean_inc_ref(v_post_2553_);
lean_inc_ref(v_pre_2551_);
v___x_2587_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2551_, v_post_2553_, v_usedLetOnly_2554_, v_skipConstInApp_2555_, v_skipInstances_2556_, v_expr_2586_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v_a_2588_; size_t v___x_2589_; size_t v___x_2590_; uint8_t v___x_2591_; 
v_a_2588_ = lean_ctor_get(v___x_2587_, 0);
lean_inc(v_a_2588_);
lean_dec_ref_known(v___x_2587_, 1);
v___x_2589_ = lean_ptr_addr(v_expr_2586_);
v___x_2590_ = lean_ptr_addr(v_a_2588_);
v___x_2591_ = lean_usize_dec_eq(v___x_2589_, v___x_2590_);
if (v___x_2591_ == 0)
{
lean_object* v___x_2592_; lean_object* v___x_2593_; 
lean_inc(v_data_2585_);
lean_dec_ref_known(v___y_2572_, 2);
v___x_2592_ = l_Lean_Expr_mdata___override(v_data_2585_, v_a_2588_);
v___x_2593_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2551_, v_post_2553_, v_usedLetOnly_2554_, v_skipConstInApp_2555_, v_skipInstances_2556_, v___x_2592_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_);
return v___x_2593_;
}
else
{
lean_object* v___x_2594_; 
lean_dec(v_a_2588_);
v___x_2594_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2551_, v_post_2553_, v_usedLetOnly_2554_, v_skipConstInApp_2555_, v_skipInstances_2556_, v___y_2572_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_);
return v___x_2594_;
}
}
else
{
lean_dec_ref_known(v___y_2572_, 2);
lean_dec_ref(v_post_2553_);
lean_dec_ref(v_pre_2551_);
return v___x_2587_;
}
}
case 11:
{
lean_object* v_typeName_2595_; lean_object* v_idx_2596_; lean_object* v_struct_2597_; lean_object* v___x_2598_; 
v_typeName_2595_ = lean_ctor_get(v___y_2572_, 0);
v_idx_2596_ = lean_ctor_get(v___y_2572_, 1);
v_struct_2597_ = lean_ctor_get(v___y_2572_, 2);
lean_inc_ref(v_struct_2597_);
lean_inc_ref(v_post_2553_);
lean_inc_ref(v_pre_2551_);
v___x_2598_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2551_, v_post_2553_, v_usedLetOnly_2554_, v_skipConstInApp_2555_, v_skipInstances_2556_, v_struct_2597_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v_a_2599_; size_t v___x_2600_; size_t v___x_2601_; uint8_t v___x_2602_; 
v_a_2599_ = lean_ctor_get(v___x_2598_, 0);
lean_inc(v_a_2599_);
lean_dec_ref_known(v___x_2598_, 1);
v___x_2600_ = lean_ptr_addr(v_struct_2597_);
v___x_2601_ = lean_ptr_addr(v_a_2599_);
v___x_2602_ = lean_usize_dec_eq(v___x_2600_, v___x_2601_);
if (v___x_2602_ == 0)
{
lean_object* v___x_2603_; lean_object* v___x_2604_; 
lean_inc(v_idx_2596_);
lean_inc(v_typeName_2595_);
lean_dec_ref_known(v___y_2572_, 3);
v___x_2603_ = l_Lean_Expr_proj___override(v_typeName_2595_, v_idx_2596_, v_a_2599_);
v___x_2604_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2551_, v_post_2553_, v_usedLetOnly_2554_, v_skipConstInApp_2555_, v_skipInstances_2556_, v___x_2603_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_);
return v___x_2604_;
}
else
{
lean_object* v___x_2605_; 
lean_dec(v_a_2599_);
v___x_2605_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2551_, v_post_2553_, v_usedLetOnly_2554_, v_skipConstInApp_2555_, v_skipInstances_2556_, v___y_2572_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_);
return v___x_2605_;
}
}
else
{
lean_dec_ref_known(v___y_2572_, 3);
lean_dec_ref(v_post_2553_);
lean_dec_ref(v_pre_2551_);
return v___x_2598_;
}
}
default: 
{
lean_object* v___x_2606_; 
v___x_2606_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2551_, v_post_2553_, v_usedLetOnly_2554_, v_skipConstInApp_2555_, v_skipInstances_2556_, v___y_2572_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_);
return v___x_2606_;
}
}
}
}
}
else
{
lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2623_; 
lean_dec_ref(v_post_2553_);
lean_dec_ref(v_e_2552_);
lean_dec_ref(v_pre_2551_);
v_a_2616_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2618_ = v___x_2566_;
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2566_);
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
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2631_; 
lean_dec_ref(v_post_2553_);
lean_dec_ref(v_e_2552_);
lean_dec_ref(v_pre_2551_);
v_a_2624_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2626_ = v___x_2565_;
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v___x_2565_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2629_; 
if (v_isShared_2627_ == 0)
{
v___x_2629_ = v___x_2626_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_a_2624_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___boxed(lean_object* v___x_2632_, lean_object* v_pre_2633_, lean_object* v_e_2634_, lean_object* v_post_2635_, lean_object* v_usedLetOnly_2636_, lean_object* v_skipConstInApp_2637_, lean_object* v_skipInstances_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
uint8_t v_usedLetOnly_boxed_2647_; uint8_t v_skipConstInApp_boxed_2648_; uint8_t v_skipInstances_boxed_2649_; lean_object* v_res_2650_; 
v_usedLetOnly_boxed_2647_ = lean_unbox(v_usedLetOnly_2636_);
v_skipConstInApp_boxed_2648_ = lean_unbox(v_skipConstInApp_2637_);
v_skipInstances_boxed_2649_ = lean_unbox(v_skipInstances_2638_);
v_res_2650_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1(v___x_2632_, v_pre_2633_, v_e_2634_, v_post_2635_, v_usedLetOnly_boxed_2647_, v_skipConstInApp_boxed_2648_, v_skipInstances_boxed_2649_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
lean_dec(v___y_2639_);
return v_res_2650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(lean_object* v_pre_2651_, lean_object* v_post_2652_, uint8_t v_usedLetOnly_2653_, uint8_t v_skipConstInApp_2654_, uint8_t v_skipInstances_2655_, lean_object* v_e_2656_, lean_object* v_a_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_){
_start:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; 
lean_inc(v_a_2657_);
v___x_2665_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2665_, 0, lean_box(0));
lean_closure_set(v___x_2665_, 1, lean_box(0));
lean_closure_set(v___x_2665_, 2, v_a_2657_);
v___x_2666_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__0(lean_box(0), v___x_2665_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2701_; 
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2669_ = v___x_2666_;
v_isShared_2670_ = v_isSharedCheck_2701_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2666_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2701_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2671_; 
v___x_2671_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5___redArg(v_a_2667_, v_e_2656_);
lean_dec(v_a_2667_);
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___f_2676_; lean_object* v___x_2677_; 
lean_del_object(v___x_2669_);
v___x_2672_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___closed__0));
v___x_2673_ = lean_box(v_usedLetOnly_2653_);
v___x_2674_ = lean_box(v_skipConstInApp_2654_);
v___x_2675_ = lean_box(v_skipInstances_2655_);
lean_inc_ref(v_e_2656_);
v___f_2676_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___boxed), 15, 7);
lean_closure_set(v___f_2676_, 0, v___x_2672_);
lean_closure_set(v___f_2676_, 1, v_pre_2651_);
lean_closure_set(v___f_2676_, 2, v_e_2656_);
lean_closure_set(v___f_2676_, 3, v_post_2652_);
lean_closure_set(v___f_2676_, 4, v___x_2673_);
lean_closure_set(v___f_2676_, 5, v___x_2674_);
lean_closure_set(v___f_2676_, 6, v___x_2675_);
v___x_2677_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10___redArg(v___f_2676_, v_a_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_object* v_a_2678_; lean_object* v___f_2679_; lean_object* v___x_2680_; 
v_a_2678_ = lean_ctor_get(v___x_2677_, 0);
lean_inc_n(v_a_2678_, 2);
lean_dec_ref_known(v___x_2677_, 1);
lean_inc(v_a_2657_);
v___f_2679_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2679_, 0, v_a_2657_);
lean_closure_set(v___f_2679_, 1, v_e_2656_);
lean_closure_set(v___f_2679_, 2, v_a_2678_);
v___x_2680_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__0(lean_box(0), v___f_2679_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2687_; 
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2687_ == 0)
{
lean_object* v_unused_2688_; 
v_unused_2688_ = lean_ctor_get(v___x_2680_, 0);
lean_dec(v_unused_2688_);
v___x_2682_ = v___x_2680_;
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
else
{
lean_dec(v___x_2680_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___x_2685_; 
if (v_isShared_2683_ == 0)
{
lean_ctor_set(v___x_2682_, 0, v_a_2678_);
v___x_2685_ = v___x_2682_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_a_2678_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
else
{
lean_object* v_a_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2696_; 
lean_dec(v_a_2678_);
v_a_2689_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2691_ = v___x_2680_;
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_a_2689_);
lean_dec(v___x_2680_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2694_; 
if (v_isShared_2692_ == 0)
{
v___x_2694_ = v___x_2691_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_a_2689_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
}
else
{
lean_dec_ref(v_e_2656_);
return v___x_2677_;
}
}
else
{
lean_object* v_val_2697_; lean_object* v___x_2699_; 
lean_dec_ref(v_e_2656_);
lean_dec_ref(v_post_2652_);
lean_dec_ref(v_pre_2651_);
v_val_2697_ = lean_ctor_get(v___x_2671_, 0);
lean_inc(v_val_2697_);
lean_dec_ref_known(v___x_2671_, 1);
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 0, v_val_2697_);
v___x_2699_ = v___x_2669_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_val_2697_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
}
else
{
lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2709_; 
lean_dec_ref(v_e_2656_);
lean_dec_ref(v_post_2652_);
lean_dec_ref(v_pre_2651_);
v_a_2702_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2704_ = v___x_2666_;
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_dec(v___x_2666_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2707_; 
if (v_isShared_2705_ == 0)
{
v___x_2707_ = v___x_2704_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_a_2702_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
return v___x_2707_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6(lean_object* v_pre_2710_, lean_object* v_post_2711_, uint8_t v_usedLetOnly_2712_, uint8_t v_skipConstInApp_2713_, uint8_t v_skipInstances_2714_, lean_object* v_fvars_2715_, lean_object* v_e_2716_, lean_object* v_a_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
if (lean_obj_tag(v_e_2716_) == 7)
{
lean_object* v_binderName_2725_; lean_object* v_binderType_2726_; lean_object* v_body_2727_; uint8_t v_binderInfo_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___f_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
v_binderName_2725_ = lean_ctor_get(v_e_2716_, 0);
lean_inc(v_binderName_2725_);
v_binderType_2726_ = lean_ctor_get(v_e_2716_, 1);
lean_inc_ref(v_binderType_2726_);
v_body_2727_ = lean_ctor_get(v_e_2716_, 2);
lean_inc_ref(v_body_2727_);
v_binderInfo_2728_ = lean_ctor_get_uint8(v_e_2716_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2716_, 3);
v___x_2729_ = lean_box(v_usedLetOnly_2712_);
v___x_2730_ = lean_box(v_skipConstInApp_2713_);
v___x_2731_ = lean_box(v_skipInstances_2714_);
lean_inc_ref(v_post_2711_);
lean_inc_ref(v_pre_2710_);
lean_inc_ref(v_fvars_2715_);
v___f_2732_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6___lam__0___boxed), 16, 7);
lean_closure_set(v___f_2732_, 0, v_fvars_2715_);
lean_closure_set(v___f_2732_, 1, v_pre_2710_);
lean_closure_set(v___f_2732_, 2, v_post_2711_);
lean_closure_set(v___f_2732_, 3, v___x_2729_);
lean_closure_set(v___f_2732_, 4, v___x_2730_);
lean_closure_set(v___f_2732_, 5, v___x_2731_);
lean_closure_set(v___f_2732_, 6, v_body_2727_);
v___x_2733_ = lean_expr_instantiate_rev(v_binderType_2726_, v_fvars_2715_);
lean_dec_ref(v_fvars_2715_);
lean_dec_ref(v_binderType_2726_);
v___x_2734_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2710_, v_post_2711_, v_usedLetOnly_2712_, v_skipConstInApp_2713_, v_skipInstances_2714_, v___x_2733_, v_a_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v_a_2735_; uint8_t v___x_2736_; lean_object* v___x_2737_; 
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
lean_inc(v_a_2735_);
lean_dec_ref_known(v___x_2734_, 1);
v___x_2736_ = 0;
v___x_2737_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_2725_, v_binderInfo_2728_, v_a_2735_, v___f_2732_, v___x_2736_, v_a_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
return v___x_2737_;
}
else
{
lean_dec_ref(v___f_2732_);
lean_dec(v_binderName_2725_);
return v___x_2734_;
}
}
else
{
lean_object* v___x_2738_; lean_object* v___x_2739_; 
v___x_2738_ = lean_expr_instantiate_rev(v_e_2716_, v_fvars_2715_);
lean_dec_ref(v_e_2716_);
lean_inc_ref(v_post_2711_);
lean_inc_ref(v_pre_2710_);
v___x_2739_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2710_, v_post_2711_, v_usedLetOnly_2712_, v_skipConstInApp_2713_, v_skipInstances_2714_, v___x_2738_, v_a_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_object* v_a_2740_; uint8_t v___x_2741_; uint8_t v___x_2742_; uint8_t v___x_2743_; lean_object* v___x_2744_; 
v_a_2740_ = lean_ctor_get(v___x_2739_, 0);
lean_inc(v_a_2740_);
lean_dec_ref_known(v___x_2739_, 1);
v___x_2741_ = 0;
v___x_2742_ = 1;
v___x_2743_ = 1;
v___x_2744_ = l_Lean_Meta_mkForallFVars(v_fvars_2715_, v_a_2740_, v___x_2741_, v_usedLetOnly_2712_, v___x_2742_, v___x_2743_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
lean_dec_ref(v_fvars_2715_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v_a_2745_; lean_object* v___x_2746_; 
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
lean_inc(v_a_2745_);
lean_dec_ref_known(v___x_2744_, 1);
v___x_2746_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2710_, v_post_2711_, v_usedLetOnly_2712_, v_skipConstInApp_2713_, v_skipInstances_2714_, v_a_2745_, v_a_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
return v___x_2746_;
}
else
{
lean_dec_ref(v_post_2711_);
lean_dec_ref(v_pre_2710_);
return v___x_2744_;
}
}
else
{
lean_dec_ref(v_fvars_2715_);
lean_dec_ref(v_post_2711_);
lean_dec_ref(v_pre_2710_);
return v___x_2739_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6___lam__0(lean_object* v_fvars_2747_, lean_object* v_pre_2748_, lean_object* v_post_2749_, uint8_t v_usedLetOnly_2750_, uint8_t v_skipConstInApp_2751_, uint8_t v_skipInstances_2752_, lean_object* v_body_2753_, lean_object* v_x_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2763_ = lean_array_push(v_fvars_2747_, v_x_2754_);
v___x_2764_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6(v_pre_2748_, v_post_2749_, v_usedLetOnly_2750_, v_skipConstInApp_2751_, v_skipInstances_2752_, v___x_2763_, v_body_2753_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
return v___x_2764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_2765_, lean_object* v_post_2766_, lean_object* v_usedLetOnly_2767_, lean_object* v_skipConstInApp_2768_, lean_object* v_skipInstances_2769_, lean_object* v_e_2770_, lean_object* v_a_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_){
_start:
{
uint8_t v_usedLetOnly_boxed_2779_; uint8_t v_skipConstInApp_boxed_2780_; uint8_t v_skipInstances_boxed_2781_; lean_object* v_res_2782_; 
v_usedLetOnly_boxed_2779_ = lean_unbox(v_usedLetOnly_2767_);
v_skipConstInApp_boxed_2780_ = lean_unbox(v_skipConstInApp_2768_);
v_skipInstances_boxed_2781_ = lean_unbox(v_skipInstances_2769_);
v_res_2782_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2765_, v_post_2766_, v_usedLetOnly_boxed_2779_, v_skipConstInApp_boxed_2780_, v_skipInstances_boxed_2781_, v_e_2770_, v_a_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_);
lean_dec(v___y_2777_);
lean_dec_ref(v___y_2776_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2774_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec(v_a_2771_);
return v_res_2782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_2783_, lean_object* v_post_2784_, lean_object* v_usedLetOnly_2785_, lean_object* v_skipConstInApp_2786_, lean_object* v_skipInstances_2787_, lean_object* v_sz_2788_, lean_object* v_i_2789_, lean_object* v_bs_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
uint8_t v_usedLetOnly_boxed_2799_; uint8_t v_skipConstInApp_boxed_2800_; uint8_t v_skipInstances_boxed_2801_; size_t v_sz_boxed_2802_; size_t v_i_boxed_2803_; lean_object* v_res_2804_; 
v_usedLetOnly_boxed_2799_ = lean_unbox(v_usedLetOnly_2785_);
v_skipConstInApp_boxed_2800_ = lean_unbox(v_skipConstInApp_2786_);
v_skipInstances_boxed_2801_ = lean_unbox(v_skipInstances_2787_);
v_sz_boxed_2802_ = lean_unbox_usize(v_sz_2788_);
lean_dec(v_sz_2788_);
v_i_boxed_2803_ = lean_unbox_usize(v_i_2789_);
lean_dec(v_i_2789_);
v_res_2804_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__2(v_pre_2783_, v_post_2784_, v_usedLetOnly_boxed_2799_, v_skipConstInApp_boxed_2800_, v_skipInstances_boxed_2801_, v_sz_boxed_2802_, v_i_boxed_2803_, v_bs_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec(v___y_2793_);
lean_dec_ref(v___y_2792_);
lean_dec(v___y_2791_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___boxed(lean_object* v_pre_2805_, lean_object* v_post_2806_, lean_object* v_usedLetOnly_2807_, lean_object* v_skipConstInApp_2808_, lean_object* v_skipInstances_2809_, lean_object* v_e_2810_, lean_object* v_a_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_){
_start:
{
uint8_t v_usedLetOnly_boxed_2819_; uint8_t v_skipConstInApp_boxed_2820_; uint8_t v_skipInstances_boxed_2821_; lean_object* v_res_2822_; 
v_usedLetOnly_boxed_2819_ = lean_unbox(v_usedLetOnly_2807_);
v_skipConstInApp_boxed_2820_ = lean_unbox(v_skipConstInApp_2808_);
v_skipInstances_boxed_2821_ = lean_unbox(v_skipInstances_2809_);
v_res_2822_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2805_, v_post_2806_, v_usedLetOnly_boxed_2819_, v_skipConstInApp_boxed_2820_, v_skipInstances_boxed_2821_, v_e_2810_, v_a_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_);
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
lean_dec(v_a_2811_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6___boxed(lean_object* v_pre_2823_, lean_object* v_post_2824_, lean_object* v_usedLetOnly_2825_, lean_object* v_skipConstInApp_2826_, lean_object* v_skipInstances_2827_, lean_object* v_fvars_2828_, lean_object* v_e_2829_, lean_object* v_a_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
uint8_t v_usedLetOnly_boxed_2838_; uint8_t v_skipConstInApp_boxed_2839_; uint8_t v_skipInstances_boxed_2840_; lean_object* v_res_2841_; 
v_usedLetOnly_boxed_2838_ = lean_unbox(v_usedLetOnly_2825_);
v_skipConstInApp_boxed_2839_ = lean_unbox(v_skipConstInApp_2826_);
v_skipInstances_boxed_2840_ = lean_unbox(v_skipInstances_2827_);
v_res_2841_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6(v_pre_2823_, v_post_2824_, v_usedLetOnly_boxed_2838_, v_skipConstInApp_boxed_2839_, v_skipInstances_boxed_2840_, v_fvars_2828_, v_e_2829_, v_a_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec_ref(v___y_2833_);
lean_dec(v___y_2832_);
lean_dec_ref(v___y_2831_);
lean_dec(v_a_2830_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7___boxed(lean_object* v_pre_2842_, lean_object* v_post_2843_, lean_object* v_usedLetOnly_2844_, lean_object* v_skipConstInApp_2845_, lean_object* v_skipInstances_2846_, lean_object* v_fvars_2847_, lean_object* v_e_2848_, lean_object* v_a_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
uint8_t v_usedLetOnly_boxed_2857_; uint8_t v_skipConstInApp_boxed_2858_; uint8_t v_skipInstances_boxed_2859_; lean_object* v_res_2860_; 
v_usedLetOnly_boxed_2857_ = lean_unbox(v_usedLetOnly_2844_);
v_skipConstInApp_boxed_2858_ = lean_unbox(v_skipConstInApp_2845_);
v_skipInstances_boxed_2859_ = lean_unbox(v_skipInstances_2846_);
v_res_2860_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7(v_pre_2842_, v_post_2843_, v_usedLetOnly_boxed_2857_, v_skipConstInApp_boxed_2858_, v_skipInstances_boxed_2859_, v_fvars_2847_, v_e_2848_, v_a_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
lean_dec(v___y_2853_);
lean_dec_ref(v___y_2852_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v_a_2849_);
return v_res_2860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8___boxed(lean_object* v_pre_2861_, lean_object* v_post_2862_, lean_object* v_usedLetOnly_2863_, lean_object* v_skipConstInApp_2864_, lean_object* v_skipInstances_2865_, lean_object* v_fvars_2866_, lean_object* v_e_2867_, lean_object* v_a_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
uint8_t v_usedLetOnly_boxed_2876_; uint8_t v_skipConstInApp_boxed_2877_; uint8_t v_skipInstances_boxed_2878_; lean_object* v_res_2879_; 
v_usedLetOnly_boxed_2876_ = lean_unbox(v_usedLetOnly_2863_);
v_skipConstInApp_boxed_2877_ = lean_unbox(v_skipConstInApp_2864_);
v_skipInstances_boxed_2878_ = lean_unbox(v_skipInstances_2865_);
v_res_2879_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8(v_pre_2861_, v_post_2862_, v_usedLetOnly_boxed_2876_, v_skipConstInApp_boxed_2877_, v_skipInstances_boxed_2878_, v_fvars_2866_, v_e_2867_, v_a_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
lean_dec(v_a_2868_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_2880_ = _args[0];
lean_object* v___x_2881_ = _args[1];
lean_object* v_pre_2882_ = _args[2];
lean_object* v_post_2883_ = _args[3];
lean_object* v_usedLetOnly_2884_ = _args[4];
lean_object* v_skipConstInApp_2885_ = _args[5];
lean_object* v_skipInstances_2886_ = _args[6];
lean_object* v_a_2887_ = _args[7];
lean_object* v_b_2888_ = _args[8];
lean_object* v___y_2889_ = _args[9];
lean_object* v___y_2890_ = _args[10];
lean_object* v___y_2891_ = _args[11];
lean_object* v___y_2892_ = _args[12];
lean_object* v___y_2893_ = _args[13];
lean_object* v___y_2894_ = _args[14];
lean_object* v___y_2895_ = _args[15];
lean_object* v___y_2896_ = _args[16];
_start:
{
uint8_t v_usedLetOnly_boxed_2897_; uint8_t v_skipConstInApp_boxed_2898_; uint8_t v_skipInstances_boxed_2899_; lean_object* v_res_2900_; 
v_usedLetOnly_boxed_2897_ = lean_unbox(v_usedLetOnly_2884_);
v_skipConstInApp_boxed_2898_ = lean_unbox(v_skipConstInApp_2885_);
v_skipInstances_boxed_2899_ = lean_unbox(v_skipInstances_2886_);
v_res_2900_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg(v_upperBound_2880_, v___x_2881_, v_pre_2882_, v_post_2883_, v_usedLetOnly_boxed_2897_, v_skipConstInApp_boxed_2898_, v_skipInstances_boxed_2899_, v_a_2887_, v_b_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
lean_dec(v___y_2895_);
lean_dec_ref(v___y_2894_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___x_2881_);
lean_dec(v_upperBound_2880_);
return v_res_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__9___boxed(lean_object* v_skipInstances_2901_, lean_object* v_pre_2902_, lean_object* v_post_2903_, lean_object* v_usedLetOnly_2904_, lean_object* v_skipConstInApp_2905_, lean_object* v_x_2906_, lean_object* v_x_2907_, lean_object* v_x_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_){
_start:
{
uint8_t v_skipInstances_boxed_2917_; uint8_t v_usedLetOnly_boxed_2918_; uint8_t v_skipConstInApp_boxed_2919_; lean_object* v_res_2920_; 
v_skipInstances_boxed_2917_ = lean_unbox(v_skipInstances_2901_);
v_usedLetOnly_boxed_2918_ = lean_unbox(v_usedLetOnly_2904_);
v_skipConstInApp_boxed_2919_ = lean_unbox(v_skipConstInApp_2905_);
v_res_2920_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__9(v_skipInstances_boxed_2917_, v_pre_2902_, v_post_2903_, v_usedLetOnly_boxed_2918_, v_skipConstInApp_boxed_2919_, v_x_2906_, v_x_2907_, v_x_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
lean_dec(v___y_2909_);
return v_res_2920_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; 
v___x_2921_ = lean_box(0);
v___x_2922_ = lean_unsigned_to_nat(16u);
v___x_2923_ = lean_mk_array(v___x_2922_, v___x_2921_);
return v___x_2923_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2924_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__0);
v___x_2925_ = lean_unsigned_to_nat(0u);
v___x_2926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2925_);
lean_ctor_set(v___x_2926_, 1, v___x_2924_);
return v___x_2926_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__2(void){
_start:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; 
v___x_2927_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__1, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__1);
v___x_2928_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2928_, 0, lean_box(0));
lean_closure_set(v___x_2928_, 1, lean_box(0));
lean_closure_set(v___x_2928_, 2, v___x_2927_);
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1(lean_object* v_input_2929_, lean_object* v_pre_2930_, lean_object* v_post_2931_, uint8_t v_usedLetOnly_2932_, uint8_t v_skipConstInApp_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_){
_start:
{
uint8_t v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v_a_2944_; lean_object* v___x_2945_; 
v___x_2941_ = 0;
v___x_2942_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__2, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__2);
v___x_2943_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___lam__0(lean_box(0), v___x_2942_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_);
v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
lean_inc(v_a_2944_);
lean_dec_ref(v___x_2943_);
v___x_2945_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2930_, v_post_2931_, v_usedLetOnly_2932_, v_skipConstInApp_2933_, v___x_2941_, v_input_2929_, v_a_2944_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v_a_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2955_; 
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
lean_inc(v_a_2946_);
lean_dec_ref_known(v___x_2945_, 1);
v___x_2947_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2947_, 0, lean_box(0));
lean_closure_set(v___x_2947_, 1, lean_box(0));
lean_closure_set(v___x_2947_, 2, v_a_2944_);
v___x_2948_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___lam__0(lean_box(0), v___x_2947_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_2955_ == 0)
{
lean_object* v_unused_2956_; 
v_unused_2956_ = lean_ctor_get(v___x_2948_, 0);
lean_dec(v_unused_2956_);
v___x_2950_ = v___x_2948_;
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
else
{
lean_dec(v___x_2948_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2953_; 
if (v_isShared_2951_ == 0)
{
lean_ctor_set(v___x_2950_, 0, v_a_2946_);
v___x_2953_ = v___x_2950_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_a_2946_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
}
else
{
lean_dec(v_a_2944_);
return v___x_2945_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___boxed(lean_object* v_input_2957_, lean_object* v_pre_2958_, lean_object* v_post_2959_, lean_object* v_usedLetOnly_2960_, lean_object* v_skipConstInApp_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_){
_start:
{
uint8_t v_usedLetOnly_boxed_2969_; uint8_t v_skipConstInApp_boxed_2970_; lean_object* v_res_2971_; 
v_usedLetOnly_boxed_2969_ = lean_unbox(v_usedLetOnly_2960_);
v_skipConstInApp_boxed_2970_ = lean_unbox(v_skipConstInApp_2961_);
v_res_2971_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1(v_input_2957_, v_pre_2958_, v_post_2959_, v_usedLetOnly_boxed_2969_, v_skipConstInApp_boxed_2970_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
lean_dec(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec(v___y_2965_);
lean_dec_ref(v___y_2964_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts(lean_object* v_stx_3002_, lean_object* v_expectedType_x3f_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_){
_start:
{
lean_object* v___f_3011_; lean_object* v___f_3012_; lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___x_3044_; 
v___f_3011_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__0));
v___f_3012_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__1));
lean_inc(v_expectedType_x3f_3003_);
v___x_3044_ = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(v_expectedType_x3f_3003_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_dec_ref_known(v___x_3044_, 1);
if (lean_obj_tag(v_expectedType_x3f_3003_) == 1)
{
lean_object* v_val_3045_; lean_object* v___x_3046_; lean_object* v_a_3047_; uint8_t v___x_3048_; 
v_val_3045_ = lean_ctor_get(v_expectedType_x3f_3003_, 0);
lean_inc(v_val_3045_);
v___x_3046_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0___redArg(v_val_3045_, v_a_3007_);
v_a_3047_ = lean_ctor_get(v___x_3046_, 0);
lean_inc(v_a_3047_);
lean_dec_ref(v___x_3046_);
v___x_3048_ = l_Lean_Expr_hasExprMVar(v_a_3047_);
lean_dec(v_a_3047_);
if (v___x_3048_ == 0)
{
v___y_3014_ = v_a_3004_;
v___y_3015_ = v_a_3005_;
v___y_3016_ = v_a_3006_;
v___y_3017_ = v_a_3007_;
v___y_3018_ = v_a_3008_;
v___y_3019_ = v_a_3009_;
goto v___jp_3013_;
}
else
{
lean_object* v___x_3049_; 
v___x_3049_ = l_Lean_Elab_Term_tryPostpone(v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_);
if (lean_obj_tag(v___x_3049_) == 0)
{
lean_dec_ref_known(v___x_3049_, 1);
v___y_3014_ = v_a_3004_;
v___y_3015_ = v_a_3005_;
v___y_3016_ = v_a_3006_;
v___y_3017_ = v_a_3007_;
v___y_3018_ = v_a_3008_;
v___y_3019_ = v_a_3009_;
goto v___jp_3013_;
}
else
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3057_; 
lean_dec_ref_known(v_expectedType_x3f_3003_, 1);
v_a_3050_ = lean_ctor_get(v___x_3049_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3052_ = v___x_3049_;
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___x_3049_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3055_; 
if (v_isShared_3053_ == 0)
{
v___x_3055_ = v___x_3052_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_a_3050_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
}
}
else
{
v___y_3014_ = v_a_3004_;
v___y_3015_ = v_a_3005_;
v___y_3016_ = v_a_3006_;
v___y_3017_ = v_a_3007_;
v___y_3018_ = v_a_3008_;
v___y_3019_ = v_a_3009_;
goto v___jp_3013_;
}
}
else
{
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3065_; 
lean_dec(v_expectedType_x3f_3003_);
v_a_3058_ = lean_ctor_get(v___x_3044_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3060_ = v___x_3044_;
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_3044_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3063_; 
if (v_isShared_3061_ == 0)
{
v___x_3063_ = v___x_3060_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_a_3058_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
v___jp_3013_:
{
lean_object* v___x_3020_; lean_object* v___x_3021_; uint8_t v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; uint8_t v___x_3026_; lean_object* v___x_3027_; 
v___x_3020_ = lean_unsigned_to_nat(1u);
v___x_3021_ = l_Lean_Syntax_getArg(v_stx_3002_, v___x_3020_);
v___x_3022_ = 1;
v___x_3023_ = lean_box(v___x_3022_);
v___x_3024_ = lean_box(v___x_3022_);
v___x_3025_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(v___x_3025_, 0, v___x_3021_);
lean_closure_set(v___x_3025_, 1, v_expectedType_x3f_3003_);
lean_closure_set(v___x_3025_, 2, v___x_3023_);
lean_closure_set(v___x_3025_, 3, v___x_3024_);
v___x_3026_ = 1;
v___x_3027_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_3025_, v___x_3026_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
if (lean_obj_tag(v___x_3027_) == 0)
{
lean_object* v_a_3028_; lean_object* v___x_3029_; lean_object* v_a_3030_; uint8_t v___x_3031_; lean_object* v___x_3032_; 
v_a_3028_ = lean_ctor_get(v___x_3027_, 0);
lean_inc(v_a_3028_);
lean_dec_ref_known(v___x_3027_, 1);
v___x_3029_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0___redArg(v_a_3028_, v___y_3017_);
v_a_3030_ = lean_ctor_get(v___x_3029_, 0);
lean_inc_n(v_a_3030_, 2);
lean_dec_ref(v___x_3029_);
v___x_3031_ = 0;
v___x_3032_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1(v_a_3030_, v___f_3012_, v___f_3011_, v___x_3031_, v___x_3031_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v_a_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3043_; 
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3035_ = v___x_3032_;
v_isShared_3036_ = v_isSharedCheck_3043_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_a_3033_);
lean_dec(v___x_3032_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3043_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
uint8_t v___x_3037_; 
v___x_3037_ = lean_expr_eqv(v_a_3033_, v_a_3030_);
if (v___x_3037_ == 0)
{
lean_object* v___x_3038_; lean_object* v___x_3039_; 
lean_del_object(v___x_3035_);
lean_dec(v_a_3030_);
v___x_3038_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__10));
v___x_3039_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith(v___x_3038_, v_a_3033_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
return v___x_3039_;
}
else
{
lean_object* v___x_3041_; 
lean_dec(v_a_3033_);
if (v_isShared_3036_ == 0)
{
lean_ctor_set(v___x_3035_, 0, v_a_3030_);
v___x_3041_ = v___x_3035_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v_a_3030_);
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
else
{
lean_dec(v_a_3030_);
return v___x_3032_;
}
}
else
{
return v___x_3027_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts___boxed(lean_object* v_stx_3066_, lean_object* v_expectedType_x3f_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_){
_start:
{
lean_object* v_res_3075_; 
v_res_3075_ = l_Lean_Elab_Tactic_Do_elabContractEPosts(v_stx_3066_, v_expectedType_x3f_3067_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_);
lean_dec(v_a_3073_);
lean_dec_ref(v_a_3072_);
lean_dec(v_a_3071_);
lean_dec_ref(v_a_3070_);
lean_dec(v_a_3069_);
lean_dec_ref(v_a_3068_);
lean_dec(v_stx_3066_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4(lean_object* v_upperBound_3076_, lean_object* v___x_3077_, lean_object* v_pre_3078_, lean_object* v_post_3079_, uint8_t v_usedLetOnly_3080_, uint8_t v_skipConstInApp_3081_, uint8_t v_skipInstances_3082_, lean_object* v___x_3083_, lean_object* v_inst_3084_, lean_object* v_R_3085_, lean_object* v_a_3086_, lean_object* v_b_3087_, lean_object* v_c_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_){
_start:
{
lean_object* v___x_3097_; 
v___x_3097_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg(v_upperBound_3076_, v___x_3077_, v_pre_3078_, v_post_3079_, v_usedLetOnly_3080_, v_skipConstInApp_3081_, v_skipInstances_3082_, v_a_3086_, v_b_3087_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_);
return v___x_3097_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_3098_ = _args[0];
lean_object* v___x_3099_ = _args[1];
lean_object* v_pre_3100_ = _args[2];
lean_object* v_post_3101_ = _args[3];
lean_object* v_usedLetOnly_3102_ = _args[4];
lean_object* v_skipConstInApp_3103_ = _args[5];
lean_object* v_skipInstances_3104_ = _args[6];
lean_object* v___x_3105_ = _args[7];
lean_object* v_inst_3106_ = _args[8];
lean_object* v_R_3107_ = _args[9];
lean_object* v_a_3108_ = _args[10];
lean_object* v_b_3109_ = _args[11];
lean_object* v_c_3110_ = _args[12];
lean_object* v___y_3111_ = _args[13];
lean_object* v___y_3112_ = _args[14];
lean_object* v___y_3113_ = _args[15];
lean_object* v___y_3114_ = _args[16];
lean_object* v___y_3115_ = _args[17];
lean_object* v___y_3116_ = _args[18];
lean_object* v___y_3117_ = _args[19];
lean_object* v___y_3118_ = _args[20];
_start:
{
uint8_t v_usedLetOnly_boxed_3119_; uint8_t v_skipConstInApp_boxed_3120_; uint8_t v_skipInstances_boxed_3121_; lean_object* v_res_3122_; 
v_usedLetOnly_boxed_3119_ = lean_unbox(v_usedLetOnly_3102_);
v_skipConstInApp_boxed_3120_ = lean_unbox(v_skipConstInApp_3103_);
v_skipInstances_boxed_3121_ = lean_unbox(v_skipInstances_3104_);
v_res_3122_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4(v_upperBound_3098_, v___x_3099_, v_pre_3100_, v_post_3101_, v_usedLetOnly_boxed_3119_, v_skipConstInApp_boxed_3120_, v_skipInstances_boxed_3121_, v___x_3105_, v_inst_3106_, v_R_3107_, v_a_3108_, v_b_3109_, v_c_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3111_);
lean_dec(v___x_3105_);
lean_dec_ref(v___x_3099_);
lean_dec(v_upperBound_3098_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5(lean_object* v_00_u03b2_3123_, lean_object* v_m_3124_, lean_object* v_a_3125_){
_start:
{
lean_object* v___x_3126_; 
v___x_3126_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5___redArg(v_m_3124_, v_a_3125_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5___boxed(lean_object* v_00_u03b2_3127_, lean_object* v_m_3128_, lean_object* v_a_3129_){
_start:
{
lean_object* v_res_3130_; 
v_res_3130_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5(v_00_u03b2_3127_, v_m_3128_, v_a_3129_);
lean_dec_ref(v_a_3129_);
lean_dec_ref(v_m_3128_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8(lean_object* v_00_u03b1_3131_, lean_object* v_name_3132_, uint8_t v_bi_3133_, lean_object* v_type_3134_, lean_object* v_k_3135_, uint8_t v_kind_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_){
_start:
{
lean_object* v___x_3145_; 
v___x_3145_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg(v_name_3132_, v_bi_3133_, v_type_3134_, v_k_3135_, v_kind_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___boxed(lean_object* v_00_u03b1_3146_, lean_object* v_name_3147_, lean_object* v_bi_3148_, lean_object* v_type_3149_, lean_object* v_k_3150_, lean_object* v_kind_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_){
_start:
{
uint8_t v_bi_boxed_3160_; uint8_t v_kind_boxed_3161_; lean_object* v_res_3162_; 
v_bi_boxed_3160_ = lean_unbox(v_bi_3148_);
v_kind_boxed_3161_ = lean_unbox(v_kind_3151_);
v_res_3162_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8(v_00_u03b1_3146_, v_name_3147_, v_bi_boxed_3160_, v_type_3149_, v_k_3150_, v_kind_boxed_3161_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
return v_res_3162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11(lean_object* v_00_u03b1_3163_, lean_object* v_name_3164_, lean_object* v_type_3165_, lean_object* v_val_3166_, lean_object* v_k_3167_, uint8_t v_nondep_3168_, uint8_t v_kind_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_){
_start:
{
lean_object* v___x_3178_; 
v___x_3178_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11___redArg(v_name_3164_, v_type_3165_, v_val_3166_, v_k_3167_, v_nondep_3168_, v_kind_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
return v___x_3178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11___boxed(lean_object* v_00_u03b1_3179_, lean_object* v_name_3180_, lean_object* v_type_3181_, lean_object* v_val_3182_, lean_object* v_k_3183_, lean_object* v_nondep_3184_, lean_object* v_kind_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_){
_start:
{
uint8_t v_nondep_boxed_3194_; uint8_t v_kind_boxed_3195_; lean_object* v_res_3196_; 
v_nondep_boxed_3194_ = lean_unbox(v_nondep_3184_);
v_kind_boxed_3195_ = lean_unbox(v_kind_3185_);
v_res_3196_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11(v_00_u03b1_3179_, v_name_3180_, v_type_3181_, v_val_3182_, v_k_3183_, v_nondep_boxed_3194_, v_kind_boxed_3195_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3191_);
lean_dec(v___y_3190_);
lean_dec_ref(v___y_3189_);
lean_dec(v___y_3188_);
lean_dec_ref(v___y_3187_);
lean_dec(v___y_3186_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14(lean_object* v_00_u03b1_3197_, lean_object* v_ref_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_){
_start:
{
lean_object* v___x_3204_; 
v___x_3204_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_3198_);
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___boxed(lean_object* v_00_u03b1_3205_, lean_object* v_ref_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_){
_start:
{
lean_object* v_res_3212_; 
v_res_3212_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14(v_00_u03b1_3205_, v_ref_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
lean_dec(v___y_3210_);
lean_dec_ref(v___y_3209_);
lean_dec(v___y_3208_);
lean_dec_ref(v___y_3207_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10(lean_object* v_00_u03b1_3213_, lean_object* v_x_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_){
_start:
{
lean_object* v___x_3223_; 
v___x_3223_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10___redArg(v_x_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_);
return v___x_3223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10___boxed(lean_object* v_00_u03b1_3224_, lean_object* v_x_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_){
_start:
{
lean_object* v_res_3234_; 
v_res_3234_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10(v_00_u03b1_3224_, v_x_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec(v___y_3228_);
lean_dec_ref(v___y_3227_);
lean_dec(v___y_3226_);
return v_res_3234_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11(lean_object* v_00_u03b2_3235_, lean_object* v_m_3236_, lean_object* v_a_3237_, lean_object* v_b_3238_){
_start:
{
lean_object* v___x_3239_; 
v___x_3239_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11___redArg(v_m_3236_, v_a_3237_, v_b_3238_);
return v___x_3239_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5_spec__6(lean_object* v_00_u03b2_3240_, lean_object* v_a_3241_, lean_object* v_x_3242_){
_start:
{
lean_object* v___x_3243_; 
v___x_3243_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5_spec__6___redArg(v_a_3241_, v_x_3242_);
return v___x_3243_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5_spec__6___boxed(lean_object* v_00_u03b2_3244_, lean_object* v_a_3245_, lean_object* v_x_3246_){
_start:
{
lean_object* v_res_3247_; 
v_res_3247_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5_spec__6(v_00_u03b2_3244_, v_a_3245_, v_x_3246_);
lean_dec(v_x_3246_);
lean_dec_ref(v_a_3245_);
return v_res_3247_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16(lean_object* v_00_u03b2_3248_, lean_object* v_a_3249_, lean_object* v_x_3250_){
_start:
{
uint8_t v___x_3251_; 
v___x_3251_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16___redArg(v_a_3249_, v_x_3250_);
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16___boxed(lean_object* v_00_u03b2_3252_, lean_object* v_a_3253_, lean_object* v_x_3254_){
_start:
{
uint8_t v_res_3255_; lean_object* v_r_3256_; 
v_res_3255_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16(v_00_u03b2_3252_, v_a_3253_, v_x_3254_);
lean_dec(v_x_3254_);
lean_dec_ref(v_a_3253_);
v_r_3256_ = lean_box(v_res_3255_);
return v_r_3256_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17(lean_object* v_00_u03b2_3257_, lean_object* v_data_3258_){
_start:
{
lean_object* v___x_3259_; 
v___x_3259_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17___redArg(v_data_3258_);
return v___x_3259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__18(lean_object* v_00_u03b2_3260_, lean_object* v_a_3261_, lean_object* v_b_3262_, lean_object* v_x_3263_){
_start:
{
lean_object* v___x_3264_; 
v___x_3264_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__18___redArg(v_a_3261_, v_b_3262_, v_x_3263_);
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17_spec__18(lean_object* v_00_u03b2_3265_, lean_object* v_i_3266_, lean_object* v_source_3267_, lean_object* v_target_3268_){
_start:
{
lean_object* v___x_3269_; 
v___x_3269_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v_i_3266_, v_source_3267_, v_target_3268_);
return v___x_3269_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19(lean_object* v_00_u03b2_3270_, lean_object* v_x_3271_, lean_object* v_x_3272_){
_start:
{
lean_object* v___x_3273_; 
v___x_3273_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_x_3271_, v_x_3272_);
return v___x_3273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1(){
_start:
{
lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
v___x_3287_ = l_Lean_Elab_Term_termElabAttribute;
v___x_3288_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___closed__0));
v___x_3289_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___closed__2));
v___x_3290_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elabContractEPosts___boxed), 9, 0);
v___x_3291_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3287_, v___x_3288_, v___x_3289_, v___x_3290_);
return v___x_3291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___boxed(lean_object* v_a_3292_){
_start:
{
lean_object* v_res_3293_; 
v_res_3293_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1();
return v_res_3293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts_docString__3(){
_start:
{
lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3296_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___closed__2));
v___x_3297_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts_docString__3___closed__0));
v___x_3298_ = l_Lean_addBuiltinDocString(v___x_3296_, v___x_3297_);
return v___x_3298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts_docString__3___boxed(lean_object* v_a_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts_docString__3();
return v_res_3300_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0(uint8_t v_suppressElabErrors_3302_, lean_object* v_x_3303_){
_start:
{
if (lean_obj_tag(v_x_3303_) == 1)
{
lean_object* v_pre_3304_; 
v_pre_3304_ = lean_ctor_get(v_x_3303_, 0);
if (lean_obj_tag(v_pre_3304_) == 0)
{
lean_object* v_str_3305_; lean_object* v___x_3306_; uint8_t v___x_3307_; 
v_str_3305_ = lean_ctor_get(v_x_3303_, 1);
v___x_3306_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0___closed__0));
v___x_3307_ = lean_string_dec_eq(v_str_3305_, v___x_3306_);
if (v___x_3307_ == 0)
{
return v___x_3307_;
}
else
{
return v_suppressElabErrors_3302_;
}
}
else
{
uint8_t v___x_3308_; 
v___x_3308_ = 0;
return v___x_3308_;
}
}
else
{
uint8_t v___x_3309_; 
v___x_3309_ = 0;
return v___x_3309_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0___boxed(lean_object* v_suppressElabErrors_3310_, lean_object* v_x_3311_){
_start:
{
uint8_t v_suppressElabErrors_boxed_3312_; uint8_t v_res_3313_; lean_object* v_r_3314_; 
v_suppressElabErrors_boxed_3312_ = lean_unbox(v_suppressElabErrors_3310_);
v_res_3313_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0(v_suppressElabErrors_boxed_3312_, v_x_3311_);
lean_dec(v_x_3311_);
v_r_3314_ = lean_box(v_res_3313_);
return v_r_3314_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0(lean_object* v_opts_3315_, lean_object* v_opt_3316_){
_start:
{
lean_object* v_name_3317_; lean_object* v_defValue_3318_; lean_object* v_map_3319_; lean_object* v___x_3320_; 
v_name_3317_ = lean_ctor_get(v_opt_3316_, 0);
v_defValue_3318_ = lean_ctor_get(v_opt_3316_, 1);
v_map_3319_ = lean_ctor_get(v_opts_3315_, 0);
v___x_3320_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3319_, v_name_3317_);
if (lean_obj_tag(v___x_3320_) == 0)
{
uint8_t v___x_3321_; 
v___x_3321_ = lean_unbox(v_defValue_3318_);
return v___x_3321_;
}
else
{
lean_object* v_val_3322_; 
v_val_3322_ = lean_ctor_get(v___x_3320_, 0);
lean_inc(v_val_3322_);
lean_dec_ref_known(v___x_3320_, 1);
if (lean_obj_tag(v_val_3322_) == 1)
{
uint8_t v_v_3323_; 
v_v_3323_ = lean_ctor_get_uint8(v_val_3322_, 0);
lean_dec_ref_known(v_val_3322_, 0);
return v_v_3323_;
}
else
{
uint8_t v___x_3324_; 
lean_dec(v_val_3322_);
v___x_3324_ = lean_unbox(v_defValue_3318_);
return v___x_3324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0___boxed(lean_object* v_opts_3325_, lean_object* v_opt_3326_){
_start:
{
uint8_t v_res_3327_; lean_object* v_r_3328_; 
v_res_3327_ = l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0(v_opts_3325_, v_opt_3326_);
lean_dec_ref(v_opt_3326_);
lean_dec_ref(v_opts_3325_);
v_r_3328_ = lean_box(v_res_3327_);
return v_r_3328_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_3329_; lean_object* v___x_3330_; 
v___x_3329_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0);
v___x_3330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3329_);
return v___x_3330_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; 
v___x_3331_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_3332_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__0);
v___x_3333_ = lean_unsigned_to_nat(0u);
v___x_3334_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3333_);
lean_ctor_set(v___x_3334_, 1, v___x_3333_);
lean_ctor_set(v___x_3334_, 2, v___x_3333_);
lean_ctor_set(v___x_3334_, 3, v___x_3333_);
lean_ctor_set(v___x_3334_, 4, v___x_3332_);
lean_ctor_set(v___x_3334_, 5, v___x_3332_);
lean_ctor_set(v___x_3334_, 6, v___x_3332_);
lean_ctor_set(v___x_3334_, 7, v___x_3332_);
lean_ctor_set(v___x_3334_, 8, v___x_3332_);
lean_ctor_set(v___x_3334_, 9, v___x_3332_);
lean_ctor_set(v___x_3334_, 10, v___x_3332_);
lean_ctor_set(v___x_3334_, 11, v___x_3331_);
return v___x_3334_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
v___x_3335_ = lean_unsigned_to_nat(32u);
v___x_3336_ = lean_mk_empty_array_with_capacity(v___x_3335_);
v___x_3337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3336_);
return v___x_3337_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__3(void){
_start:
{
size_t v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; 
v___x_3338_ = ((size_t)5ULL);
v___x_3339_ = lean_unsigned_to_nat(0u);
v___x_3340_ = lean_unsigned_to_nat(32u);
v___x_3341_ = lean_mk_empty_array_with_capacity(v___x_3340_);
v___x_3342_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__2);
v___x_3343_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3343_, 0, v___x_3342_);
lean_ctor_set(v___x_3343_, 1, v___x_3341_);
lean_ctor_set(v___x_3343_, 2, v___x_3339_);
lean_ctor_set(v___x_3343_, 3, v___x_3339_);
lean_ctor_set_usize(v___x_3343_, 4, v___x_3338_);
return v___x_3343_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__4(void){
_start:
{
lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3344_ = lean_box(1);
v___x_3345_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__3);
v___x_3346_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__0);
v___x_3347_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3346_);
lean_ctor_set(v___x_3347_, 1, v___x_3345_);
lean_ctor_set(v___x_3347_, 2, v___x_3344_);
return v___x_3347_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_msgData_3348_, lean_object* v___y_3349_){
_start:
{
lean_object* v___x_3351_; lean_object* v_env_3352_; uint8_t v___x_3353_; lean_object* v_env_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v_scopes_3357_; lean_object* v___x_3358_; lean_object* v_opts_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3351_ = lean_st_ref_get(v___y_3349_);
v_env_3352_ = lean_ctor_get(v___x_3351_, 0);
lean_inc_ref(v_env_3352_);
lean_dec(v___x_3351_);
v___x_3353_ = 0;
v_env_3354_ = l_Lean_Environment_setRecordingDeps(v_env_3352_, v___x_3353_);
v___x_3355_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3356_ = lean_st_ref_get(v___y_3349_);
v_scopes_3357_ = lean_ctor_get(v___x_3356_, 2);
lean_inc(v_scopes_3357_);
lean_dec(v___x_3356_);
v___x_3358_ = l_List_head_x21___redArg(v___x_3355_, v_scopes_3357_);
lean_dec(v_scopes_3357_);
v_opts_3359_ = lean_ctor_get(v___x_3358_, 1);
lean_inc_ref(v_opts_3359_);
lean_dec(v___x_3358_);
v___x_3360_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__1);
v___x_3361_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__4);
v___x_3362_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3362_, 0, v_env_3354_);
lean_ctor_set(v___x_3362_, 1, v___x_3360_);
lean_ctor_set(v___x_3362_, 2, v___x_3361_);
lean_ctor_set(v___x_3362_, 3, v_opts_3359_);
v___x_3363_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3363_, 0, v___x_3362_);
lean_ctor_set(v___x_3363_, 1, v_msgData_3348_);
v___x_3364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3363_);
return v___x_3364_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_msgData_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_){
_start:
{
lean_object* v_res_3368_; 
v_res_3368_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg(v_msgData_3365_, v___y_3366_);
lean_dec(v___y_3366_);
return v_res_3368_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2(lean_object* v_ref_3369_, lean_object* v_msgData_3370_, uint8_t v_severity_3371_, uint8_t v_isSilent_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_){
_start:
{
lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3379_; uint8_t v___y_3380_; lean_object* v___y_3381_; uint8_t v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; uint8_t v___y_3442_; uint8_t v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; uint8_t v___y_3468_; uint8_t v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; uint8_t v___y_3475_; uint8_t v___y_3476_; uint8_t v___x_3491_; uint8_t v___y_3493_; uint8_t v___x_3503_; 
v___x_3491_ = 2;
v___x_3503_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3371_, v___x_3491_);
if (v___x_3503_ == 0)
{
v___y_3493_ = v___x_3503_;
goto v___jp_3492_;
}
else
{
uint8_t v___x_3504_; 
lean_inc_ref(v_msgData_3370_);
v___x_3504_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3370_);
if (v___x_3504_ == 0)
{
v___y_3493_ = v___x_3504_;
goto v___jp_3492_;
}
else
{
lean_object* v___x_3505_; lean_object* v___x_3506_; 
lean_dec_ref(v_msgData_3370_);
v___x_3505_ = lean_box(0);
v___x_3506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3506_, 0, v___x_3505_);
return v___x_3506_;
}
}
v___jp_3376_:
{
lean_object* v___x_3385_; 
v___x_3385_ = l_Lean_Elab_Command_getScope___redArg(v___y_3384_);
if (lean_obj_tag(v___x_3385_) == 0)
{
lean_object* v_a_3386_; lean_object* v_currNamespace_3387_; lean_object* v___x_3388_; 
v_a_3386_ = lean_ctor_get(v___x_3385_, 0);
lean_inc(v_a_3386_);
lean_dec_ref_known(v___x_3385_, 1);
v_currNamespace_3387_ = lean_ctor_get(v_a_3386_, 2);
lean_inc(v_currNamespace_3387_);
lean_dec(v_a_3386_);
v___x_3388_ = l_Lean_Elab_Command_getScope___redArg(v___y_3384_);
if (lean_obj_tag(v___x_3388_) == 0)
{
lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3424_; 
v_a_3389_ = lean_ctor_get(v___x_3388_, 0);
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3391_ = v___x_3388_;
v_isShared_3392_ = v_isSharedCheck_3424_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_dec(v___x_3388_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3424_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v_openDecls_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v_env_3398_; lean_object* v_messages_3399_; lean_object* v_scopes_3400_; lean_object* v_usedQuotCtxts_3401_; lean_object* v_nextMacroScope_3402_; lean_object* v_maxRecDepth_3403_; lean_object* v_ngen_3404_; lean_object* v_auxDeclNGen_3405_; lean_object* v_infoState_3406_; lean_object* v_traceState_3407_; lean_object* v_snapshotTasks_3408_; lean_object* v_prevLinterStates_3409_; lean_object* v_codeQualityEntryTasks_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3423_; 
v_openDecls_3393_ = lean_ctor_get(v_a_3389_, 3);
lean_inc(v_openDecls_3393_);
lean_dec(v_a_3389_);
v___x_3394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3394_, 0, v_currNamespace_3387_);
lean_ctor_set(v___x_3394_, 1, v_openDecls_3393_);
v___x_3395_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3395_, 0, v___x_3394_);
lean_ctor_set(v___x_3395_, 1, v___y_3377_);
lean_inc_ref(v___y_3383_);
lean_inc_ref(v___y_3379_);
v___x_3396_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3396_, 0, v___y_3379_);
lean_ctor_set(v___x_3396_, 1, v___y_3378_);
lean_ctor_set(v___x_3396_, 2, v___y_3381_);
lean_ctor_set(v___x_3396_, 3, v___y_3383_);
lean_ctor_set(v___x_3396_, 4, v___x_3395_);
lean_ctor_set_uint8(v___x_3396_, sizeof(void*)*5, v___y_3382_);
lean_ctor_set_uint8(v___x_3396_, sizeof(void*)*5 + 1, v___y_3380_);
lean_ctor_set_uint8(v___x_3396_, sizeof(void*)*5 + 2, v_isSilent_3372_);
v___x_3397_ = lean_st_ref_take(v___y_3384_);
v_env_3398_ = lean_ctor_get(v___x_3397_, 0);
v_messages_3399_ = lean_ctor_get(v___x_3397_, 1);
v_scopes_3400_ = lean_ctor_get(v___x_3397_, 2);
v_usedQuotCtxts_3401_ = lean_ctor_get(v___x_3397_, 3);
v_nextMacroScope_3402_ = lean_ctor_get(v___x_3397_, 4);
v_maxRecDepth_3403_ = lean_ctor_get(v___x_3397_, 5);
v_ngen_3404_ = lean_ctor_get(v___x_3397_, 6);
v_auxDeclNGen_3405_ = lean_ctor_get(v___x_3397_, 7);
v_infoState_3406_ = lean_ctor_get(v___x_3397_, 8);
v_traceState_3407_ = lean_ctor_get(v___x_3397_, 9);
v_snapshotTasks_3408_ = lean_ctor_get(v___x_3397_, 10);
v_prevLinterStates_3409_ = lean_ctor_get(v___x_3397_, 11);
v_codeQualityEntryTasks_3410_ = lean_ctor_get(v___x_3397_, 12);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3412_ = v___x_3397_;
v_isShared_3413_ = v_isSharedCheck_3423_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3410_);
lean_inc(v_prevLinterStates_3409_);
lean_inc(v_snapshotTasks_3408_);
lean_inc(v_traceState_3407_);
lean_inc(v_infoState_3406_);
lean_inc(v_auxDeclNGen_3405_);
lean_inc(v_ngen_3404_);
lean_inc(v_maxRecDepth_3403_);
lean_inc(v_nextMacroScope_3402_);
lean_inc(v_usedQuotCtxts_3401_);
lean_inc(v_scopes_3400_);
lean_inc(v_messages_3399_);
lean_inc(v_env_3398_);
lean_dec(v___x_3397_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3423_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3417_; 
v___x_3414_ = lean_box(0);
v___x_3415_ = l_Lean_MessageLog_add(v___x_3396_, v_messages_3399_);
if (v_isShared_3413_ == 0)
{
lean_ctor_set(v___x_3412_, 1, v___x_3415_);
v___x_3417_ = v___x_3412_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_env_3398_);
lean_ctor_set(v_reuseFailAlloc_3422_, 1, v___x_3415_);
lean_ctor_set(v_reuseFailAlloc_3422_, 2, v_scopes_3400_);
lean_ctor_set(v_reuseFailAlloc_3422_, 3, v_usedQuotCtxts_3401_);
lean_ctor_set(v_reuseFailAlloc_3422_, 4, v_nextMacroScope_3402_);
lean_ctor_set(v_reuseFailAlloc_3422_, 5, v_maxRecDepth_3403_);
lean_ctor_set(v_reuseFailAlloc_3422_, 6, v_ngen_3404_);
lean_ctor_set(v_reuseFailAlloc_3422_, 7, v_auxDeclNGen_3405_);
lean_ctor_set(v_reuseFailAlloc_3422_, 8, v_infoState_3406_);
lean_ctor_set(v_reuseFailAlloc_3422_, 9, v_traceState_3407_);
lean_ctor_set(v_reuseFailAlloc_3422_, 10, v_snapshotTasks_3408_);
lean_ctor_set(v_reuseFailAlloc_3422_, 11, v_prevLinterStates_3409_);
lean_ctor_set(v_reuseFailAlloc_3422_, 12, v_codeQualityEntryTasks_3410_);
v___x_3417_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
lean_object* v___x_3418_; lean_object* v___x_3420_; 
v___x_3418_ = lean_st_ref_put(v___y_3384_, v___x_3417_);
if (v_isShared_3392_ == 0)
{
lean_ctor_set(v___x_3391_, 0, v___x_3414_);
v___x_3420_ = v___x_3391_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v___x_3414_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
}
}
}
else
{
lean_object* v_a_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3432_; 
lean_dec(v_currNamespace_3387_);
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3378_);
lean_dec_ref(v___y_3377_);
v_a_3425_ = lean_ctor_get(v___x_3388_, 0);
v_isSharedCheck_3432_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3432_ == 0)
{
v___x_3427_ = v___x_3388_;
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_a_3425_);
lean_dec(v___x_3388_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v___x_3430_; 
if (v_isShared_3428_ == 0)
{
v___x_3430_ = v___x_3427_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v_a_3425_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
return v___x_3430_;
}
}
}
}
else
{
lean_object* v_a_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3440_; 
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3378_);
lean_dec_ref(v___y_3377_);
v_a_3433_ = lean_ctor_get(v___x_3385_, 0);
v_isSharedCheck_3440_ = !lean_is_exclusive(v___x_3385_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3435_ = v___x_3385_;
v_isShared_3436_ = v_isSharedCheck_3440_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_a_3433_);
lean_dec(v___x_3385_);
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
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v_a_3433_);
v___x_3438_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
return v___x_3438_;
}
}
}
}
v___jp_3441_:
{
lean_object* v_fileName_3446_; lean_object* v_fileMap_3447_; uint8_t v_suppressElabErrors_3448_; lean_object* v___x_3449_; lean_object* v___f_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v_a_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3466_; 
v_fileName_3446_ = lean_ctor_get(v___y_3373_, 0);
v_fileMap_3447_ = lean_ctor_get(v___y_3373_, 1);
v_suppressElabErrors_3448_ = lean_ctor_get_uint8(v___y_3373_, sizeof(void*)*10);
v___x_3449_ = lean_box(v_suppressElabErrors_3448_);
v___f_3450_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3450_, 0, v___x_3449_);
v___x_3451_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3370_);
v___x_3452_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg(v___x_3451_, v___y_3374_);
v_a_3453_ = lean_ctor_get(v___x_3452_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3452_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3455_ = v___x_3452_;
v_isShared_3456_ = v_isSharedCheck_3466_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_a_3453_);
lean_dec(v___x_3452_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3466_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; 
lean_inc_ref_n(v_fileMap_3447_, 2);
v___x_3457_ = l_Lean_FileMap_toPosition(v_fileMap_3447_, v___y_3444_);
lean_dec(v___y_3444_);
v___x_3458_ = l_Lean_FileMap_toPosition(v_fileMap_3447_, v___y_3445_);
lean_dec(v___y_3445_);
v___x_3459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3459_, 0, v___x_3458_);
v___x_3460_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__19));
if (v_suppressElabErrors_3448_ == 0)
{
lean_del_object(v___x_3455_);
lean_dec_ref(v___f_3450_);
v___y_3377_ = v_a_3453_;
v___y_3378_ = v___x_3457_;
v___y_3379_ = v_fileName_3446_;
v___y_3380_ = v___y_3442_;
v___y_3381_ = v___x_3459_;
v___y_3382_ = v___y_3443_;
v___y_3383_ = v___x_3460_;
v___y_3384_ = v___y_3374_;
goto v___jp_3376_;
}
else
{
uint8_t v___x_3461_; 
lean_inc(v_a_3453_);
v___x_3461_ = l_Lean_MessageData_hasTag(v___f_3450_, v_a_3453_);
if (v___x_3461_ == 0)
{
lean_object* v___x_3462_; lean_object* v___x_3464_; 
lean_dec_ref_known(v___x_3459_, 1);
lean_dec_ref(v___x_3457_);
lean_dec(v_a_3453_);
v___x_3462_ = lean_box(0);
if (v_isShared_3456_ == 0)
{
lean_ctor_set(v___x_3455_, 0, v___x_3462_);
v___x_3464_ = v___x_3455_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v___x_3462_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
return v___x_3464_;
}
}
else
{
lean_del_object(v___x_3455_);
v___y_3377_ = v_a_3453_;
v___y_3378_ = v___x_3457_;
v___y_3379_ = v_fileName_3446_;
v___y_3380_ = v___y_3442_;
v___y_3381_ = v___x_3459_;
v___y_3382_ = v___y_3443_;
v___y_3383_ = v___x_3460_;
v___y_3384_ = v___y_3374_;
goto v___jp_3376_;
}
}
}
}
v___jp_3467_:
{
lean_object* v___x_3472_; 
v___x_3472_ = l_Lean_Syntax_getTailPos_x3f(v___y_3470_, v___y_3469_);
lean_dec(v___y_3470_);
if (lean_obj_tag(v___x_3472_) == 0)
{
lean_inc(v___y_3471_);
v___y_3442_ = v___y_3468_;
v___y_3443_ = v___y_3469_;
v___y_3444_ = v___y_3471_;
v___y_3445_ = v___y_3471_;
goto v___jp_3441_;
}
else
{
lean_object* v_val_3473_; 
v_val_3473_ = lean_ctor_get(v___x_3472_, 0);
lean_inc(v_val_3473_);
lean_dec_ref_known(v___x_3472_, 1);
v___y_3442_ = v___y_3468_;
v___y_3443_ = v___y_3469_;
v___y_3444_ = v___y_3471_;
v___y_3445_ = v_val_3473_;
goto v___jp_3441_;
}
}
v___jp_3474_:
{
lean_object* v___x_3477_; 
v___x_3477_ = l_Lean_Elab_Command_getRef___redArg(v___y_3373_);
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v_a_3478_; lean_object* v_ref_3479_; lean_object* v___x_3480_; 
v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
lean_inc(v_a_3478_);
lean_dec_ref_known(v___x_3477_, 1);
v_ref_3479_ = l_Lean_replaceRef(v_ref_3369_, v_a_3478_);
lean_dec(v_a_3478_);
v___x_3480_ = l_Lean_Syntax_getPos_x3f(v_ref_3479_, v___y_3475_);
if (lean_obj_tag(v___x_3480_) == 0)
{
lean_object* v___x_3481_; 
v___x_3481_ = lean_unsigned_to_nat(0u);
v___y_3468_ = v___y_3476_;
v___y_3469_ = v___y_3475_;
v___y_3470_ = v_ref_3479_;
v___y_3471_ = v___x_3481_;
goto v___jp_3467_;
}
else
{
lean_object* v_val_3482_; 
v_val_3482_ = lean_ctor_get(v___x_3480_, 0);
lean_inc(v_val_3482_);
lean_dec_ref_known(v___x_3480_, 1);
v___y_3468_ = v___y_3476_;
v___y_3469_ = v___y_3475_;
v___y_3470_ = v_ref_3479_;
v___y_3471_ = v_val_3482_;
goto v___jp_3467_;
}
}
else
{
lean_object* v_a_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3490_; 
lean_dec_ref(v_msgData_3370_);
v_a_3483_ = lean_ctor_get(v___x_3477_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3485_ = v___x_3477_;
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_a_3483_);
lean_dec(v___x_3477_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3488_; 
if (v_isShared_3486_ == 0)
{
v___x_3488_ = v___x_3485_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_a_3483_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
}
}
v___jp_3492_:
{
lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v_scopes_3496_; lean_object* v___x_3497_; lean_object* v_opts_3498_; uint8_t v___x_3499_; uint8_t v___x_3500_; 
v___x_3494_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3495_ = lean_st_ref_get(v___y_3374_);
v_scopes_3496_ = lean_ctor_get(v___x_3495_, 2);
lean_inc(v_scopes_3496_);
lean_dec(v___x_3495_);
v___x_3497_ = l_List_head_x21___redArg(v___x_3494_, v_scopes_3496_);
lean_dec(v_scopes_3496_);
v_opts_3498_ = lean_ctor_get(v___x_3497_, 1);
lean_inc_ref(v_opts_3498_);
lean_dec(v___x_3497_);
v___x_3499_ = 1;
v___x_3500_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3371_, v___x_3499_);
if (v___x_3500_ == 0)
{
lean_dec_ref(v_opts_3498_);
v___y_3475_ = v___y_3493_;
v___y_3476_ = v_severity_3371_;
goto v___jp_3474_;
}
else
{
lean_object* v___x_3501_; uint8_t v___x_3502_; 
v___x_3501_ = l_Lean_warningAsError;
v___x_3502_ = l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0(v_opts_3498_, v___x_3501_);
lean_dec_ref(v_opts_3498_);
if (v___x_3502_ == 0)
{
v___y_3475_ = v___y_3493_;
v___y_3476_ = v_severity_3371_;
goto v___jp_3474_;
}
else
{
v___y_3475_ = v___y_3493_;
v___y_3476_ = v___x_3491_;
goto v___jp_3474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___boxed(lean_object* v_ref_3507_, lean_object* v_msgData_3508_, lean_object* v_severity_3509_, lean_object* v_isSilent_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_){
_start:
{
uint8_t v_severity_boxed_3514_; uint8_t v_isSilent_boxed_3515_; lean_object* v_res_3516_; 
v_severity_boxed_3514_ = lean_unbox(v_severity_3509_);
v_isSilent_boxed_3515_ = lean_unbox(v_isSilent_3510_);
v_res_3516_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2(v_ref_3507_, v_msgData_3508_, v_severity_boxed_3514_, v_isSilent_boxed_3515_, v___y_3511_, v___y_3512_);
lean_dec(v___y_3512_);
lean_dec_ref(v___y_3511_);
lean_dec(v_ref_3507_);
return v_res_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1(lean_object* v_ref_3517_, lean_object* v_msgData_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_){
_start:
{
uint8_t v___x_3522_; uint8_t v___x_3523_; lean_object* v___x_3524_; 
v___x_3522_ = 1;
v___x_3523_ = 0;
v___x_3524_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2(v_ref_3517_, v_msgData_3518_, v___x_3522_, v___x_3523_, v___y_3519_, v___y_3520_);
return v___x_3524_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1___boxed(lean_object* v_ref_3525_, lean_object* v_msgData_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_){
_start:
{
lean_object* v_res_3530_; 
v_res_3530_ = l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1(v_ref_3525_, v_msgData_3526_, v___y_3527_, v___y_3528_);
lean_dec(v___y_3528_);
lean_dec_ref(v___y_3527_);
lean_dec(v_ref_3525_);
return v_res_3530_;
}
}
static lean_object* _init_l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; 
v___x_3532_ = ((lean_object*)(l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__0));
v___x_3533_ = l_Lean_stringToMessageData(v___x_3532_);
return v___x_3533_;
}
}
static lean_object* _init_l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3535_ = ((lean_object*)(l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__2));
v___x_3536_ = l_Lean_stringToMessageData(v___x_3535_);
return v___x_3536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0(lean_object* v_kw_3537_, lean_object* v_what_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_){
_start:
{
lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v_scopes_3544_; lean_object* v___x_3545_; lean_object* v_opts_3546_; lean_object* v___x_3547_; uint8_t v___x_3548_; 
v___x_3542_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3543_ = lean_st_ref_get(v___y_3540_);
v_scopes_3544_ = lean_ctor_get(v___x_3543_, 2);
lean_inc(v_scopes_3544_);
lean_dec(v___x_3543_);
v___x_3545_ = l_List_head_x21___redArg(v___x_3542_, v_scopes_3544_);
lean_dec(v_scopes_3544_);
v_opts_3546_ = lean_ctor_get(v___x_3545_, 1);
lean_inc_ref(v_opts_3546_);
lean_dec(v___x_3545_);
v___x_3547_ = l_Lean_Elab_Do_experimental_intrinsic;
v___x_3548_ = l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0(v_opts_3546_, v___x_3547_);
lean_dec_ref(v_opts_3546_);
if (v___x_3548_ == 0)
{
lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3549_ = lean_obj_once(&l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1, &l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1_once, _init_l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1);
v___x_3550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3550_, 0, v___x_3549_);
lean_ctor_set(v___x_3550_, 1, v_what_3538_);
v___x_3551_ = lean_obj_once(&l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3, &l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3_once, _init_l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3);
v___x_3552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3552_, 0, v___x_3550_);
lean_ctor_set(v___x_3552_, 1, v___x_3551_);
v___x_3553_ = l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1(v_kw_3537_, v___x_3552_, v___y_3539_, v___y_3540_);
return v___x_3553_;
}
else
{
lean_object* v___x_3554_; lean_object* v___x_3555_; 
lean_dec_ref(v_what_3538_);
v___x_3554_ = lean_box(0);
v___x_3555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3555_, 0, v___x_3554_);
return v___x_3555_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___boxed(lean_object* v_kw_3556_, lean_object* v_what_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_){
_start:
{
lean_object* v_res_3561_; 
v_res_3561_ = l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0(v_kw_3556_, v_what_3557_, v___y_3558_, v___y_3559_);
lean_dec(v___y_3559_);
lean_dec_ref(v___y_3558_);
lean_dec(v_kw_3556_);
return v_res_3561_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3563_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__0));
v___x_3564_ = l_Lean_stringToMessageData(v___x_3563_);
return v___x_3564_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__3(void){
_start:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; 
v___x_3566_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__2));
v___x_3567_ = l_Lean_stringToMessageData(v___x_3566_);
return v___x_3567_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1(lean_object* v_as_3568_, size_t v_sz_3569_, size_t v_i_3570_, lean_object* v_b_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_){
_start:
{
uint8_t v___x_3575_; 
v___x_3575_ = lean_usize_dec_lt(v_i_3570_, v_sz_3569_);
if (v___x_3575_ == 0)
{
lean_object* v___x_3576_; 
v___x_3576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3576_, 0, v_b_3571_);
return v___x_3576_;
}
else
{
lean_object* v___x_3577_; lean_object* v_a_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3577_ = lean_box(0);
v_a_3578_ = lean_array_uget_borrowed(v_as_3568_, v_i_3570_);
v___x_3579_ = lean_unsigned_to_nat(0u);
v___x_3580_ = l_Lean_Syntax_getArg(v_a_3578_, v___x_3579_);
v___x_3581_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__1);
v___x_3582_ = l_Lean_Syntax_getAtomVal(v___x_3580_);
v___x_3583_ = l_Lean_stringToMessageData(v___x_3582_);
v___x_3584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3581_);
lean_ctor_set(v___x_3584_, 1, v___x_3583_);
v___x_3585_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__3);
v___x_3586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3586_, 0, v___x_3584_);
lean_ctor_set(v___x_3586_, 1, v___x_3585_);
v___x_3587_ = l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0(v___x_3580_, v___x_3586_, v___y_3572_, v___y_3573_);
lean_dec(v___x_3580_);
if (lean_obj_tag(v___x_3587_) == 0)
{
size_t v___x_3588_; size_t v___x_3589_; 
lean_dec_ref_known(v___x_3587_, 1);
v___x_3588_ = ((size_t)1ULL);
v___x_3589_ = lean_usize_add(v_i_3570_, v___x_3588_);
v_i_3570_ = v___x_3589_;
v_b_3571_ = v___x_3577_;
goto _start;
}
else
{
return v___x_3587_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___boxed(lean_object* v_as_3591_, lean_object* v_sz_3592_, lean_object* v_i_3593_, lean_object* v_b_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_){
_start:
{
size_t v_sz_boxed_3598_; size_t v_i_boxed_3599_; lean_object* v_res_3600_; 
v_sz_boxed_3598_ = lean_unbox_usize(v_sz_3592_);
lean_dec(v_sz_3592_);
v_i_boxed_3599_ = lean_unbox_usize(v_i_3593_);
lean_dec(v_i_3593_);
v_res_3600_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1(v_as_3591_, v_sz_boxed_3598_, v_i_boxed_3599_, v_b_3594_, v___y_3595_, v___y_3596_);
lean_dec(v___y_3596_);
lean_dec_ref(v___y_3595_);
lean_dec_ref(v_as_3591_);
return v_res_3600_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__2(lean_object* v_as_3601_, size_t v_sz_3602_, size_t v_i_3603_, lean_object* v_b_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_){
_start:
{
uint8_t v___x_3608_; 
v___x_3608_ = lean_usize_dec_lt(v_i_3603_, v_sz_3602_);
if (v___x_3608_ == 0)
{
lean_object* v___x_3609_; 
v___x_3609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3609_, 0, v_b_3604_);
return v___x_3609_;
}
else
{
lean_object* v___x_3610_; lean_object* v_a_3611_; lean_object* v___x_3612_; size_t v_sz_3613_; size_t v___x_3614_; lean_object* v___x_3615_; 
v___x_3610_ = lean_box(0);
v_a_3611_ = lean_array_uget_borrowed(v_as_3601_, v_i_3603_);
v___x_3612_ = l_Lean_Syntax_getArgs(v_a_3611_);
v_sz_3613_ = lean_array_size(v___x_3612_);
v___x_3614_ = ((size_t)0ULL);
v___x_3615_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1(v___x_3612_, v_sz_3613_, v___x_3614_, v___x_3610_, v___y_3605_, v___y_3606_);
lean_dec_ref(v___x_3612_);
if (lean_obj_tag(v___x_3615_) == 0)
{
size_t v___x_3616_; size_t v___x_3617_; 
lean_dec_ref_known(v___x_3615_, 1);
v___x_3616_ = ((size_t)1ULL);
v___x_3617_ = lean_usize_add(v_i_3603_, v___x_3616_);
v_i_3603_ = v___x_3617_;
v_b_3604_ = v___x_3610_;
goto _start;
}
else
{
return v___x_3615_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__2___boxed(lean_object* v_as_3619_, lean_object* v_sz_3620_, lean_object* v_i_3621_, lean_object* v_b_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_){
_start:
{
size_t v_sz_boxed_3626_; size_t v_i_boxed_3627_; lean_object* v_res_3628_; 
v_sz_boxed_3626_ = lean_unbox_usize(v_sz_3620_);
lean_dec(v_sz_3620_);
v_i_boxed_3627_ = lean_unbox_usize(v_i_3621_);
lean_dec(v_i_3621_);
v_res_3628_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__2(v_as_3619_, v_sz_boxed_3626_, v_i_boxed_3627_, v_b_3622_, v___y_3623_, v___y_3624_);
lean_dec(v___y_3624_);
lean_dec_ref(v___y_3623_);
lean_dec_ref(v_as_3619_);
return v_res_3628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractNotice(lean_object* v_stx_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_){
_start:
{
lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; size_t v_sz_3636_; size_t v___x_3637_; lean_object* v___x_3638_; 
v___x_3633_ = l_Lean_Syntax_getArgs(v_stx_3629_);
v___x_3634_ = lean_array_pop(v___x_3633_);
v___x_3635_ = lean_box(0);
v_sz_3636_ = lean_array_size(v___x_3634_);
v___x_3637_ = ((size_t)0ULL);
v___x_3638_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__2(v___x_3634_, v_sz_3636_, v___x_3637_, v___x_3635_, v_a_3630_, v_a_3631_);
lean_dec_ref(v___x_3634_);
if (lean_obj_tag(v___x_3638_) == 0)
{
lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3645_; 
v_isSharedCheck_3645_ = !lean_is_exclusive(v___x_3638_);
if (v_isSharedCheck_3645_ == 0)
{
lean_object* v_unused_3646_; 
v_unused_3646_ = lean_ctor_get(v___x_3638_, 0);
lean_dec(v_unused_3646_);
v___x_3640_ = v___x_3638_;
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
else
{
lean_dec(v___x_3638_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v___x_3643_; 
if (v_isShared_3641_ == 0)
{
lean_ctor_set(v___x_3640_, 0, v___x_3635_);
v___x_3643_ = v___x_3640_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v___x_3635_);
v___x_3643_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
return v___x_3643_;
}
}
}
else
{
return v___x_3638_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractNotice___boxed(lean_object* v_stx_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_){
_start:
{
lean_object* v_res_3651_; 
v_res_3651_ = l_Lean_Elab_Tactic_Do_elabContractNotice(v_stx_3647_, v_a_3648_, v_a_3649_);
lean_dec(v_a_3649_);
lean_dec_ref(v_a_3648_);
lean_dec(v_stx_3647_);
return v_res_3651_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5(lean_object* v_msgData_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_){
_start:
{
lean_object* v___x_3656_; 
v___x_3656_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg(v_msgData_3652_, v___y_3654_);
return v___x_3656_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___boxed(lean_object* v_msgData_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_){
_start:
{
lean_object* v_res_3661_; 
v_res_3661_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5(v_msgData_3657_, v___y_3658_, v___y_3659_);
lean_dec(v___y_3659_);
lean_dec_ref(v___y_3658_);
return v_res_3661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1(){
_start:
{
lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; 
v___x_3670_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3671_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__1));
v___x_3672_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__1));
v___x_3673_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elabContractNotice___boxed), 4, 0);
v___x_3674_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3670_, v___x_3671_, v___x_3672_, v___x_3673_);
return v___x_3674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___boxed(lean_object* v_a_3675_){
_start:
{
lean_object* v_res_3676_; 
v_res_3676_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1();
return v_res_3676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice_docString__3(){
_start:
{
lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; 
v___x_3679_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__1));
v___x_3680_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice_docString__3___closed__0));
v___x_3681_ = l_Lean_addBuiltinDocString(v___x_3679_, v___x_3680_);
return v___x_3681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice_docString__3___boxed(lean_object* v_a_3682_){
_start:
{
lean_object* v_res_3683_; 
v_res_3683_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice_docString__3();
return v_res_3683_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; 
v___x_3684_ = lean_box(0);
v___x_3685_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3686_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3686_, 0, v___x_3685_);
lean_ctor_set(v___x_3686_, 1, v___x_3684_);
return v___x_3686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg(){
_start:
{
lean_object* v___x_3688_; lean_object* v___x_3689_; 
v___x_3688_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg___closed__0);
v___x_3689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3689_, 0, v___x_3688_);
return v___x_3689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg___boxed(lean_object* v___y_3690_){
_start:
{
lean_object* v_res_3691_; 
v_res_3691_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg();
return v_res_3691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2(lean_object* v_00_u03b1_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_){
_start:
{
lean_object* v___x_3701_; 
v___x_3701_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg();
return v___x_3701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___boxed(lean_object* v_00_u03b1_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_){
_start:
{
lean_object* v_res_3711_; 
v_res_3711_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2(v_00_u03b1_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_);
lean_dec(v___y_3709_);
lean_dec_ref(v___y_3708_);
lean_dec(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec_ref(v___y_3703_);
return v_res_3711_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2_spec__5(lean_object* v_msgData_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_){
_start:
{
lean_object* v___x_3718_; lean_object* v_env_3719_; uint8_t v___x_3720_; lean_object* v_env_3721_; lean_object* v___x_3722_; lean_object* v_toCold_3723_; lean_object* v_mctx_3724_; lean_object* v_lctx_3725_; lean_object* v_options_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; 
v___x_3718_ = lean_st_ref_get(v___y_3716_);
v_env_3719_ = lean_ctor_get(v___x_3718_, 0);
lean_inc_ref(v_env_3719_);
lean_dec(v___x_3718_);
v___x_3720_ = 0;
v_env_3721_ = l_Lean_Environment_setRecordingDeps(v_env_3719_, v___x_3720_);
v___x_3722_ = lean_st_ref_get(v___y_3714_);
v_toCold_3723_ = lean_ctor_get(v___y_3715_, 0);
v_mctx_3724_ = lean_ctor_get(v___x_3722_, 0);
lean_inc_ref(v_mctx_3724_);
lean_dec(v___x_3722_);
v_lctx_3725_ = lean_ctor_get(v___y_3713_, 2);
v_options_3726_ = lean_ctor_get(v_toCold_3723_, 2);
lean_inc_ref(v_options_3726_);
lean_inc_ref(v_lctx_3725_);
v___x_3727_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3727_, 0, v_env_3721_);
lean_ctor_set(v___x_3727_, 1, v_mctx_3724_);
lean_ctor_set(v___x_3727_, 2, v_lctx_3725_);
lean_ctor_set(v___x_3727_, 3, v_options_3726_);
v___x_3728_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3728_, 0, v___x_3727_);
lean_ctor_set(v___x_3728_, 1, v_msgData_3712_);
v___x_3729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3728_);
return v___x_3729_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2_spec__5___boxed(lean_object* v_msgData_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_){
_start:
{
lean_object* v_res_3736_; 
v_res_3736_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2_spec__5(v_msgData_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_);
lean_dec(v___y_3734_);
lean_dec_ref(v___y_3733_);
lean_dec(v___y_3732_);
lean_dec_ref(v___y_3731_);
return v_res_3736_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0(uint8_t v_suppressElabErrors_3742_, lean_object* v_x_3743_){
_start:
{
if (lean_obj_tag(v_x_3743_) == 1)
{
lean_object* v_pre_3744_; 
v_pre_3744_ = lean_ctor_get(v_x_3743_, 0);
switch(lean_obj_tag(v_pre_3744_))
{
case 1:
{
lean_object* v_pre_3745_; 
v_pre_3745_ = lean_ctor_get(v_pre_3744_, 0);
switch(lean_obj_tag(v_pre_3745_))
{
case 0:
{
lean_object* v_str_3746_; lean_object* v_str_3747_; lean_object* v___x_3748_; uint8_t v___x_3749_; 
v_str_3746_ = lean_ctor_get(v_x_3743_, 1);
v_str_3747_ = lean_ctor_get(v_pre_3744_, 1);
v___x_3748_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__21));
v___x_3749_ = lean_string_dec_eq(v_str_3747_, v___x_3748_);
if (v___x_3749_ == 0)
{
lean_object* v___x_3750_; uint8_t v___x_3751_; 
v___x_3750_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__22));
v___x_3751_ = lean_string_dec_eq(v_str_3747_, v___x_3750_);
if (v___x_3751_ == 0)
{
return v___x_3751_;
}
else
{
lean_object* v___x_3752_; uint8_t v___x_3753_; 
v___x_3752_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__0));
v___x_3753_ = lean_string_dec_eq(v_str_3746_, v___x_3752_);
if (v___x_3753_ == 0)
{
return v___x_3753_;
}
else
{
return v_suppressElabErrors_3742_;
}
}
}
else
{
lean_object* v___x_3754_; uint8_t v___x_3755_; 
v___x_3754_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__1));
v___x_3755_ = lean_string_dec_eq(v_str_3746_, v___x_3754_);
if (v___x_3755_ == 0)
{
return v___x_3755_;
}
else
{
return v_suppressElabErrors_3742_;
}
}
}
case 1:
{
lean_object* v_pre_3756_; 
v_pre_3756_ = lean_ctor_get(v_pre_3745_, 0);
if (lean_obj_tag(v_pre_3756_) == 0)
{
lean_object* v_str_3757_; lean_object* v_str_3758_; lean_object* v_str_3759_; lean_object* v___x_3760_; uint8_t v___x_3761_; 
v_str_3757_ = lean_ctor_get(v_x_3743_, 1);
v_str_3758_ = lean_ctor_get(v_pre_3744_, 1);
v_str_3759_ = lean_ctor_get(v_pre_3745_, 1);
v___x_3760_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__2));
v___x_3761_ = lean_string_dec_eq(v_str_3759_, v___x_3760_);
if (v___x_3761_ == 0)
{
return v___x_3761_;
}
else
{
lean_object* v___x_3762_; uint8_t v___x_3763_; 
v___x_3762_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__3));
v___x_3763_ = lean_string_dec_eq(v_str_3758_, v___x_3762_);
if (v___x_3763_ == 0)
{
return v___x_3763_;
}
else
{
lean_object* v___x_3764_; uint8_t v___x_3765_; 
v___x_3764_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__4));
v___x_3765_ = lean_string_dec_eq(v_str_3757_, v___x_3764_);
if (v___x_3765_ == 0)
{
return v___x_3765_;
}
else
{
return v_suppressElabErrors_3742_;
}
}
}
}
else
{
uint8_t v___x_3766_; 
v___x_3766_ = 0;
return v___x_3766_;
}
}
default: 
{
uint8_t v___x_3767_; 
v___x_3767_ = 0;
return v___x_3767_;
}
}
}
case 0:
{
lean_object* v_str_3768_; lean_object* v___x_3769_; uint8_t v___x_3770_; 
v_str_3768_ = lean_ctor_get(v_x_3743_, 1);
v___x_3769_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0___closed__0));
v___x_3770_ = lean_string_dec_eq(v_str_3768_, v___x_3769_);
if (v___x_3770_ == 0)
{
return v___x_3770_;
}
else
{
return v_suppressElabErrors_3742_;
}
}
default: 
{
uint8_t v___x_3771_; 
v___x_3771_ = 0;
return v___x_3771_;
}
}
}
else
{
uint8_t v___x_3772_; 
v___x_3772_ = 0;
return v___x_3772_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_3773_, lean_object* v_x_3774_){
_start:
{
uint8_t v_suppressElabErrors_boxed_3775_; uint8_t v_res_3776_; lean_object* v_r_3777_; 
v_suppressElabErrors_boxed_3775_ = lean_unbox(v_suppressElabErrors_3773_);
v_res_3776_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0(v_suppressElabErrors_boxed_3775_, v_x_3774_);
lean_dec(v_x_3774_);
v_r_3777_ = lean_box(v_res_3776_);
return v_r_3777_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_3778_, lean_object* v_msgData_3779_, uint8_t v_severity_3780_, uint8_t v_isSilent_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_){
_start:
{
lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; uint8_t v___y_3792_; lean_object* v___y_3793_; uint8_t v___y_3794_; lean_object* v_toCold_3795_; lean_object* v___y_3796_; lean_object* v___y_3825_; lean_object* v___y_3826_; lean_object* v___y_3827_; uint8_t v___y_3828_; uint8_t v___y_3829_; uint8_t v___y_3830_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3852_; uint8_t v___y_3853_; lean_object* v___y_3854_; lean_object* v___y_3855_; uint8_t v___y_3856_; uint8_t v___y_3857_; lean_object* v___y_3858_; uint8_t v___y_3862_; uint8_t v___y_3863_; uint8_t v___x_3873_; uint8_t v___y_3875_; uint8_t v___x_3881_; 
v___x_3873_ = 2;
v___x_3881_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3780_, v___x_3873_);
if (v___x_3881_ == 0)
{
v___y_3875_ = v___x_3881_;
goto v___jp_3874_;
}
else
{
uint8_t v___x_3882_; 
lean_inc_ref(v_msgData_3779_);
v___x_3882_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3779_);
if (v___x_3882_ == 0)
{
v___y_3875_ = v___x_3882_;
goto v___jp_3874_;
}
else
{
lean_object* v___x_3883_; lean_object* v___x_3884_; 
lean_dec_ref(v_msgData_3779_);
v___x_3883_ = lean_box(0);
v___x_3884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3884_, 0, v___x_3883_);
return v___x_3884_;
}
}
v___jp_3787_:
{
lean_object* v_currNamespace_3797_; lean_object* v_openDecls_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v_env_3803_; lean_object* v_nextMacroScope_3804_; lean_object* v_ngen_3805_; lean_object* v_auxDeclNGen_3806_; lean_object* v_traceState_3807_; lean_object* v_cache_3808_; lean_object* v_recordedDeps_3809_; lean_object* v_messages_3810_; lean_object* v_infoState_3811_; lean_object* v_snapshotTasks_3812_; lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3823_; 
v_currNamespace_3797_ = lean_ctor_get(v_toCold_3795_, 4);
v_openDecls_3798_ = lean_ctor_get(v_toCold_3795_, 5);
lean_inc(v_openDecls_3798_);
lean_inc(v_currNamespace_3797_);
v___x_3799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3799_, 0, v_currNamespace_3797_);
lean_ctor_set(v___x_3799_, 1, v_openDecls_3798_);
v___x_3800_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3800_, 0, v___x_3799_);
lean_ctor_set(v___x_3800_, 1, v___y_3788_);
lean_inc_ref(v___y_3793_);
lean_inc_ref(v___y_3789_);
v___x_3801_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3801_, 0, v___y_3789_);
lean_ctor_set(v___x_3801_, 1, v___y_3791_);
lean_ctor_set(v___x_3801_, 2, v___y_3790_);
lean_ctor_set(v___x_3801_, 3, v___y_3793_);
lean_ctor_set(v___x_3801_, 4, v___x_3800_);
lean_ctor_set_uint8(v___x_3801_, sizeof(void*)*5, v___y_3794_);
lean_ctor_set_uint8(v___x_3801_, sizeof(void*)*5 + 1, v___y_3792_);
lean_ctor_set_uint8(v___x_3801_, sizeof(void*)*5 + 2, v_isSilent_3781_);
v___x_3802_ = lean_st_ref_take(v___y_3796_);
v_env_3803_ = lean_ctor_get(v___x_3802_, 0);
v_nextMacroScope_3804_ = lean_ctor_get(v___x_3802_, 1);
v_ngen_3805_ = lean_ctor_get(v___x_3802_, 2);
v_auxDeclNGen_3806_ = lean_ctor_get(v___x_3802_, 3);
v_traceState_3807_ = lean_ctor_get(v___x_3802_, 4);
v_cache_3808_ = lean_ctor_get(v___x_3802_, 5);
v_recordedDeps_3809_ = lean_ctor_get(v___x_3802_, 6);
v_messages_3810_ = lean_ctor_get(v___x_3802_, 7);
v_infoState_3811_ = lean_ctor_get(v___x_3802_, 8);
v_snapshotTasks_3812_ = lean_ctor_get(v___x_3802_, 9);
v_isSharedCheck_3823_ = !lean_is_exclusive(v___x_3802_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3814_ = v___x_3802_;
v_isShared_3815_ = v_isSharedCheck_3823_;
goto v_resetjp_3813_;
}
else
{
lean_inc(v_snapshotTasks_3812_);
lean_inc(v_infoState_3811_);
lean_inc(v_messages_3810_);
lean_inc(v_recordedDeps_3809_);
lean_inc(v_cache_3808_);
lean_inc(v_traceState_3807_);
lean_inc(v_auxDeclNGen_3806_);
lean_inc(v_ngen_3805_);
lean_inc(v_nextMacroScope_3804_);
lean_inc(v_env_3803_);
lean_dec(v___x_3802_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3823_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3819_; 
v___x_3816_ = lean_box(0);
v___x_3817_ = l_Lean_MessageLog_add(v___x_3801_, v_messages_3810_);
if (v_isShared_3815_ == 0)
{
lean_ctor_set(v___x_3814_, 7, v___x_3817_);
v___x_3819_ = v___x_3814_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_env_3803_);
lean_ctor_set(v_reuseFailAlloc_3822_, 1, v_nextMacroScope_3804_);
lean_ctor_set(v_reuseFailAlloc_3822_, 2, v_ngen_3805_);
lean_ctor_set(v_reuseFailAlloc_3822_, 3, v_auxDeclNGen_3806_);
lean_ctor_set(v_reuseFailAlloc_3822_, 4, v_traceState_3807_);
lean_ctor_set(v_reuseFailAlloc_3822_, 5, v_cache_3808_);
lean_ctor_set(v_reuseFailAlloc_3822_, 6, v_recordedDeps_3809_);
lean_ctor_set(v_reuseFailAlloc_3822_, 7, v___x_3817_);
lean_ctor_set(v_reuseFailAlloc_3822_, 8, v_infoState_3811_);
lean_ctor_set(v_reuseFailAlloc_3822_, 9, v_snapshotTasks_3812_);
v___x_3819_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
lean_object* v___x_3820_; lean_object* v___x_3821_; 
v___x_3820_ = lean_st_ref_put(v___y_3796_, v___x_3819_);
v___x_3821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3821_, 0, v___x_3816_);
return v___x_3821_;
}
}
}
v___jp_3824_:
{
lean_object* v_fileName_3833_; lean_object* v_fileMap_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v_a_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3850_; 
v_fileName_3833_ = lean_ctor_get(v___y_3831_, 0);
v_fileMap_3834_ = lean_ctor_get(v___y_3831_, 1);
v___x_3835_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3779_);
v___x_3836_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2_spec__5(v___x_3835_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_);
v_a_3837_ = lean_ctor_get(v___x_3836_, 0);
v_isSharedCheck_3850_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3850_ == 0)
{
v___x_3839_ = v___x_3836_;
v_isShared_3840_ = v_isSharedCheck_3850_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_a_3837_);
lean_dec(v___x_3836_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3850_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; 
lean_inc_ref_n(v_fileMap_3834_, 2);
v___x_3841_ = l_Lean_FileMap_toPosition(v_fileMap_3834_, v___y_3827_);
lean_dec(v___y_3827_);
v___x_3842_ = l_Lean_FileMap_toPosition(v_fileMap_3834_, v___y_3832_);
lean_dec(v___y_3832_);
v___x_3843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3843_, 0, v___x_3842_);
v___x_3844_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__19));
if (v___y_3828_ == 0)
{
lean_del_object(v___x_3839_);
lean_dec_ref(v___y_3825_);
v___y_3788_ = v_a_3837_;
v___y_3789_ = v_fileName_3833_;
v___y_3790_ = v___x_3843_;
v___y_3791_ = v___x_3841_;
v___y_3792_ = v___y_3829_;
v___y_3793_ = v___x_3844_;
v___y_3794_ = v___y_3830_;
v_toCold_3795_ = v___y_3826_;
v___y_3796_ = v___y_3785_;
goto v___jp_3787_;
}
else
{
uint8_t v___x_3845_; 
lean_inc(v_a_3837_);
v___x_3845_ = l_Lean_MessageData_hasTag(v___y_3825_, v_a_3837_);
if (v___x_3845_ == 0)
{
lean_object* v___x_3846_; lean_object* v___x_3848_; 
lean_dec_ref_known(v___x_3843_, 1);
lean_dec_ref(v___x_3841_);
lean_dec(v_a_3837_);
v___x_3846_ = lean_box(0);
if (v_isShared_3840_ == 0)
{
lean_ctor_set(v___x_3839_, 0, v___x_3846_);
v___x_3848_ = v___x_3839_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v___x_3846_);
v___x_3848_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
return v___x_3848_;
}
}
else
{
lean_del_object(v___x_3839_);
v___y_3788_ = v_a_3837_;
v___y_3789_ = v_fileName_3833_;
v___y_3790_ = v___x_3843_;
v___y_3791_ = v___x_3841_;
v___y_3792_ = v___y_3829_;
v___y_3793_ = v___x_3844_;
v___y_3794_ = v___y_3830_;
v_toCold_3795_ = v___y_3826_;
v___y_3796_ = v___y_3785_;
goto v___jp_3787_;
}
}
}
}
v___jp_3851_:
{
lean_object* v___x_3859_; 
v___x_3859_ = l_Lean_Syntax_getTailPos_x3f(v___y_3855_, v___y_3857_);
lean_dec(v___y_3855_);
if (lean_obj_tag(v___x_3859_) == 0)
{
lean_inc(v___y_3858_);
v___y_3825_ = v___y_3852_;
v___y_3826_ = v___y_3854_;
v___y_3827_ = v___y_3858_;
v___y_3828_ = v___y_3853_;
v___y_3829_ = v___y_3856_;
v___y_3830_ = v___y_3857_;
v___y_3831_ = v___y_3854_;
v___y_3832_ = v___y_3858_;
goto v___jp_3824_;
}
else
{
lean_object* v_val_3860_; 
v_val_3860_ = lean_ctor_get(v___x_3859_, 0);
lean_inc(v_val_3860_);
lean_dec_ref_known(v___x_3859_, 1);
v___y_3825_ = v___y_3852_;
v___y_3826_ = v___y_3854_;
v___y_3827_ = v___y_3858_;
v___y_3828_ = v___y_3853_;
v___y_3829_ = v___y_3856_;
v___y_3830_ = v___y_3857_;
v___y_3831_ = v___y_3854_;
v___y_3832_ = v_val_3860_;
goto v___jp_3824_;
}
}
v___jp_3861_:
{
lean_object* v_toCold_3864_; lean_object* v_ref_3865_; uint8_t v_suppressElabErrors_3866_; lean_object* v___x_3867_; lean_object* v___f_3868_; lean_object* v_ref_3869_; lean_object* v___x_3870_; 
v_toCold_3864_ = lean_ctor_get(v___y_3784_, 0);
v_ref_3865_ = lean_ctor_get(v___y_3784_, 2);
v_suppressElabErrors_3866_ = lean_ctor_get_uint8(v___y_3784_, sizeof(void*)*3 + 2);
v___x_3867_ = lean_box(v_suppressElabErrors_3866_);
v___f_3868_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3868_, 0, v___x_3867_);
v_ref_3869_ = l_Lean_replaceRef(v_ref_3778_, v_ref_3865_);
v___x_3870_ = l_Lean_Syntax_getPos_x3f(v_ref_3869_, v___y_3862_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v___x_3871_; 
v___x_3871_ = lean_unsigned_to_nat(0u);
v___y_3852_ = v___f_3868_;
v___y_3853_ = v_suppressElabErrors_3866_;
v___y_3854_ = v_toCold_3864_;
v___y_3855_ = v_ref_3869_;
v___y_3856_ = v___y_3863_;
v___y_3857_ = v___y_3862_;
v___y_3858_ = v___x_3871_;
goto v___jp_3851_;
}
else
{
lean_object* v_val_3872_; 
v_val_3872_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_val_3872_);
lean_dec_ref_known(v___x_3870_, 1);
v___y_3852_ = v___f_3868_;
v___y_3853_ = v_suppressElabErrors_3866_;
v___y_3854_ = v_toCold_3864_;
v___y_3855_ = v_ref_3869_;
v___y_3856_ = v___y_3863_;
v___y_3857_ = v___y_3862_;
v___y_3858_ = v_val_3872_;
goto v___jp_3851_;
}
}
v___jp_3874_:
{
uint8_t v___x_3876_; uint8_t v___x_3877_; 
v___x_3876_ = 1;
v___x_3877_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3780_, v___x_3876_);
if (v___x_3877_ == 0)
{
v___y_3862_ = v___y_3875_;
v___y_3863_ = v_severity_3780_;
goto v___jp_3861_;
}
else
{
lean_object* v___x_3878_; lean_object* v___x_3879_; uint8_t v___x_3880_; 
v___x_3878_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3784_);
v___x_3879_ = l_Lean_warningAsError;
v___x_3880_ = l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0(v___x_3878_, v___x_3879_);
lean_dec_ref(v___x_3878_);
if (v___x_3880_ == 0)
{
v___y_3862_ = v___y_3875_;
v___y_3863_ = v_severity_3780_;
goto v___jp_3861_;
}
else
{
v___y_3862_ = v___y_3875_;
v___y_3863_ = v___x_3873_;
goto v___jp_3861_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_3885_, lean_object* v_msgData_3886_, lean_object* v_severity_3887_, lean_object* v_isSilent_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_){
_start:
{
uint8_t v_severity_boxed_3894_; uint8_t v_isSilent_boxed_3895_; lean_object* v_res_3896_; 
v_severity_boxed_3894_ = lean_unbox(v_severity_3887_);
v_isSilent_boxed_3895_ = lean_unbox(v_isSilent_3888_);
v_res_3896_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg(v_ref_3885_, v_msgData_3886_, v_severity_boxed_3894_, v_isSilent_boxed_3895_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_);
lean_dec(v___y_3892_);
lean_dec_ref(v___y_3891_);
lean_dec(v___y_3890_);
lean_dec_ref(v___y_3889_);
lean_dec(v_ref_3885_);
return v_res_3896_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0(lean_object* v_ref_3897_, lean_object* v_msgData_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_){
_start:
{
uint8_t v___x_3907_; uint8_t v___x_3908_; lean_object* v___x_3909_; 
v___x_3907_ = 1;
v___x_3908_ = 0;
v___x_3909_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg(v_ref_3897_, v_msgData_3898_, v___x_3907_, v___x_3908_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_);
return v___x_3909_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0___boxed(lean_object* v_ref_3910_, lean_object* v_msgData_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_){
_start:
{
lean_object* v_res_3920_; 
v_res_3920_ = l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0(v_ref_3910_, v_msgData_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_);
lean_dec(v___y_3918_);
lean_dec_ref(v___y_3917_);
lean_dec(v___y_3916_);
lean_dec_ref(v___y_3915_);
lean_dec(v___y_3914_);
lean_dec_ref(v___y_3913_);
lean_dec_ref(v___y_3912_);
lean_dec(v_ref_3910_);
return v_res_3920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0(lean_object* v_kw_3921_, lean_object* v_what_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_){
_start:
{
lean_object* v___x_3931_; lean_object* v___x_3932_; uint8_t v___x_3933_; 
v___x_3931_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3928_);
v___x_3932_ = l_Lean_Elab_Do_experimental_intrinsic;
v___x_3933_ = l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0(v___x_3931_, v___x_3932_);
lean_dec_ref(v___x_3931_);
if (v___x_3933_ == 0)
{
lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; 
v___x_3934_ = lean_obj_once(&l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1, &l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1_once, _init_l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1);
v___x_3935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3935_, 0, v___x_3934_);
lean_ctor_set(v___x_3935_, 1, v_what_3922_);
v___x_3936_ = lean_obj_once(&l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3, &l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3_once, _init_l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3);
v___x_3937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3935_);
lean_ctor_set(v___x_3937_, 1, v___x_3936_);
v___x_3938_ = l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0(v_kw_3921_, v___x_3937_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_);
return v___x_3938_;
}
else
{
lean_object* v___x_3939_; lean_object* v___x_3940_; 
lean_dec_ref(v_what_3922_);
v___x_3939_ = lean_box(0);
v___x_3940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3940_, 0, v___x_3939_);
return v___x_3940_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0___boxed(lean_object* v_kw_3941_, lean_object* v_what_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_){
_start:
{
lean_object* v_res_3951_; 
v_res_3951_ = l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0(v_kw_3941_, v_what_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
lean_dec(v___y_3945_);
lean_dec_ref(v___y_3944_);
lean_dec_ref(v___y_3943_);
lean_dec(v_kw_3941_);
return v_res_3951_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2___redArg(lean_object* v_msg_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_){
_start:
{
lean_object* v_ref_3958_; lean_object* v___x_3959_; lean_object* v_a_3960_; lean_object* v___x_3962_; uint8_t v_isShared_3963_; uint8_t v_isSharedCheck_3968_; 
v_ref_3958_ = lean_ctor_get(v___y_3955_, 2);
v___x_3959_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2_spec__5(v_msg_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_);
v_a_3960_ = lean_ctor_get(v___x_3959_, 0);
v_isSharedCheck_3968_ = !lean_is_exclusive(v___x_3959_);
if (v_isSharedCheck_3968_ == 0)
{
v___x_3962_ = v___x_3959_;
v_isShared_3963_ = v_isSharedCheck_3968_;
goto v_resetjp_3961_;
}
else
{
lean_inc(v_a_3960_);
lean_dec(v___x_3959_);
v___x_3962_ = lean_box(0);
v_isShared_3963_ = v_isSharedCheck_3968_;
goto v_resetjp_3961_;
}
v_resetjp_3961_:
{
lean_object* v___x_3964_; lean_object* v___x_3966_; 
lean_inc(v_ref_3958_);
v___x_3964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3964_, 0, v_ref_3958_);
lean_ctor_set(v___x_3964_, 1, v_a_3960_);
if (v_isShared_3963_ == 0)
{
lean_ctor_set_tag(v___x_3962_, 1);
lean_ctor_set(v___x_3962_, 0, v___x_3964_);
v___x_3966_ = v___x_3962_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v___x_3964_);
v___x_3966_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
return v___x_3966_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2___redArg___boxed(lean_object* v_msg_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_){
_start:
{
lean_object* v_res_3975_; 
v_res_3975_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2___redArg(v_msg_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_);
lean_dec(v___y_3973_);
lean_dec_ref(v___y_3972_);
lean_dec(v___y_3971_);
lean_dec_ref(v___y_3970_);
return v_res_3975_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg(lean_object* v_ref_3976_, lean_object* v_msg_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_){
_start:
{
lean_object* v_toCold_3986_; lean_object* v_currRecDepth_3987_; lean_object* v_ref_3988_; uint16_t v_optionFlags_3989_; uint8_t v_suppressElabErrors_3990_; uint8_t v_isRecordingDeps_3991_; lean_object* v_ref_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; 
v_toCold_3986_ = lean_ctor_get(v___y_3983_, 0);
v_currRecDepth_3987_ = lean_ctor_get(v___y_3983_, 1);
v_ref_3988_ = lean_ctor_get(v___y_3983_, 2);
v_optionFlags_3989_ = lean_ctor_get_uint16(v___y_3983_, sizeof(void*)*3);
v_suppressElabErrors_3990_ = lean_ctor_get_uint8(v___y_3983_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3991_ = lean_ctor_get_uint8(v___y_3983_, sizeof(void*)*3 + 3);
v_ref_3992_ = l_Lean_replaceRef(v_ref_3976_, v_ref_3988_);
lean_inc(v_currRecDepth_3987_);
lean_inc_ref(v_toCold_3986_);
v___x_3993_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3993_, 0, v_toCold_3986_);
lean_ctor_set(v___x_3993_, 1, v_currRecDepth_3987_);
lean_ctor_set(v___x_3993_, 2, v_ref_3992_);
lean_ctor_set_uint16(v___x_3993_, sizeof(void*)*3, v_optionFlags_3989_);
lean_ctor_set_uint8(v___x_3993_, sizeof(void*)*3 + 2, v_suppressElabErrors_3990_);
lean_ctor_set_uint8(v___x_3993_, sizeof(void*)*3 + 3, v_isRecordingDeps_3991_);
v___x_3994_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2___redArg(v_msg_3977_, v___y_3981_, v___y_3982_, v___x_3993_, v___y_3984_);
lean_dec_ref_known(v___x_3993_, 3);
return v___x_3994_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg___boxed(lean_object* v_ref_3995_, lean_object* v_msg_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_){
_start:
{
lean_object* v_res_4005_; 
v_res_4005_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg(v_ref_3995_, v_msg_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_);
lean_dec(v___y_4003_);
lean_dec_ref(v___y_4002_);
lean_dec(v___y_4001_);
lean_dec_ref(v___y_4000_);
lean_dec(v___y_3999_);
lean_dec_ref(v___y_3998_);
lean_dec_ref(v___y_3997_);
lean_dec(v_ref_3995_);
return v_res_4005_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__1(void){
_start:
{
lean_object* v___x_4007_; lean_object* v___x_4008_; 
v___x_4007_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__0));
v___x_4008_ = l_Lean_stringToMessageData(v___x_4007_);
return v___x_4008_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__9(void){
_start:
{
lean_object* v___x_4032_; lean_object* v___x_4033_; 
v___x_4032_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__8));
v___x_4033_ = l_Lean_mkCIdent(v___x_4032_);
return v___x_4033_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__11(void){
_start:
{
lean_object* v___x_4035_; lean_object* v___x_4036_; 
v___x_4035_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__10));
v___x_4036_ = l_Lean_stringToMessageData(v___x_4035_);
return v___x_4036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion(lean_object* v_stx_4043_, lean_object* v_dec_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_){
_start:
{
lean_object* v___x_4053_; lean_object* v_tk_4054_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; lean_object* v___y_4061_; lean_object* v___y_4062_; lean_object* v___y_4063_; lean_object* v_as_4133_; lean_object* v___y_4134_; lean_object* v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v___y_4139_; lean_object* v___y_4140_; lean_object* v___x_4156_; uint8_t v___x_4157_; 
v___x_4053_ = lean_unsigned_to_nat(0u);
v_tk_4054_ = l_Lean_Syntax_getArg(v_stx_4043_, v___x_4053_);
v___x_4156_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__13));
lean_inc(v_stx_4043_);
v___x_4157_ = l_Lean_Syntax_isOfKind(v_stx_4043_, v___x_4156_);
if (v___x_4157_ == 0)
{
lean_object* v___x_4158_; lean_object* v_a_4159_; lean_object* v___x_4161_; uint8_t v_isShared_4162_; uint8_t v_isSharedCheck_4166_; 
lean_dec(v_tk_4054_);
lean_dec_ref(v_dec_4044_);
lean_dec(v_stx_4043_);
v___x_4158_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg();
v_a_4159_ = lean_ctor_get(v___x_4158_, 0);
v_isSharedCheck_4166_ = !lean_is_exclusive(v___x_4158_);
if (v_isSharedCheck_4166_ == 0)
{
v___x_4161_ = v___x_4158_;
v_isShared_4162_ = v_isSharedCheck_4166_;
goto v_resetjp_4160_;
}
else
{
lean_inc(v_a_4159_);
lean_dec(v___x_4158_);
v___x_4161_ = lean_box(0);
v_isShared_4162_ = v_isSharedCheck_4166_;
goto v_resetjp_4160_;
}
v_resetjp_4160_:
{
lean_object* v___x_4164_; 
if (v_isShared_4162_ == 0)
{
v___x_4164_ = v___x_4161_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4165_, 0, v_a_4159_);
v___x_4164_ = v_reuseFailAlloc_4165_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
return v___x_4164_;
}
}
}
else
{
lean_object* v___x_4167_; lean_object* v_p_4168_; lean_object* v___x_4169_; uint8_t v___x_4170_; 
v___x_4167_ = lean_unsigned_to_nat(1u);
v_p_4168_ = l_Lean_Syntax_getArg(v_stx_4043_, v___x_4167_);
lean_dec(v_stx_4043_);
v___x_4169_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__3));
lean_inc(v_p_4168_);
v___x_4170_ = l_Lean_Syntax_isOfKind(v_p_4168_, v___x_4169_);
if (v___x_4170_ == 0)
{
v_as_4133_ = v_p_4168_;
v___y_4134_ = v_a_4045_;
v___y_4135_ = v_a_4046_;
v___y_4136_ = v_a_4047_;
v___y_4137_ = v_a_4048_;
v___y_4138_ = v_a_4049_;
v___y_4139_ = v_a_4050_;
v___y_4140_ = v_a_4051_;
goto v___jp_4132_;
}
else
{
lean_object* v_ref_4171_; uint8_t v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; 
v_ref_4171_ = lean_ctor_get(v_a_4050_, 2);
v___x_4172_ = 0;
v___x_4173_ = l_Lean_SourceInfo_fromRef(v_ref_4171_, v___x_4172_);
v___x_4174_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__40));
v___x_4175_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__41));
lean_inc(v___x_4173_);
v___x_4176_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4176_, 0, v___x_4173_);
lean_ctor_set(v___x_4176_, 1, v___x_4174_);
v___x_4177_ = l_Lean_Syntax_node2(v___x_4173_, v___x_4175_, v___x_4176_, v_p_4168_);
v_as_4133_ = v___x_4177_;
v___y_4134_ = v_a_4045_;
v___y_4135_ = v_a_4046_;
v___y_4136_ = v_a_4047_;
v___y_4137_ = v_a_4048_;
v___y_4138_ = v_a_4049_;
v___y_4139_ = v_a_4050_;
v___y_4140_ = v_a_4051_;
goto v___jp_4132_;
}
}
v___jp_4055_:
{
lean_object* v___x_4064_; lean_object* v___x_4065_; 
v___x_4064_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__1, &l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__1_once, _init_l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__1);
v___x_4065_ = l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0(v_tk_4054_, v___x_4064_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_);
if (lean_obj_tag(v___x_4065_) == 0)
{
lean_object* v___x_4066_; 
lean_dec_ref_known(v___x_4065_, 1);
v___x_4066_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_4044_, v_tk_4054_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_);
lean_dec(v_tk_4054_);
if (lean_obj_tag(v___x_4066_) == 0)
{
lean_object* v_toCold_4067_; lean_object* v_a_4068_; lean_object* v_ref_4069_; lean_object* v_quotContext_4070_; lean_object* v_currMacroScope_4071_; uint8_t v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; 
v_toCold_4067_ = lean_ctor_get(v___y_4062_, 0);
v_a_4068_ = lean_ctor_get(v___x_4066_, 0);
lean_inc(v_a_4068_);
lean_dec_ref_known(v___x_4066_, 1);
v_ref_4069_ = lean_ctor_get(v___y_4062_, 2);
v_quotContext_4070_ = lean_ctor_get(v_toCold_4067_, 8);
v_currMacroScope_4071_ = lean_ctor_get(v_toCold_4067_, 9);
v___x_4072_ = 0;
v___x_4073_ = l_Lean_SourceInfo_fromRef(v_ref_4069_, v___x_4072_);
v___x_4074_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__1));
v___x_4075_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__2));
lean_inc_n(v___x_4073_, 9);
v___x_4076_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4076_, 0, v___x_4073_);
lean_ctor_set(v___x_4076_, 1, v___x_4074_);
v___x_4077_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__3));
v___x_4078_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__3));
v___x_4079_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4079_, 0, v___x_4073_);
lean_ctor_set(v___x_4079_, 1, v___x_4078_);
v___x_4080_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__2));
v___x_4081_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_expandDefContract___closed__5, &l_Lean_Elab_Tactic_Do_expandDefContract___closed__5_once, _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__5);
v___x_4082_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__29));
lean_inc_n(v_currMacroScope_4071_, 2);
lean_inc_n(v_quotContext_4070_, 2);
v___x_4083_ = l_Lean_addMacroScope(v_quotContext_4070_, v___x_4082_, v_currMacroScope_4071_);
v___x_4084_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__4));
v___x_4085_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4085_, 0, v___x_4073_);
lean_ctor_set(v___x_4085_, 1, v___x_4081_);
lean_ctor_set(v___x_4085_, 2, v___x_4083_);
lean_ctor_set(v___x_4085_, 3, v___x_4084_);
v___x_4086_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_expandDefContract___closed__7, &l_Lean_Elab_Tactic_Do_expandDefContract___closed__7_once, _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__7);
v___x_4087_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__27));
v___x_4088_ = l_Lean_addMacroScope(v_quotContext_4070_, v___x_4087_, v_currMacroScope_4071_);
v___x_4089_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__5));
v___x_4090_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4090_, 0, v___x_4073_);
lean_ctor_set(v___x_4090_, 1, v___x_4086_);
lean_ctor_set(v___x_4090_, 2, v___x_4088_);
lean_ctor_set(v___x_4090_, 3, v___x_4089_);
v___x_4091_ = l_Lean_Syntax_node2(v___x_4073_, v___x_4080_, v___x_4085_, v___x_4090_);
v___x_4092_ = l_Lean_Syntax_node2(v___x_4073_, v___x_4077_, v___x_4079_, v___x_4091_);
v___x_4093_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__0));
v___x_4094_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4094_, 0, v___x_4073_);
lean_ctor_set(v___x_4094_, 1, v___x_4093_);
v___x_4095_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__7));
v___x_4096_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__9, &l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__9_once, _init_l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__9);
v___x_4097_ = l_Lean_Syntax_node1(v___x_4073_, v___x_4080_, v___y_4056_);
v___x_4098_ = l_Lean_Syntax_node2(v___x_4073_, v___x_4095_, v___x_4096_, v___x_4097_);
v___x_4099_ = l_Lean_Syntax_node4(v___x_4073_, v___x_4075_, v___x_4076_, v___x_4092_, v___x_4094_, v___x_4098_);
v___x_4100_ = l_Lean_Elab_Do_mkPUnit___redArg(v___y_4057_);
if (lean_obj_tag(v___x_4100_) == 0)
{
lean_object* v_a_4101_; lean_object* v___x_4102_; 
v_a_4101_ = lean_ctor_get(v___x_4100_, 0);
lean_inc(v_a_4101_);
lean_dec_ref_known(v___x_4100_, 1);
v___x_4102_ = l_Lean_Elab_Do_mkMonadApp(v_a_4101_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_);
if (lean_obj_tag(v___x_4102_) == 0)
{
lean_object* v_a_4103_; lean_object* v___x_4105_; uint8_t v_isShared_4106_; uint8_t v_isSharedCheck_4115_; 
v_a_4103_ = lean_ctor_get(v___x_4102_, 0);
v_isSharedCheck_4115_ = !lean_is_exclusive(v___x_4102_);
if (v_isSharedCheck_4115_ == 0)
{
v___x_4105_ = v___x_4102_;
v_isShared_4106_ = v_isSharedCheck_4115_;
goto v_resetjp_4104_;
}
else
{
lean_inc(v_a_4103_);
lean_dec(v___x_4102_);
v___x_4105_ = lean_box(0);
v_isShared_4106_ = v_isSharedCheck_4115_;
goto v_resetjp_4104_;
}
v_resetjp_4104_:
{
lean_object* v___x_4108_; 
if (v_isShared_4106_ == 0)
{
lean_ctor_set_tag(v___x_4105_, 1);
v___x_4108_ = v___x_4105_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v_a_4103_);
v___x_4108_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4107_;
}
v_reusejp_4107_:
{
uint8_t v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; 
v___x_4109_ = 1;
v___x_4110_ = lean_box(0);
v___x_4111_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_4099_, v___x_4108_, v___x_4109_, v___x_4109_, v___x_4110_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_);
if (lean_obj_tag(v___x_4111_) == 0)
{
lean_object* v_a_4112_; lean_object* v___x_4113_; 
v_a_4112_ = lean_ctor_get(v___x_4111_, 0);
lean_inc(v_a_4112_);
lean_dec_ref_known(v___x_4111_, 1);
v___x_4113_ = l_Lean_Elab_Do_DoElemCont_mkBindUnlessPure(v_a_4068_, v_a_4112_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_);
return v___x_4113_;
}
else
{
lean_dec(v_a_4068_);
return v___x_4111_;
}
}
}
}
else
{
lean_dec(v___x_4099_);
lean_dec(v_a_4068_);
return v___x_4102_;
}
}
else
{
lean_dec(v___x_4099_);
lean_dec(v_a_4068_);
return v___x_4100_;
}
}
else
{
lean_object* v_a_4116_; lean_object* v___x_4118_; uint8_t v_isShared_4119_; uint8_t v_isSharedCheck_4123_; 
lean_dec(v___y_4056_);
v_a_4116_ = lean_ctor_get(v___x_4066_, 0);
v_isSharedCheck_4123_ = !lean_is_exclusive(v___x_4066_);
if (v_isSharedCheck_4123_ == 0)
{
v___x_4118_ = v___x_4066_;
v_isShared_4119_ = v_isSharedCheck_4123_;
goto v_resetjp_4117_;
}
else
{
lean_inc(v_a_4116_);
lean_dec(v___x_4066_);
v___x_4118_ = lean_box(0);
v_isShared_4119_ = v_isSharedCheck_4123_;
goto v_resetjp_4117_;
}
v_resetjp_4117_:
{
lean_object* v___x_4121_; 
if (v_isShared_4119_ == 0)
{
v___x_4121_ = v___x_4118_;
goto v_reusejp_4120_;
}
else
{
lean_object* v_reuseFailAlloc_4122_; 
v_reuseFailAlloc_4122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4122_, 0, v_a_4116_);
v___x_4121_ = v_reuseFailAlloc_4122_;
goto v_reusejp_4120_;
}
v_reusejp_4120_:
{
return v___x_4121_;
}
}
}
}
else
{
lean_object* v_a_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4131_; 
lean_dec(v___y_4056_);
lean_dec(v_tk_4054_);
lean_dec_ref(v_dec_4044_);
v_a_4124_ = lean_ctor_get(v___x_4065_, 0);
v_isSharedCheck_4131_ = !lean_is_exclusive(v___x_4065_);
if (v_isSharedCheck_4131_ == 0)
{
v___x_4126_ = v___x_4065_;
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
else
{
lean_inc(v_a_4124_);
lean_dec(v___x_4065_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
lean_object* v___x_4129_; 
if (v_isShared_4127_ == 0)
{
v___x_4129_ = v___x_4126_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4130_; 
v_reuseFailAlloc_4130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4130_, 0, v_a_4124_);
v___x_4129_ = v_reuseFailAlloc_4130_;
goto v_reusejp_4128_;
}
v_reusejp_4128_:
{
return v___x_4129_;
}
}
}
}
v___jp_4132_:
{
lean_object* v___x_4141_; lean_object* v_env_4142_; lean_object* v___x_4143_; uint8_t v___x_4144_; uint8_t v___x_4145_; 
v___x_4141_ = lean_st_ref_get(v___y_4140_);
v_env_4142_ = lean_ctor_get(v___x_4141_, 0);
lean_inc_ref(v_env_4142_);
lean_dec(v___x_4141_);
v___x_4143_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__8));
v___x_4144_ = 1;
v___x_4145_ = l_Lean_Environment_contains(v_env_4142_, v___x_4143_, v___x_4144_);
if (v___x_4145_ == 0)
{
lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v_a_4148_; lean_object* v___x_4150_; uint8_t v_isShared_4151_; uint8_t v_isSharedCheck_4155_; 
lean_dec(v_as_4133_);
lean_dec_ref(v_dec_4044_);
v___x_4146_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__11, &l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__11_once, _init_l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__11);
v___x_4147_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg(v_tk_4054_, v___x_4146_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_);
lean_dec(v_tk_4054_);
v_a_4148_ = lean_ctor_get(v___x_4147_, 0);
v_isSharedCheck_4155_ = !lean_is_exclusive(v___x_4147_);
if (v_isSharedCheck_4155_ == 0)
{
v___x_4150_ = v___x_4147_;
v_isShared_4151_ = v_isSharedCheck_4155_;
goto v_resetjp_4149_;
}
else
{
lean_inc(v_a_4148_);
lean_dec(v___x_4147_);
v___x_4150_ = lean_box(0);
v_isShared_4151_ = v_isSharedCheck_4155_;
goto v_resetjp_4149_;
}
v_resetjp_4149_:
{
lean_object* v___x_4153_; 
if (v_isShared_4151_ == 0)
{
v___x_4153_ = v___x_4150_;
goto v_reusejp_4152_;
}
else
{
lean_object* v_reuseFailAlloc_4154_; 
v_reuseFailAlloc_4154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4154_, 0, v_a_4148_);
v___x_4153_ = v_reuseFailAlloc_4154_;
goto v_reusejp_4152_;
}
v_reusejp_4152_:
{
return v___x_4153_;
}
}
}
else
{
v___y_4056_ = v_as_4133_;
v___y_4057_ = v___y_4134_;
v___y_4058_ = v___y_4135_;
v___y_4059_ = v___y_4136_;
v___y_4060_ = v___y_4137_;
v___y_4061_ = v___y_4138_;
v___y_4062_ = v___y_4139_;
v___y_4063_ = v___y_4140_;
goto v___jp_4055_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___boxed(lean_object* v_stx_4178_, lean_object* v_dec_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_){
_start:
{
lean_object* v_res_4188_; 
v_res_4188_ = l_Lean_Elab_Tactic_Do_elabDoAssertion(v_stx_4178_, v_dec_4179_, v_a_4180_, v_a_4181_, v_a_4182_, v_a_4183_, v_a_4184_, v_a_4185_, v_a_4186_);
lean_dec(v_a_4186_);
lean_dec_ref(v_a_4185_);
lean_dec(v_a_4184_);
lean_dec_ref(v_a_4183_);
lean_dec(v_a_4182_);
lean_dec_ref(v_a_4181_);
lean_dec_ref(v_a_4180_);
return v_res_4188_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1(lean_object* v_00_u03b1_4189_, lean_object* v_ref_4190_, lean_object* v_msg_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_){
_start:
{
lean_object* v___x_4200_; 
v___x_4200_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg(v_ref_4190_, v_msg_4191_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_);
return v___x_4200_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___boxed(lean_object* v_00_u03b1_4201_, lean_object* v_ref_4202_, lean_object* v_msg_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_){
_start:
{
lean_object* v_res_4212_; 
v_res_4212_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1(v_00_u03b1_4201_, v_ref_4202_, v_msg_4203_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_);
lean_dec(v___y_4210_);
lean_dec_ref(v___y_4209_);
lean_dec(v___y_4208_);
lean_dec_ref(v___y_4207_);
lean_dec(v___y_4206_);
lean_dec_ref(v___y_4205_);
lean_dec_ref(v___y_4204_);
lean_dec(v_ref_4202_);
return v_res_4212_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2(lean_object* v_00_u03b1_4213_, lean_object* v_msg_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_){
_start:
{
lean_object* v___x_4223_; 
v___x_4223_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2___redArg(v_msg_4214_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_);
return v___x_4223_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2___boxed(lean_object* v_00_u03b1_4224_, lean_object* v_msg_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_){
_start:
{
lean_object* v_res_4234_; 
v_res_4234_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2(v_00_u03b1_4224_, v_msg_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_);
lean_dec(v___y_4232_);
lean_dec_ref(v___y_4231_);
lean_dec(v___y_4230_);
lean_dec_ref(v___y_4229_);
lean_dec(v___y_4228_);
lean_dec_ref(v___y_4227_);
lean_dec_ref(v___y_4226_);
return v_res_4234_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2(lean_object* v_ref_4235_, lean_object* v_msgData_4236_, uint8_t v_severity_4237_, uint8_t v_isSilent_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_){
_start:
{
lean_object* v___x_4247_; 
v___x_4247_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg(v_ref_4235_, v_msgData_4236_, v_severity_4237_, v_isSilent_4238_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_);
return v___x_4247_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___boxed(lean_object* v_ref_4248_, lean_object* v_msgData_4249_, lean_object* v_severity_4250_, lean_object* v_isSilent_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_){
_start:
{
uint8_t v_severity_boxed_4260_; uint8_t v_isSilent_boxed_4261_; lean_object* v_res_4262_; 
v_severity_boxed_4260_ = lean_unbox(v_severity_4250_);
v_isSilent_boxed_4261_ = lean_unbox(v_isSilent_4251_);
v_res_4262_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2(v_ref_4248_, v_msgData_4249_, v_severity_boxed_4260_, v_isSilent_boxed_4261_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
lean_dec(v___y_4258_);
lean_dec_ref(v___y_4257_);
lean_dec(v___y_4256_);
lean_dec_ref(v___y_4255_);
lean_dec(v___y_4254_);
lean_dec_ref(v___y_4253_);
lean_dec_ref(v___y_4252_);
lean_dec(v_ref_4248_);
return v_res_4262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1(){
_start:
{
lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; 
v___x_4271_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4272_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__13));
v___x_4273_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___closed__1));
v___x_4274_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___boxed), 10, 0);
v___x_4275_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4271_, v___x_4272_, v___x_4273_, v___x_4274_);
return v___x_4275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___boxed(lean_object* v_a_4276_){
_start:
{
lean_object* v_res_4277_; 
v_res_4277_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1();
return v_res_4277_;
}
}
lean_object* runtime_initialize_Std_Tactic_Do_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Std_WP(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Do_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_Extension(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
lean_object* runtime_initialize_Init_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Interactive(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Contract(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Tactic_Do_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_WP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Do_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Interactive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Term(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Do(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_Contract(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_Do_Syntax(uint8_t builtin);
lean_object* initialize_Std_WP(uint8_t builtin);
lean_object* initialize_Lean_Elab_Util(uint8_t builtin);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Lean_Elab_Do_Basic(uint8_t builtin);
lean_object* initialize_Lean_DocString_Extension(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
lean_object* initialize_Lean_Parser_Command(uint8_t builtin);
lean_object* initialize_Lean_Parser_Term(uint8_t builtin);
lean_object* initialize_Lean_Parser_Do(uint8_t builtin);
lean_object* initialize_Init_Syntax(uint8_t builtin);
lean_object* initialize_Init_Grind_Interactive(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_Contract(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_Do_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_WP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Do_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Interactive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Contract(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_Contract(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_Contract(builtin);
}
#ifdef __cplusplus
}
#endif
