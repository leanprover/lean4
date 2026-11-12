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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ImportedConsts_empty___redArg();
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
static const lean_array_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__4;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__5;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__6;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 32, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 1, 1, 1, 0, 1),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 1, 1, 0, 0),LEAN_SCALAR_PTR_LITERAL(0, 1, 1, 1, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__8;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__9;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__10;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__11;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__12;
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
lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v_specTac_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; size_t v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v_a_869_; lean_object* v_a_870_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; size_t v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v_post_985_; lean_object* v___y_986_; lean_object* v_ref_987_; lean_object* v___y_988_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; size_t v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1037_; lean_object* v_post_1038_; lean_object* v___y_1039_; lean_object* v___y_1040_; lean_object* v___x_1042_; lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; size_t v___y_1051_; lean_object* v___y_1052_; uint8_t v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; lean_object* v___y_1057_; lean_object* v___y_1058_; lean_object* v___y_1059_; lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v_pre_1062_; lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1131_; size_t v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1134_; uint8_t v___y_1135_; lean_object* v___y_1136_; lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1185_; uint8_t v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1194_; lean_object* v___y_1195_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v_decl_1207_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1268_; lean_object* v___y_1269_; lean_object* v___y_1270_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___x_1360_; uint8_t v___x_1361_; 
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
lean_inc_ref_n(v___y_632_, 30);
lean_inc_ref_n(v___y_636_, 32);
v___x_666_ = l_Lean_Name_mkStr4(v___y_636_, v___y_632_, v___x_664_, v___x_665_);
v___x_667_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__1));
v___x_668_ = l_Lean_Name_mkStr4(v___y_636_, v___y_632_, v___x_664_, v___x_667_);
lean_inc_n(v_a_659_, 76);
v___x_669_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_669_, 0, v_a_659_);
lean_ctor_set(v___x_669_, 1, v___x_667_);
v___x_670_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__2));
v___x_671_ = l_Lean_Name_mkStr4(v___y_636_, v___y_632_, v___x_664_, v___x_670_);
v___x_672_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__3));
v___x_673_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_673_, 0, v_a_659_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
v___x_674_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_expandDefContract___closed__5, &l_Lean_Elab_Tactic_Do_expandDefContract___closed__5_once, _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__5);
lean_inc_ref(v___y_635_);
lean_inc_ref(v___y_644_);
v___x_675_ = l_Lean_Name_mkStr2(v___y_644_, v___y_635_);
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
lean_inc_ref(v___y_646_);
v___x_682_ = l_Lean_Name_mkStr2(v___y_636_, v___y_646_);
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
lean_inc_n(v___y_640_, 17);
v___x_687_ = l_Lean_Syntax_node2(v_a_659_, v___y_640_, v___x_680_, v___x_686_);
v___x_688_ = l_Lean_Syntax_node2(v_a_659_, v___x_671_, v___x_673_, v___x_687_);
v___x_689_ = l_Lean_Syntax_node2(v_a_659_, v___x_668_, v___x_669_, v___x_688_);
v___x_690_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_690_, 0, v_a_659_);
lean_ctor_set(v___x_690_, 1, v___x_665_);
v___x_691_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__8));
v___x_692_ = l_Lean_Name_mkStr4(v___y_636_, v___y_632_, v___x_664_, v___x_691_);
v___x_693_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__9));
v___x_694_ = l_Lean_Name_mkStr4(v___y_636_, v___y_632_, v___x_664_, v___x_693_);
lean_inc_ref(v___y_642_);
v___x_695_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_695_, 0, v_a_659_);
lean_ctor_set(v___x_695_, 1, v___y_640_);
lean_ctor_set(v___x_695_, 2, v___y_642_);
v___x_696_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__10));
lean_inc_ref_n(v___y_648_, 4);
v___x_697_ = l_Lean_Name_mkStr4(v___y_636_, v___y_632_, v___y_648_, v___x_696_);
v___x_698_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__11));
v___x_699_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_699_, 0, v_a_659_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
v___x_700_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__12));
v___x_701_ = l_Lean_Name_mkStr4(v___y_636_, v___y_632_, v___y_648_, v___x_700_);
v___x_702_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__13));
v___x_703_ = l_Lean_Name_mkStr4(v___y_636_, v___y_632_, v___y_648_, v___x_702_);
lean_inc_ref_n(v___x_695_, 24);
v___x_704_ = l_Lean_Syntax_node1(v_a_659_, v___x_703_, v___x_695_);
v___x_705_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__14));
lean_inc_ref_n(v___y_651_, 2);
v___x_706_ = l_Lean_Name_mkStr4(v___y_636_, v___y_632_, v___x_705_, v___y_651_);
v___x_707_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_707_, 0, v_a_659_);
lean_ctor_set(v___x_707_, 1, v___y_651_);
v___x_708_ = l_Lean_Syntax_node2(v_a_659_, v___x_706_, v___x_707_, v___x_695_);
v___x_709_ = l_Lean_Syntax_node2(v_a_659_, v___x_701_, v___x_704_, v___x_708_);
v___x_710_ = l_Lean_Syntax_node1(v_a_659_, v___y_640_, v___x_709_);
v___x_711_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__15));
v___x_712_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_712_, 0, v_a_659_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
lean_inc_ref(v___x_712_);
v___x_713_ = l_Lean_Syntax_node3(v_a_659_, v___x_697_, v___x_699_, v___x_710_, v___x_712_);
v___x_714_ = l_Lean_Syntax_node1(v_a_659_, v___y_640_, v___x_713_);
v___x_715_ = l_Lean_Syntax_node7(v_a_659_, v___x_694_, v___x_695_, v___x_714_, v___x_695_, v___x_695_, v___x_695_, v___x_695_, v___x_695_);
v___x_716_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__16));
v___x_717_ = l_Lean_Name_mkStr4(v___y_636_, v___y_632_, v___x_664_, v___x_716_);
v___x_718_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_718_, 0, v_a_659_);
lean_ctor_set(v___x_718_, 1, v___x_716_);
v___x_719_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__17));
v___x_720_ = l_Lean_Name_mkStr4(v___y_636_, v___y_632_, v___x_664_, v___x_719_);
v___x_721_ = lean_mk_empty_array_with_capacity(v___y_638_);
lean_inc_n(v___y_643_, 2);
v___x_722_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_722_, 0, v___y_643_);
lean_ctor_set(v___x_722_, 1, v___y_640_);
lean_ctor_set(v___x_722_, 2, v___x_721_);
v___x_723_ = lean_array_push(v___y_637_, v___y_641_);
v___x_724_ = lean_array_push(v___x_723_, v___x_722_);
v___x_725_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_725_, 0, v___y_643_);
lean_ctor_set(v___x_725_, 1, v___x_720_);
lean_ctor_set(v___x_725_, 2, v___x_724_);
v___x_726_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__18));
v___x_727_ = l_Lean_Name_mkStr4(v___y_636_, v___y_632_, v___x_664_, v___x_726_);
v___x_728_ = l_Array_append___redArg(v___y_642_, v___y_634_);
lean_dec_ref(v___y_634_);
v___x_729_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_729_, 0, v_a_659_);
lean_ctor_set(v___x_729_, 1, v___y_640_);
lean_ctor_set(v___x_729_, 2, v___x_728_);
v___x_730_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__19));
v___x_731_ = l_Lean_Name_mkStr4(v___y_636_, v___y_632_, v___y_648_, v___x_730_);
v___x_732_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__20));
v___x_733_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_733_, 0, v_a_659_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
v___x_734_ = l_Lean_Syntax_node2(v_a_659_, v___x_731_, v___x_733_, v___y_645_);
v___x_735_ = l_Lean_Syntax_node2(v_a_659_, v___x_727_, v___x_729_, v___x_734_);
v___x_736_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__1));
v___x_737_ = l_Lean_Name_mkStr4(v___y_636_, v___y_632_, v___x_664_, v___x_736_);
v___x_738_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__21));
v___x_739_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_739_, 0, v_a_659_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
v___x_740_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__22));
v___x_741_ = l_Lean_Name_mkStr4(v___y_636_, v___y_632_, v___y_648_, v___x_740_);
v___x_742_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__23));
v___x_743_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_743_, 0, v_a_659_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v___x_744_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__22));
v___x_745_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__24));
v___x_746_ = l_Lean_Name_mkStr4(v___y_636_, v___y_632_, v___x_744_, v___x_745_);
v___x_747_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__25));
v___x_748_ = l_Lean_Name_mkStr4(v___y_636_, v___y_632_, v___x_744_, v___x_747_);
v___x_749_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__26));
v___x_750_ = l_Lean_Name_mkStr4(v___y_636_, v___y_632_, v___x_744_, v___x_749_);
v___x_751_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_751_, 0, v_a_659_);
lean_ctor_set(v___x_751_, 1, v___x_749_);
v___x_752_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__27));
v___x_753_ = l_Lean_Name_mkStr4(v___y_636_, v___y_632_, v___x_744_, v___x_752_);
v___x_754_ = l_Lean_Syntax_node1(v_a_659_, v___x_753_, v___x_695_);
v___x_755_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__28));
v___x_756_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_756_, 0, v_a_659_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
v___x_757_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__29));
v___x_758_ = l_Lean_Name_mkStr4(v___y_636_, v___y_632_, v___x_744_, v___x_757_);
v___x_759_ = l_Lean_Syntax_node3(v_a_659_, v___x_758_, v___x_695_, v___x_695_, v___y_649_);
v___x_760_ = l_Lean_Syntax_node1(v_a_659_, v___y_640_, v___x_759_);
v___x_761_ = l_Lean_Syntax_node3(v_a_659_, v___y_640_, v___x_756_, v___x_760_, v___x_712_);
v___x_762_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__30));
v___x_763_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_763_, 0, v_a_659_);
lean_ctor_set(v___x_763_, 1, v___x_762_);
v___x_764_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__31));
v___x_765_ = l_Lean_Name_mkStr4(v___y_636_, v___y_632_, v___x_744_, v___x_764_);
v___x_766_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__32));
v___x_767_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__12));
v___x_768_ = l_Lean_Name_mkStr5(v___y_636_, v___y_632_, v___x_744_, v___x_766_, v___x_767_);
v___x_769_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__16));
v___x_770_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_770_, 0, v_a_659_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
v___x_771_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__33));
v___x_772_ = l_Lean_Name_mkStr5(v___y_636_, v___y_632_, v___x_744_, v___x_766_, v___x_771_);
v___x_773_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__34));
v___x_774_ = l_Lean_Name_mkStr5(v___y_636_, v___y_632_, v___x_744_, v___x_766_, v___x_773_);
v___x_775_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__35));
v___x_776_ = l_Lean_Name_mkStr5(v___y_636_, v___y_632_, v___x_744_, v___x_766_, v___x_775_);
v___x_777_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__36));
v___x_778_ = l_Lean_Name_mkStr5(v___y_636_, v___y_632_, v___x_744_, v___x_766_, v___x_777_);
v___x_779_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__37));
v___x_780_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_780_, 0, v_a_659_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
v___x_781_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__38));
v___x_782_ = l_Lean_Name_mkStr5(v___y_636_, v___y_632_, v___x_744_, v___x_766_, v___x_781_);
v___x_783_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_783_, 0, v_a_659_);
lean_ctor_set(v___x_783_, 1, v___x_781_);
v___x_784_ = l_Lean_Syntax_node4(v_a_659_, v___x_782_, v___x_783_, v___x_695_, v___x_695_, v___x_695_);
lean_inc(v___x_776_);
v___x_785_ = l_Lean_Syntax_node2(v_a_659_, v___x_776_, v___x_784_, v___x_695_);
v___x_786_ = l_Lean_Syntax_node1(v_a_659_, v___y_640_, v___x_785_);
lean_inc(v___x_774_);
v___x_787_ = l_Lean_Syntax_node1(v_a_659_, v___x_774_, v___x_786_);
lean_inc(v___x_772_);
v___x_788_ = l_Lean_Syntax_node1(v_a_659_, v___x_772_, v___x_787_);
v___x_789_ = l_Lean_Syntax_node2(v_a_659_, v___x_778_, v___x_780_, v___x_788_);
v___x_790_ = l_Lean_Syntax_node2(v_a_659_, v___x_776_, v___x_789_, v___x_695_);
v___x_791_ = l_Lean_Syntax_node1(v_a_659_, v___y_640_, v___x_790_);
v___x_792_ = l_Lean_Syntax_node1(v_a_659_, v___x_774_, v___x_791_);
v___x_793_ = l_Lean_Syntax_node1(v_a_659_, v___x_772_, v___x_792_);
v___x_794_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__42));
v___x_795_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_795_, 0, v_a_659_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
v___x_796_ = l_Lean_Syntax_node3(v_a_659_, v___x_768_, v___x_770_, v___x_793_, v___x_795_);
v___x_797_ = l_Lean_Syntax_node1(v_a_659_, v___x_765_, v___x_796_);
v___x_798_ = l_Lean_Syntax_node2(v_a_659_, v___y_640_, v___x_763_, v___x_797_);
v___x_799_ = l_Lean_Syntax_node8(v_a_659_, v___x_750_, v___x_751_, v___x_754_, v___x_761_, v___x_695_, v___x_695_, v___x_695_, v___x_695_, v___x_798_);
v___x_800_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__39));
v___x_801_ = l_Lean_Name_mkStr4(v___y_636_, v___y_632_, v___x_744_, v___x_800_);
v___x_802_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_802_, 0, v_a_659_);
lean_ctor_set(v___x_802_, 1, v___x_800_);
v___x_803_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__41));
v___x_804_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__42));
v___x_805_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_805_, 0, v_a_659_);
lean_ctor_set(v___x_805_, 1, v___x_804_);
v___x_806_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__43));
v___x_807_ = l_Lean_Name_mkStr4(v___y_636_, v___y_632_, v___x_744_, v___x_806_);
v___x_808_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_808_, 0, v_a_659_);
lean_ctor_set(v___x_808_, 1, v___x_806_);
v___x_809_ = l_Lean_Syntax_node1(v_a_659_, v___x_807_, v___x_808_);
v___x_810_ = l_Lean_Syntax_node1(v_a_659_, v___y_640_, v___x_809_);
lean_inc_n(v___x_748_, 2);
v___x_811_ = l_Lean_Syntax_node1(v_a_659_, v___x_748_, v___x_810_);
lean_inc_n(v___x_746_, 2);
v___x_812_ = l_Lean_Syntax_node1(v_a_659_, v___x_746_, v___x_811_);
lean_inc_ref(v___x_805_);
v___x_813_ = l_Lean_Syntax_node2(v_a_659_, v___x_803_, v___x_805_, v___x_812_);
v___x_814_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__44));
v___x_815_ = l_Lean_Name_mkStr4(v___y_636_, v___y_632_, v___x_744_, v___x_814_);
v___x_816_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_816_, 0, v_a_659_);
lean_ctor_set(v___x_816_, 1, v___x_814_);
v___x_817_ = l_Lean_Syntax_node1(v_a_659_, v___y_640_, v___y_650_);
v___x_818_ = l_Lean_Syntax_node2(v_a_659_, v___x_815_, v___x_816_, v___x_817_);
v___x_819_ = l_Lean_Syntax_node1(v_a_659_, v___y_640_, v___x_818_);
v___x_820_ = l_Lean_Syntax_node1(v_a_659_, v___x_748_, v___x_819_);
v___x_821_ = l_Lean_Syntax_node1(v_a_659_, v___x_746_, v___x_820_);
v___x_822_ = l_Lean_Syntax_node2(v_a_659_, v___x_803_, v___x_805_, v___x_821_);
v___x_823_ = l_Lean_Syntax_node2(v_a_659_, v___y_640_, v___x_813_, v___x_822_);
v___x_824_ = l_Lean_Syntax_node2(v_a_659_, v___x_801_, v___x_802_, v___x_823_);
v___x_825_ = l_Lean_Syntax_node5(v_a_659_, v___y_640_, v___x_799_, v___x_695_, v_specTac_652_, v___x_695_, v___x_824_);
v___x_826_ = l_Lean_Syntax_node1(v_a_659_, v___x_748_, v___x_825_);
v___x_827_ = l_Lean_Syntax_node1(v_a_659_, v___x_746_, v___x_826_);
v___x_828_ = l_Lean_Syntax_node2(v_a_659_, v___x_741_, v___x_743_, v___x_827_);
v___x_829_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__45));
v___x_830_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__46));
v___x_831_ = l_Lean_Name_mkStr4(v___y_636_, v___y_632_, v___x_829_, v___x_830_);
v___x_832_ = l_Lean_Syntax_node2(v_a_659_, v___x_831_, v___x_695_, v___x_695_);
v___x_833_ = l_Lean_Syntax_node4(v_a_659_, v___x_737_, v___x_739_, v___x_828_, v___x_832_, v___x_695_);
v___x_834_ = l_Lean_Syntax_node4(v_a_659_, v___x_717_, v___x_718_, v___x_725_, v___x_735_, v___x_833_);
v___x_835_ = l_Lean_Syntax_node2(v_a_659_, v___x_692_, v___x_715_, v___x_834_);
v___x_836_ = l_Lean_Syntax_node3(v_a_659_, v___x_666_, v___x_689_, v___x_690_, v___x_835_);
v___x_837_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice(v___y_633_);
lean_dec(v___y_633_);
v___x_838_ = lean_mk_empty_array_with_capacity(v___y_647_);
v___x_839_ = lean_array_push(v___x_838_, v___x_837_);
v___x_840_ = lean_array_push(v___x_839_, v___y_639_);
v___x_841_ = lean_array_push(v___x_840_, v___x_836_);
v___x_842_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_842_, 0, v___y_643_);
lean_ctor_set(v___x_842_, 1, v___y_640_);
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
v___x_871_ = l_Lean_Elab_Tactic_Do_expandDefContract___lam__0(v___y_859_, v___y_861_, v_a_870_);
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
v___x_882_ = lean_mk_empty_array_with_capacity(v___y_848_);
lean_inc_ref(v___x_882_);
v___x_883_ = lean_array_push(v___x_882_, v___x_881_);
v___x_884_ = lean_array_push(v___x_883_, v_a_869_);
v___x_885_ = lean_box(2);
v___x_886_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
lean_ctor_set(v___x_886_, 1, v___x_880_);
lean_ctor_set(v___x_886_, 2, v___x_884_);
v___x_887_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__50));
lean_inc_ref(v___y_849_);
lean_inc_ref(v___y_863_);
v___x_888_ = l_Lean_Name_mkStr3(v___y_863_, v___y_849_, v___x_887_);
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
v_sz_899_ = lean_array_size(v___y_862_);
v___x_900_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__1(v_sz_899_, v___y_855_, v___y_862_);
v___x_901_ = l_Array_append___redArg(v___x_895_, v___x_900_);
lean_dec_ref(v___x_900_);
v___x_902_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_902_, 0, v_a_872_);
lean_ctor_set(v___x_902_, 1, v___x_894_);
lean_ctor_set(v___x_902_, 2, v___x_901_);
lean_inc(v___y_866_);
v___x_903_ = l_Lean_Syntax_node2(v_a_872_, v___x_898_, v___y_866_, v___x_902_);
v___x_904_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__54));
v___x_905_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_905_, 0, v_a_872_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___x_906_ = lean_unsigned_to_nat(10u);
v___x_907_ = lean_mk_empty_array_with_capacity(v___x_906_);
lean_inc_ref(v___x_891_);
v___x_908_ = lean_array_push(v___x_907_, v___x_891_);
v___x_909_ = lean_array_push(v___x_908_, v___y_856_);
lean_inc_ref(v___x_893_);
v___x_910_ = lean_array_push(v___x_909_, v___x_893_);
v___x_911_ = lean_array_push(v___x_910_, v___x_896_);
v___x_912_ = lean_array_push(v___x_911_, v___x_903_);
v___x_913_ = lean_array_push(v___x_912_, v___x_891_);
v___x_914_ = lean_array_push(v___x_913_, v___y_858_);
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
v___x_919_ = l_Lean_Elab_Tactic_Do_expandDefContract___lam__0(v___y_859_, v___y_861_, v_a_873_);
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
v___x_927_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_867_, v___x_926_);
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
v___y_632_ = v___x_877_;
v___y_633_ = v___y_850_;
v___y_634_ = v___y_851_;
v___y_635_ = v___y_849_;
v___y_636_ = v___y_852_;
v___y_637_ = v___x_882_;
v___y_638_ = v___y_853_;
v___y_639_ = v___y_854_;
v___y_640_ = v___x_894_;
v___y_641_ = v___y_857_;
v___y_642_ = v___x_895_;
v___y_643_ = v___x_885_;
v___y_644_ = v___y_863_;
v___y_645_ = v___x_918_;
v___y_646_ = v___y_864_;
v___y_647_ = v___y_865_;
v___y_648_ = v___x_878_;
v___y_649_ = v___y_866_;
v___y_650_ = v___x_931_;
v___y_651_ = v___y_868_;
v_specTac_652_ = v___x_937_;
v___y_653_ = v___y_861_;
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
v___x_941_ = l_Lean_Elab_Tactic_Do_expandDefContract___lam__0(v___y_859_, v___y_861_, v_a_873_);
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
v___x_949_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_867_, v___x_947_);
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
v___y_632_ = v___x_877_;
v___y_633_ = v___y_850_;
v___y_634_ = v___y_851_;
v___y_635_ = v___y_849_;
v___y_636_ = v___y_852_;
v___y_637_ = v___x_882_;
v___y_638_ = v___y_853_;
v___y_639_ = v___y_854_;
v___y_640_ = v___x_894_;
v___y_641_ = v___y_857_;
v___y_642_ = v___x_895_;
v___y_643_ = v___x_885_;
v___y_644_ = v___y_863_;
v___y_645_ = v___x_918_;
v___y_646_ = v___y_864_;
v___y_647_ = v___y_865_;
v___y_648_ = v___x_878_;
v___y_649_ = v___y_866_;
v___y_650_ = v___x_953_;
v___y_651_ = v___y_868_;
v_specTac_652_ = v___x_962_;
v___y_653_ = v___y_861_;
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
v___x_1002_ = l_Lean_Syntax_getArgs(v___y_980_);
lean_dec(v___y_980_);
v___x_1003_ = lean_array_get_size(v___x_1002_);
v___x_1004_ = lean_nat_dec_lt(v___y_972_, v___x_1003_);
if (v___x_1004_ == 0)
{
lean_dec_ref(v___x_1002_);
v___y_848_ = v___y_968_;
v___y_849_ = v___y_969_;
v___y_850_ = v___y_970_;
v___y_851_ = v___y_971_;
v___y_852_ = v___x_995_;
v___y_853_ = v___y_972_;
v___y_854_ = v___y_973_;
v___y_855_ = v___y_974_;
v___y_856_ = v___y_975_;
v___y_857_ = v___y_976_;
v___y_858_ = v_post_985_;
v___y_859_ = v_ref_987_;
v___y_860_ = v___y_977_;
v___y_861_ = v___y_986_;
v___y_862_ = v___y_978_;
v___y_863_ = v___y_979_;
v___y_864_ = v___x_996_;
v___y_865_ = v___y_981_;
v___y_866_ = v___y_982_;
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
v___x_1006_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2(v___x_1002_, v___x_1005_, v___y_974_, v___x_1001_, v___y_986_, v_a_991_);
lean_dec_ref(v___x_1002_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; lean_object* v_a_1008_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_a_1007_);
v_a_1008_ = lean_ctor_get(v___x_1006_, 1);
lean_inc(v_a_1008_);
lean_dec_ref_known(v___x_1006_, 2);
v___y_848_ = v___y_968_;
v___y_849_ = v___y_969_;
v___y_850_ = v___y_970_;
v___y_851_ = v___y_971_;
v___y_852_ = v___x_995_;
v___y_853_ = v___y_972_;
v___y_854_ = v___y_973_;
v___y_855_ = v___y_974_;
v___y_856_ = v___y_975_;
v___y_857_ = v___y_976_;
v___y_858_ = v_post_985_;
v___y_859_ = v_ref_987_;
v___y_860_ = v___y_977_;
v___y_861_ = v___y_986_;
v___y_862_ = v___y_978_;
v___y_863_ = v___y_979_;
v___y_864_ = v___x_996_;
v___y_865_ = v___y_981_;
v___y_866_ = v___y_982_;
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
lean_dec(v___y_983_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec(v___y_976_);
lean_dec(v___y_975_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
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
v___x_1065_ = l_Lean_Syntax_isNone(v___y_1045_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1066_; lean_object* v___x_1067_; uint8_t v___x_1068_; 
v___x_1066_ = l_Lean_Syntax_getArg(v___y_1045_, v___y_1049_);
lean_dec(v___y_1045_);
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
v___y_1022_ = v___y_1046_;
v___y_1023_ = v___y_1047_;
v___y_1024_ = v___y_1048_;
v___y_1025_ = v___y_1049_;
v___y_1026_ = v___y_1050_;
v___y_1027_ = v___y_1051_;
v___y_1028_ = v_pre_1062_;
v___y_1029_ = v___y_1052_;
v___y_1030_ = v___y_1054_;
v___y_1031_ = v___y_1055_;
v___y_1032_ = v___y_1056_;
v___y_1033_ = v___y_1057_;
v___y_1034_ = v___y_1058_;
v___y_1035_ = v___y_1059_;
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
lean_dec(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec(v___y_1052_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
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
v___y_1022_ = v___y_1046_;
v___y_1023_ = v___y_1047_;
v___y_1024_ = v___y_1048_;
v___y_1025_ = v___y_1049_;
v___y_1026_ = v___y_1050_;
v___y_1027_ = v___y_1051_;
v___y_1028_ = v_pre_1062_;
v___y_1029_ = v___y_1052_;
v___y_1030_ = v___y_1054_;
v___y_1031_ = v___y_1055_;
v___y_1032_ = v___y_1056_;
v___y_1033_ = v___y_1057_;
v___y_1034_ = v___y_1058_;
v___y_1035_ = v___y_1059_;
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
lean_dec(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec(v___y_1052_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
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
v___y_969_ = v___y_1046_;
v___y_970_ = v___y_1047_;
v___y_971_ = v___y_1048_;
v___y_972_ = v___y_1049_;
v___y_973_ = v___y_1050_;
v___y_974_ = v___y_1051_;
v___y_975_ = v_pre_1062_;
v___y_976_ = v___y_1052_;
v___y_977_ = v___y_1054_;
v___y_978_ = v___y_1055_;
v___y_979_ = v___y_1056_;
v___y_980_ = v___y_1057_;
v___y_981_ = v___y_1058_;
v___y_982_ = v___y_1059_;
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
lean_dec(v___y_1045_);
v_ref_1102_ = lean_ctor_get(v___y_1063_, 5);
v___x_1103_ = l_Lean_SourceInfo_fromRef(v_ref_1102_, v___y_1053_);
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
v___y_969_ = v___y_1046_;
v___y_970_ = v___y_1047_;
v___y_971_ = v___y_1048_;
v___y_972_ = v___y_1049_;
v___y_973_ = v___y_1050_;
v___y_974_ = v___y_1051_;
v___y_975_ = v_pre_1062_;
v___y_976_ = v___y_1052_;
v___y_977_ = v___y_1054_;
v___y_978_ = v___y_1055_;
v___y_979_ = v___y_1056_;
v___y_980_ = v___y_1057_;
v___y_981_ = v___y_1058_;
v___y_982_ = v___y_1059_;
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
v___x_1146_ = l_Lean_Syntax_isNone(v___y_1136_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; lean_object* v___x_1148_; uint8_t v___x_1149_; 
v___x_1147_ = l_Lean_Syntax_getArg(v___y_1136_, v___y_1130_);
lean_dec(v___y_1136_);
v___x_1148_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__72));
lean_inc(v___x_1147_);
v___x_1149_ = l_Lean_Syntax_isOfKind(v___x_1147_, v___x_1148_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; 
lean_dec(v___x_1147_);
v___x_1150_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1143_);
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
v___y_1046_ = v___y_1127_;
v___y_1047_ = v___y_1128_;
v___y_1048_ = v___y_1129_;
v___y_1049_ = v___y_1130_;
v___y_1050_ = v___y_1131_;
v___y_1051_ = v___y_1132_;
v___y_1052_ = v___y_1134_;
v___y_1053_ = v___y_1135_;
v___y_1054_ = v___y_1137_;
v___y_1055_ = v___y_1145_;
v___y_1056_ = v___y_1138_;
v___y_1057_ = v___y_1139_;
v___y_1058_ = v___y_1140_;
v___y_1059_ = v___y_1141_;
v___y_1060_ = v___y_1142_;
v___y_1061_ = v___y_1144_;
v_pre_1062_ = v_a_1151_;
v___y_1063_ = v___y_1133_;
v___y_1064_ = v_a_1152_;
goto v___jp_1043_;
}
else
{
lean_object* v_a_1153_; lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
lean_dec_ref(v___y_1145_);
lean_dec(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec(v___y_1139_);
lean_dec(v___y_1137_);
lean_dec(v___y_1134_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1129_);
lean_dec(v___y_1128_);
lean_dec(v___y_1126_);
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
v___y_1046_ = v___y_1127_;
v___y_1047_ = v___y_1128_;
v___y_1048_ = v___y_1129_;
v___y_1049_ = v___y_1130_;
v___y_1050_ = v___y_1131_;
v___y_1051_ = v___y_1132_;
v___y_1052_ = v___y_1134_;
v___y_1053_ = v___y_1135_;
v___y_1054_ = v___y_1137_;
v___y_1055_ = v___y_1145_;
v___y_1056_ = v___y_1138_;
v___y_1057_ = v___y_1139_;
v___y_1058_ = v___y_1140_;
v___y_1059_ = v___y_1141_;
v___y_1060_ = v___y_1142_;
v___y_1061_ = v___y_1144_;
v_pre_1062_ = v___x_1162_;
v___y_1063_ = v___y_1133_;
v___y_1064_ = v___y_1143_;
goto v___jp_1043_;
}
else
{
lean_object* v_ref_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v_ref_1165_ = lean_ctor_get(v___y_1133_, 5);
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
v___y_1046_ = v___y_1127_;
v___y_1047_ = v___y_1128_;
v___y_1048_ = v___y_1129_;
v___y_1049_ = v___y_1130_;
v___y_1050_ = v___y_1131_;
v___y_1051_ = v___y_1132_;
v___y_1052_ = v___y_1134_;
v___y_1053_ = v___y_1135_;
v___y_1054_ = v___y_1137_;
v___y_1055_ = v___y_1145_;
v___y_1056_ = v___y_1138_;
v___y_1057_ = v___y_1139_;
v___y_1058_ = v___y_1140_;
v___y_1059_ = v___y_1141_;
v___y_1060_ = v___y_1142_;
v___y_1061_ = v___y_1144_;
v_pre_1062_ = v___x_1170_;
v___y_1063_ = v___y_1133_;
v___y_1064_ = v___y_1143_;
goto v___jp_1043_;
}
}
}
else
{
lean_object* v_ref_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
lean_dec(v___y_1136_);
v_ref_1171_ = lean_ctor_get(v___y_1133_, 5);
v___x_1172_ = l_Lean_SourceInfo_fromRef(v_ref_1171_, v___y_1135_);
v___x_1173_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__69));
v___x_1174_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__70));
lean_inc(v___x_1172_);
v___x_1175_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1172_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
v___x_1176_ = l_Lean_Syntax_node1(v___x_1172_, v___x_1173_, v___x_1175_);
v___y_1044_ = v___y_1125_;
v___y_1045_ = v___y_1126_;
v___y_1046_ = v___y_1127_;
v___y_1047_ = v___y_1128_;
v___y_1048_ = v___y_1129_;
v___y_1049_ = v___y_1130_;
v___y_1050_ = v___y_1131_;
v___y_1051_ = v___y_1132_;
v___y_1052_ = v___y_1134_;
v___y_1053_ = v___y_1135_;
v___y_1054_ = v___y_1137_;
v___y_1055_ = v___y_1145_;
v___y_1056_ = v___y_1138_;
v___y_1057_ = v___y_1139_;
v___y_1058_ = v___y_1140_;
v___y_1059_ = v___y_1141_;
v___y_1060_ = v___y_1142_;
v___y_1061_ = v___y_1144_;
v_pre_1062_ = v___x_1176_;
v___y_1063_ = v___y_1133_;
v___y_1064_ = v___y_1143_;
goto v___jp_1043_;
}
}
v___jp_1177_:
{
lean_object* v___x_1198_; size_t v_sz_1199_; size_t v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; uint8_t v___x_1204_; 
lean_inc_ref(v___y_1189_);
v___x_1198_ = l_Array_append___redArg(v___y_1189_, v___y_1197_);
lean_dec_ref(v___y_1197_);
v_sz_1199_ = lean_array_size(v___x_1198_);
v___x_1200_ = ((size_t)0ULL);
v___x_1201_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__0(v_sz_1199_, v___x_1200_, v___x_1198_);
v___x_1202_ = lean_mk_empty_array_with_capacity(v___y_1182_);
v___x_1203_ = lean_array_get_size(v___y_1189_);
v___x_1204_ = lean_nat_dec_lt(v___y_1182_, v___x_1203_);
if (v___x_1204_ == 0)
{
lean_dec_ref(v___y_1189_);
v___y_1125_ = v___y_1178_;
v___y_1126_ = v___y_1179_;
v___y_1127_ = v___y_1180_;
v___y_1128_ = v___y_1181_;
v___y_1129_ = v___x_1201_;
v___y_1130_ = v___y_1182_;
v___y_1131_ = v___y_1183_;
v___y_1132_ = v___x_1200_;
v___y_1133_ = v___y_1184_;
v___y_1134_ = v___y_1185_;
v___y_1135_ = v___y_1186_;
v___y_1136_ = v___y_1187_;
v___y_1137_ = v___y_1188_;
v___y_1138_ = v___y_1190_;
v___y_1139_ = v___y_1191_;
v___y_1140_ = v___y_1192_;
v___y_1141_ = v___y_1193_;
v___y_1142_ = v___y_1194_;
v___y_1143_ = v___y_1195_;
v___y_1144_ = v___y_1196_;
v___y_1145_ = v___x_1202_;
goto v___jp_1124_;
}
else
{
size_t v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = lean_usize_of_nat(v___x_1203_);
v___x_1206_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__3(v___y_1189_, v___x_1200_, v___x_1205_, v___x_1202_);
lean_dec_ref(v___y_1189_);
v___y_1125_ = v___y_1178_;
v___y_1126_ = v___y_1179_;
v___y_1127_ = v___y_1180_;
v___y_1128_ = v___y_1181_;
v___y_1129_ = v___x_1201_;
v___y_1130_ = v___y_1182_;
v___y_1131_ = v___y_1183_;
v___y_1132_ = v___x_1200_;
v___y_1133_ = v___y_1184_;
v___y_1134_ = v___y_1185_;
v___y_1135_ = v___y_1186_;
v___y_1136_ = v___y_1187_;
v___y_1137_ = v___y_1188_;
v___y_1138_ = v___y_1190_;
v___y_1139_ = v___y_1191_;
v___y_1140_ = v___y_1192_;
v___y_1141_ = v___y_1193_;
v___y_1142_ = v___y_1194_;
v___y_1143_ = v___y_1195_;
v___y_1144_ = v___y_1196_;
v___y_1145_ = v___x_1206_;
goto v___jp_1124_;
}
}
v___jp_1208_:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; uint8_t v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1223_ = l_Lean_Syntax_getArg(v_decl_1207_, v___y_1209_);
v___x_1224_ = l_Lean_Syntax_getArg(v_decl_1207_, v___x_1042_);
lean_dec(v_decl_1207_);
v___x_1225_ = l_Lean_Syntax_getArg(v___x_1224_, v___y_1214_);
lean_dec(v___x_1224_);
v___x_1226_ = l_Lean_TSyntax_getId(v___x_1225_);
v___x_1227_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0___closed__0));
v___x_1228_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0___closed__1));
lean_inc(v___x_1226_);
v___x_1229_ = l_Lean_Name_append(v___x_1226_, v___x_1228_);
v___x_1230_ = 0;
v___x_1231_ = l_Lean_mkIdentFrom(v___x_1225_, v___x_1229_, v___x_1230_);
v___x_1232_ = l_Lean_Syntax_getArg(v___x_1223_, v___y_1214_);
lean_dec(v___x_1223_);
v___x_1233_ = l_Lean_Syntax_getArgs(v___x_1232_);
lean_dec(v___x_1232_);
v___x_1234_ = l_Lean_Syntax_isNone(v___y_1219_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1235_ = l_Lean_Syntax_getArg(v___y_1219_, v___y_1214_);
lean_dec(v___y_1219_);
v___x_1236_ = l_Lean_Syntax_getArg(v___x_1235_, v___x_1042_);
lean_dec(v___x_1235_);
v___x_1237_ = l_Lean_Syntax_getArgs(v___x_1236_);
lean_dec(v___x_1236_);
v___y_1178_ = v___y_1209_;
v___y_1179_ = v___y_1210_;
v___y_1180_ = v___y_1212_;
v___y_1181_ = v___y_1211_;
v___y_1182_ = v___y_1214_;
v___y_1183_ = v___y_1215_;
v___y_1184_ = v___y_1221_;
v___y_1185_ = v___x_1231_;
v___y_1186_ = v___x_1230_;
v___y_1187_ = v___y_1218_;
v___y_1188_ = v___y_1220_;
v___y_1189_ = v___x_1233_;
v___y_1190_ = v___y_1213_;
v___y_1191_ = v___y_1216_;
v___y_1192_ = v___y_1217_;
v___y_1193_ = v___x_1225_;
v___y_1194_ = v___x_1226_;
v___y_1195_ = v___y_1222_;
v___y_1196_ = v___x_1227_;
v___y_1197_ = v___x_1237_;
goto v___jp_1177_;
}
else
{
lean_object* v___x_1238_; 
lean_dec(v___y_1219_);
v___x_1238_ = lean_mk_empty_array_with_capacity(v___y_1214_);
v___y_1178_ = v___y_1209_;
v___y_1179_ = v___y_1210_;
v___y_1180_ = v___y_1212_;
v___y_1181_ = v___y_1211_;
v___y_1182_ = v___y_1214_;
v___y_1183_ = v___y_1215_;
v___y_1184_ = v___y_1221_;
v___y_1185_ = v___x_1231_;
v___y_1186_ = v___x_1230_;
v___y_1187_ = v___y_1218_;
v___y_1188_ = v___y_1220_;
v___y_1189_ = v___x_1233_;
v___y_1190_ = v___y_1213_;
v___y_1191_ = v___y_1216_;
v___y_1192_ = v___y_1217_;
v___y_1193_ = v___x_1225_;
v___y_1194_ = v___x_1226_;
v___y_1195_ = v___y_1222_;
v___y_1196_ = v___x_1227_;
v___y_1197_ = v___x_1238_;
goto v___jp_1177_;
}
}
v___jp_1239_:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__73));
v___x_1256_ = l_Lean_Macro_throwErrorAt___redArg(v___y_1254_, v___x_1255_, v___y_1249_, v___y_1246_);
lean_dec(v___y_1254_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; 
v_a_1257_ = lean_ctor_get(v___x_1256_, 1);
lean_inc(v_a_1257_);
lean_dec_ref_known(v___x_1256_, 2);
v___y_1209_ = v___y_1240_;
v___y_1210_ = v___y_1241_;
v___y_1211_ = v___y_1242_;
v___y_1212_ = v___y_1243_;
v___y_1213_ = v___y_1250_;
v___y_1214_ = v___y_1244_;
v___y_1215_ = v___y_1245_;
v___y_1216_ = v___y_1251_;
v___y_1217_ = v___y_1252_;
v___y_1218_ = v___y_1247_;
v___y_1219_ = v___y_1253_;
v___y_1220_ = v___y_1248_;
v___y_1221_ = v___y_1249_;
v___y_1222_ = v_a_1257_;
goto v___jp_1208_;
}
else
{
lean_object* v_a_1258_; lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
lean_dec(v___y_1253_);
lean_dec(v___y_1251_);
lean_dec(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec(v___y_1245_);
lean_dec(v___y_1242_);
lean_dec(v___y_1241_);
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
v___x_1279_ = l_Lean_Syntax_getArg(v___y_1270_, v___x_1278_);
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
v___x_1291_ = l_Lean_Syntax_setArg(v_decl_1207_, v___y_1273_, v_snd_1284_);
v___x_1292_ = l_Lean_Syntax_setArg(v_stx_628_, v___x_1042_, v___x_1291_);
v___x_1293_ = lean_unbox(v_a_1289_);
lean_dec(v_a_1289_);
if (v___x_1293_ == 0)
{
uint8_t v___x_1294_; 
v___x_1294_ = l_Lean_Syntax_isNone(v___y_1275_);
if (v___x_1294_ == 0)
{
lean_inc(v___y_1275_);
v___y_1240_ = v___y_1268_;
v___y_1241_ = v___y_1269_;
v___y_1242_ = v___y_1270_;
v___y_1243_ = v___x_1286_;
v___y_1244_ = v___y_1271_;
v___y_1245_ = v___x_1292_;
v___y_1246_ = v_a_1290_;
v___y_1247_ = v___y_1274_;
v___y_1248_ = v_fst_1283_;
v___y_1249_ = v___y_1276_;
v___y_1250_ = v___x_1285_;
v___y_1251_ = v___y_1272_;
v___y_1252_ = v___y_1273_;
v___y_1253_ = v___y_1275_;
v___y_1254_ = v___y_1275_;
goto v___jp_1239_;
}
else
{
uint8_t v___x_1295_; 
v___x_1295_ = l_Lean_Syntax_isNone(v___y_1274_);
if (v___x_1295_ == 0)
{
lean_inc(v___y_1274_);
v___y_1240_ = v___y_1268_;
v___y_1241_ = v___y_1269_;
v___y_1242_ = v___y_1270_;
v___y_1243_ = v___x_1286_;
v___y_1244_ = v___y_1271_;
v___y_1245_ = v___x_1292_;
v___y_1246_ = v_a_1290_;
v___y_1247_ = v___y_1274_;
v___y_1248_ = v_fst_1283_;
v___y_1249_ = v___y_1276_;
v___y_1250_ = v___x_1285_;
v___y_1251_ = v___y_1272_;
v___y_1252_ = v___y_1273_;
v___y_1253_ = v___y_1275_;
v___y_1254_ = v___y_1274_;
goto v___jp_1239_;
}
else
{
uint8_t v___x_1296_; 
v___x_1296_ = l_Lean_Syntax_isNone(v___y_1269_);
if (v___x_1296_ == 0)
{
lean_inc(v___y_1269_);
v___y_1240_ = v___y_1268_;
v___y_1241_ = v___y_1269_;
v___y_1242_ = v___y_1270_;
v___y_1243_ = v___x_1286_;
v___y_1244_ = v___y_1271_;
v___y_1245_ = v___x_1292_;
v___y_1246_ = v_a_1290_;
v___y_1247_ = v___y_1274_;
v___y_1248_ = v_fst_1283_;
v___y_1249_ = v___y_1276_;
v___y_1250_ = v___x_1285_;
v___y_1251_ = v___y_1272_;
v___y_1252_ = v___y_1273_;
v___y_1253_ = v___y_1275_;
v___y_1254_ = v___y_1269_;
goto v___jp_1239_;
}
else
{
lean_inc(v___y_1272_);
v___y_1240_ = v___y_1268_;
v___y_1241_ = v___y_1269_;
v___y_1242_ = v___y_1270_;
v___y_1243_ = v___x_1286_;
v___y_1244_ = v___y_1271_;
v___y_1245_ = v___x_1292_;
v___y_1246_ = v_a_1290_;
v___y_1247_ = v___y_1274_;
v___y_1248_ = v_fst_1283_;
v___y_1249_ = v___y_1276_;
v___y_1250_ = v___x_1285_;
v___y_1251_ = v___y_1272_;
v___y_1252_ = v___y_1273_;
v___y_1253_ = v___y_1275_;
v___y_1254_ = v___y_1272_;
goto v___jp_1239_;
}
}
}
}
else
{
v___y_1209_ = v___y_1268_;
v___y_1210_ = v___y_1269_;
v___y_1211_ = v___y_1270_;
v___y_1212_ = v___x_1286_;
v___y_1213_ = v___x_1285_;
v___y_1214_ = v___y_1271_;
v___y_1215_ = v___x_1292_;
v___y_1216_ = v___y_1272_;
v___y_1217_ = v___y_1273_;
v___y_1218_ = v___y_1274_;
v___y_1219_ = v___y_1275_;
v___y_1220_ = v_fst_1283_;
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
lean_dec(v___y_1275_);
lean_dec(v___y_1274_);
lean_dec(v___y_1272_);
lean_dec(v___y_1270_);
lean_dec(v___y_1269_);
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
lean_dec(v___y_1275_);
lean_dec(v___y_1274_);
lean_dec(v___y_1272_);
lean_dec(v___y_1270_);
lean_dec(v___y_1269_);
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
v___y_1268_ = v___x_1323_;
v___y_1269_ = v_ensuresStx_1324_;
v___y_1270_ = v___y_1316_;
v___y_1271_ = v___x_1320_;
v___y_1272_ = v_throwsStx_1325_;
v___y_1273_ = v___y_1317_;
v___y_1274_ = v_requiresStx_1322_;
v___y_1275_ = v_givenStx_1321_;
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
v___y_1268_ = v___x_1323_;
v___y_1269_ = v_ensuresStx_1324_;
v___y_1270_ = v___y_1316_;
v___y_1271_ = v___x_1320_;
v___y_1272_ = v_throwsStx_1325_;
v___y_1273_ = v___y_1317_;
v___y_1274_ = v_requiresStx_1322_;
v___y_1275_ = v_givenStx_1321_;
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
v___y_1268_ = v___x_1323_;
v___y_1269_ = v_ensuresStx_1324_;
v___y_1270_ = v___y_1316_;
v___y_1271_ = v___x_1320_;
v___y_1272_ = v_throwsStx_1325_;
v___y_1273_ = v___y_1317_;
v___y_1274_ = v_requiresStx_1322_;
v___y_1275_ = v_givenStx_1321_;
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
v___y_1268_ = v___x_1323_;
v___y_1269_ = v_ensuresStx_1324_;
v___y_1270_ = v___y_1316_;
v___y_1271_ = v___x_1320_;
v___y_1272_ = v_throwsStx_1325_;
v___y_1273_ = v___y_1317_;
v___y_1274_ = v_requiresStx_1322_;
v___y_1275_ = v_givenStx_1321_;
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
v___y_1268_ = v___x_1323_;
v___y_1269_ = v_ensuresStx_1324_;
v___y_1270_ = v___y_1316_;
v___y_1271_ = v___x_1320_;
v___y_1272_ = v_throwsStx_1325_;
v___y_1273_ = v___y_1317_;
v___y_1274_ = v_requiresStx_1322_;
v___y_1275_ = v_givenStx_1321_;
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
lean_object* v___x_1455_; 
v___x_1455_ = l_Lean_ImportedConsts_empty___redArg();
return v___x_1455_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3(void){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1458_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0);
v___x_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1458_);
return v___x_1459_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__4(void){
_start:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1460_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3);
v___x_1461_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__2));
v___x_1462_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__1, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__1);
v___x_1463_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1462_);
lean_ctor_set(v___x_1463_, 1, v___x_1461_);
lean_ctor_set(v___x_1463_, 2, v___x_1461_);
lean_ctor_set(v___x_1463_, 3, v___x_1460_);
return v___x_1463_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__5(void){
_start:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1464_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3);
v___x_1465_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___closed__0);
v___x_1466_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__4, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__4_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__4);
v___x_1467_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
lean_ctor_set(v___x_1467_, 1, v___x_1465_);
lean_ctor_set(v___x_1467_, 2, v___x_1464_);
return v___x_1467_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__6(void){
_start:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v_thms_1473_; 
v___x_1468_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3);
v___x_1469_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___closed__0);
v___x_1470_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___closed__0);
v___x_1471_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__5, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__5);
v___x_1472_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__0, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__0);
v_thms_1473_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_thms_1473_, 0, v___x_1472_);
lean_ctor_set(v_thms_1473_, 1, v___x_1472_);
lean_ctor_set(v_thms_1473_, 2, v___x_1471_);
lean_ctor_set(v_thms_1473_, 3, v___x_1470_);
lean_ctor_set(v_thms_1473_, 4, v___x_1469_);
lean_ctor_set(v_thms_1473_, 5, v___x_1468_);
return v_thms_1473_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__8(void){
_start:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1481_ = lean_unsigned_to_nat(0u);
v___x_1482_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3);
v___x_1483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1482_);
lean_ctor_set(v___x_1483_, 1, v___x_1481_);
return v___x_1483_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__9(void){
_start:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1484_ = lean_unsigned_to_nat(32u);
v___x_1485_ = lean_mk_empty_array_with_capacity(v___x_1484_);
v___x_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1485_);
return v___x_1486_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__10(void){
_start:
{
size_t v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1487_ = ((size_t)5ULL);
v___x_1488_ = lean_unsigned_to_nat(0u);
v___x_1489_ = lean_unsigned_to_nat(32u);
v___x_1490_ = lean_mk_empty_array_with_capacity(v___x_1489_);
v___x_1491_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__9, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__9);
v___x_1492_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1492_, 0, v___x_1491_);
lean_ctor_set(v___x_1492_, 1, v___x_1490_);
lean_ctor_set(v___x_1492_, 2, v___x_1488_);
lean_ctor_set(v___x_1492_, 3, v___x_1488_);
lean_ctor_set_usize(v___x_1492_, 4, v___x_1487_);
return v___x_1492_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__11(void){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1493_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__10, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__10_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__10);
v___x_1494_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3);
v___x_1495_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1494_);
lean_ctor_set(v___x_1495_, 1, v___x_1494_);
lean_ctor_set(v___x_1495_, 2, v___x_1494_);
lean_ctor_set(v___x_1495_, 3, v___x_1493_);
return v___x_1495_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__12(void){
_start:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1496_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__11, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__11_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__11);
v___x_1497_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__8, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__8_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__8);
v___x_1498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1497_);
lean_ctor_set(v___x_1498_, 1, v___x_1496_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith(lean_object* v_names_1499_, lean_object* v_e_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_){
_start:
{
lean_object* v___x_1508_; lean_object* v_thms_1509_; size_t v_sz_1510_; size_t v___x_1511_; lean_object* v___x_1512_; 
v___x_1508_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__2));
v_thms_1509_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__6, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__6);
v_sz_1510_ = lean_array_size(v_names_1499_);
v___x_1511_ = ((size_t)0ULL);
v___x_1512_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__2___redArg(v_names_1499_, v_sz_1510_, v___x_1511_, v_thms_1509_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_a_1513_; lean_object* v___x_1514_; 
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_a_1513_);
lean_dec_ref_known(v___x_1512_, 1);
v___x_1514_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_1506_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_a_1515_);
lean_dec_ref_known(v___x_1514_, 1);
v___x_1516_ = lean_box(0);
v___x_1517_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__7));
v___x_1518_ = lean_unsigned_to_nat(1u);
v___x_1519_ = lean_mk_empty_array_with_capacity(v___x_1518_);
v___x_1520_ = lean_array_push(v___x_1519_, v_a_1513_);
v___x_1521_ = l_Lean_Options_empty;
v___x_1522_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1517_, v___x_1520_, v_a_1515_, v___x_1521_, v_a_1503_, v_a_1505_, v_a_1506_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1523_);
lean_dec_ref_known(v___x_1522_, 1);
v___x_1524_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__12, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__12_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__12);
v___x_1525_ = l_Lean_Meta_simp(v_e_1500_, v_a_1523_, v___x_1508_, v___x_1516_, v___x_1524_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_);
if (lean_obj_tag(v___x_1525_) == 0)
{
lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1535_; 
v_a_1526_ = lean_ctor_get(v___x_1525_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1528_ = v___x_1525_;
v_isShared_1529_ = v_isSharedCheck_1535_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_dec(v___x_1525_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1535_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v_fst_1530_; lean_object* v_expr_1531_; lean_object* v___x_1533_; 
v_fst_1530_ = lean_ctor_get(v_a_1526_, 0);
lean_inc(v_fst_1530_);
lean_dec(v_a_1526_);
v_expr_1531_ = lean_ctor_get(v_fst_1530_, 0);
lean_inc_ref(v_expr_1531_);
lean_dec(v_fst_1530_);
if (v_isShared_1529_ == 0)
{
lean_ctor_set(v___x_1528_, 0, v_expr_1531_);
v___x_1533_ = v___x_1528_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_expr_1531_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
else
{
lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1543_; 
v_a_1536_ = lean_ctor_get(v___x_1525_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1538_ = v___x_1525_;
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1525_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1541_; 
if (v_isShared_1539_ == 0)
{
v___x_1541_ = v___x_1538_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_a_1536_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
}
else
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1551_; 
lean_dec_ref(v_e_1500_);
v_a_1544_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1546_ = v___x_1522_;
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v___x_1522_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1549_; 
if (v_isShared_1547_ == 0)
{
v___x_1549_ = v___x_1546_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_a_1544_);
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
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1559_; 
lean_dec(v_a_1513_);
lean_dec_ref(v_e_1500_);
v_a_1552_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1554_ = v___x_1514_;
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1514_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1557_; 
if (v_isShared_1555_ == 0)
{
v___x_1557_ = v___x_1554_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_a_1552_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
lean_dec_ref(v_e_1500_);
v_a_1560_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1512_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1512_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1560_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___boxed(lean_object* v_names_1568_, lean_object* v_e_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_){
_start:
{
lean_object* v_res_1577_; 
v_res_1577_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith(v_names_1568_, v_e_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_);
lean_dec(v_a_1575_);
lean_dec_ref(v_a_1574_);
lean_dec(v_a_1573_);
lean_dec_ref(v_a_1572_);
lean_dec(v_a_1571_);
lean_dec_ref(v_a_1570_);
lean_dec_ref(v_names_1568_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__2(lean_object* v_as_1578_, size_t v_sz_1579_, size_t v_i_1580_, lean_object* v_b_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__2___redArg(v_as_1578_, v_sz_1579_, v_i_1580_, v_b_1581_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__2___boxed(lean_object* v_as_1590_, lean_object* v_sz_1591_, lean_object* v_i_1592_, lean_object* v_b_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
size_t v_sz_boxed_1601_; size_t v_i_boxed_1602_; lean_object* v_res_1603_; 
v_sz_boxed_1601_ = lean_unbox_usize(v_sz_1591_);
lean_dec(v_sz_1591_);
v_i_boxed_1602_ = lean_unbox_usize(v_i_1592_);
lean_dec(v_i_1592_);
v_res_1603_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__2(v_as_1590_, v_sz_boxed_1601_, v_i_boxed_1602_, v_b_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
lean_dec_ref(v_as_1590_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0___redArg(lean_object* v_e_1604_, lean_object* v___y_1605_){
_start:
{
uint8_t v___x_1607_; 
v___x_1607_ = l_Lean_Expr_hasMVar(v_e_1604_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1608_; 
v___x_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1608_, 0, v_e_1604_);
return v___x_1608_;
}
else
{
lean_object* v___x_1609_; lean_object* v_mctx_1610_; lean_object* v___x_1611_; lean_object* v_fst_1612_; lean_object* v_snd_1613_; lean_object* v___x_1614_; lean_object* v_cache_1615_; lean_object* v_zetaDeltaFVarIds_1616_; lean_object* v_postponed_1617_; lean_object* v_diag_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1627_; 
v___x_1609_ = lean_st_ref_get(v___y_1605_);
v_mctx_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc_ref(v_mctx_1610_);
lean_dec(v___x_1609_);
v___x_1611_ = l_Lean_instantiateMVarsCore(v_mctx_1610_, v_e_1604_);
v_fst_1612_ = lean_ctor_get(v___x_1611_, 0);
lean_inc(v_fst_1612_);
v_snd_1613_ = lean_ctor_get(v___x_1611_, 1);
lean_inc(v_snd_1613_);
lean_dec_ref(v___x_1611_);
v___x_1614_ = lean_st_ref_take(v___y_1605_);
v_cache_1615_ = lean_ctor_get(v___x_1614_, 1);
v_zetaDeltaFVarIds_1616_ = lean_ctor_get(v___x_1614_, 2);
v_postponed_1617_ = lean_ctor_get(v___x_1614_, 3);
v_diag_1618_ = lean_ctor_get(v___x_1614_, 4);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1627_ == 0)
{
lean_object* v_unused_1628_; 
v_unused_1628_ = lean_ctor_get(v___x_1614_, 0);
lean_dec(v_unused_1628_);
v___x_1620_ = v___x_1614_;
v_isShared_1621_ = v_isSharedCheck_1627_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_diag_1618_);
lean_inc(v_postponed_1617_);
lean_inc(v_zetaDeltaFVarIds_1616_);
lean_inc(v_cache_1615_);
lean_dec(v___x_1614_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1627_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1623_; 
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 0, v_snd_1613_);
v___x_1623_ = v___x_1620_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_snd_1613_);
lean_ctor_set(v_reuseFailAlloc_1626_, 1, v_cache_1615_);
lean_ctor_set(v_reuseFailAlloc_1626_, 2, v_zetaDeltaFVarIds_1616_);
lean_ctor_set(v_reuseFailAlloc_1626_, 3, v_postponed_1617_);
lean_ctor_set(v_reuseFailAlloc_1626_, 4, v_diag_1618_);
v___x_1623_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1624_ = lean_st_ref_put(v___y_1605_, v___x_1623_);
v___x_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1625_, 0, v_fst_1612_);
return v___x_1625_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0___redArg___boxed(lean_object* v_e_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0___redArg(v_e_1629_, v___y_1630_);
lean_dec(v___y_1630_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0(lean_object* v_e_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0___redArg(v_e_1633_, v___y_1637_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0___boxed(lean_object* v_e_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0(v_e_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__0(lean_object* v_e_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v___x_1664_; uint8_t v___x_1665_; 
v___x_1664_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__10));
v___x_1665_ = l_Lean_Expr_isAppOf(v_e_1653_, v___x_1664_);
if (v___x_1665_ == 0)
{
lean_dec_ref(v_e_1653_);
goto v___jp_1661_;
}
else
{
lean_object* v___x_1666_; 
v___x_1666_ = l_Lean_Meta_unfoldProjInst_x3f(v_e_1653_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1682_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1669_ = v___x_1666_;
v_isShared_1670_ = v_isSharedCheck_1682_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1666_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1682_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
if (lean_obj_tag(v_a_1667_) == 1)
{
lean_object* v_val_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1681_; 
v_val_1671_ = lean_ctor_get(v_a_1667_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v_a_1667_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1673_ = v_a_1667_;
v_isShared_1674_ = v_isSharedCheck_1681_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_val_1671_);
lean_dec(v_a_1667_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1681_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1676_; 
if (v_isShared_1674_ == 0)
{
v___x_1676_ = v___x_1673_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_val_1671_);
v___x_1676_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
lean_object* v___x_1678_; 
if (v_isShared_1670_ == 0)
{
lean_ctor_set(v___x_1669_, 0, v___x_1676_);
v___x_1678_ = v___x_1669_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v___x_1676_);
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
else
{
lean_del_object(v___x_1669_);
lean_dec(v_a_1667_);
goto v___jp_1661_;
}
}
}
else
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
v_a_1683_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v___x_1666_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1666_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
v___jp_1661_:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1662_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__0___closed__0));
v___x_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1662_);
return v___x_1663_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__0___boxed(lean_object* v_e_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__0(v_e_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__1(lean_object* v_x_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1708_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__0___closed__0));
v___x_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1708_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__1___boxed(lean_object* v_x_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__1(v_x_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec_ref(v_x_1710_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___lam__0(lean_object* v_00_u03b1_1719_, lean_object* v_x_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1728_ = lean_apply_1(v_x_1720_, lean_box(0));
v___x_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___lam__0___boxed(lean_object* v_00_u03b1_1730_, lean_object* v_x_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___lam__0(v_00_u03b1_1730_, v_x_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
return v_res_1739_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__3(void){
_start:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1745_ = l_Lean_maxRecDepthErrorMessage;
v___x_1746_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1745_);
return v___x_1746_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__4(void){
_start:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1747_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__3);
v___x_1748_ = l_Lean_MessageData_ofFormat(v___x_1747_);
return v___x_1748_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__5(void){
_start:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1749_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__4);
v___x_1750_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__2));
v___x_1751_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1750_);
lean_ctor_set(v___x_1751_, 1, v___x_1749_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg(lean_object* v_ref_1752_){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1754_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__5);
v___x_1755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1755_, 0, v_ref_1752_);
lean_ctor_set(v___x_1755_, 1, v___x_1754_);
v___x_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___boxed(lean_object* v_ref_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_1757_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10___redArg(lean_object* v_x_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v___y_1770_; lean_object* v_toCold_1779_; lean_object* v_currRecDepth_1780_; lean_object* v_ref_1781_; uint16_t v_optionFlags_1782_; uint8_t v_suppressElabErrors_1783_; uint8_t v_checkDeprecated_1784_; uint8_t v_isRecordingDeps_1785_; lean_object* v_maxRecDepth_1791_; lean_object* v___x_1792_; uint8_t v___x_1793_; 
v_toCold_1779_ = lean_ctor_get(v___y_1766_, 0);
v_currRecDepth_1780_ = lean_ctor_get(v___y_1766_, 1);
v_ref_1781_ = lean_ctor_get(v___y_1766_, 2);
v_optionFlags_1782_ = lean_ctor_get_uint16(v___y_1766_, sizeof(void*)*3);
v_suppressElabErrors_1783_ = lean_ctor_get_uint8(v___y_1766_, sizeof(void*)*3 + 2);
v_checkDeprecated_1784_ = lean_ctor_get_uint8(v___y_1766_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1785_ = lean_ctor_get_uint8(v___y_1766_, sizeof(void*)*3 + 4);
v_maxRecDepth_1791_ = lean_ctor_get(v_toCold_1779_, 3);
v___x_1792_ = lean_unsigned_to_nat(0u);
v___x_1793_ = lean_nat_dec_eq(v_maxRecDepth_1791_, v___x_1792_);
if (v___x_1793_ == 0)
{
uint8_t v___x_1794_; 
v___x_1794_ = lean_nat_dec_eq(v_currRecDepth_1780_, v_maxRecDepth_1791_);
if (v___x_1794_ == 0)
{
goto v___jp_1786_;
}
else
{
lean_object* v___x_1795_; 
lean_dec_ref(v_x_1760_);
lean_inc(v_ref_1781_);
v___x_1795_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_1781_);
v___y_1770_ = v___x_1795_;
goto v___jp_1769_;
}
}
else
{
goto v___jp_1786_;
}
v___jp_1769_:
{
if (lean_obj_tag(v___y_1770_) == 0)
{
return v___y_1770_;
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
v_a_1771_ = lean_ctor_get(v___y_1770_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___y_1770_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___y_1770_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___y_1770_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
v___jp_1786_:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1787_ = lean_unsigned_to_nat(1u);
v___x_1788_ = lean_nat_add(v_currRecDepth_1780_, v___x_1787_);
lean_inc(v_ref_1781_);
lean_inc_ref(v_toCold_1779_);
v___x_1789_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1789_, 0, v_toCold_1779_);
lean_ctor_set(v___x_1789_, 1, v___x_1788_);
lean_ctor_set(v___x_1789_, 2, v_ref_1781_);
lean_ctor_set_uint16(v___x_1789_, sizeof(void*)*3, v_optionFlags_1782_);
lean_ctor_set_uint8(v___x_1789_, sizeof(void*)*3 + 2, v_suppressElabErrors_1783_);
lean_ctor_set_uint8(v___x_1789_, sizeof(void*)*3 + 3, v_checkDeprecated_1784_);
lean_ctor_set_uint8(v___x_1789_, sizeof(void*)*3 + 4, v_isRecordingDeps_1785_);
lean_inc(v___y_1767_);
lean_inc(v___y_1765_);
lean_inc_ref(v___y_1764_);
lean_inc(v___y_1763_);
lean_inc_ref(v___y_1762_);
lean_inc(v___y_1761_);
v___x_1790_ = lean_apply_8(v_x_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___x_1789_, v___y_1767_, lean_box(0));
v___y_1770_ = v___x_1790_;
goto v___jp_1769_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10___redArg___boxed(lean_object* v_x_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10___redArg(v_x_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__2(lean_object* v___x_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v___x_1814_; 
v___x_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1806_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__2___boxed(lean_object* v___x_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__2(v___x_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(lean_object* v_k_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v_b_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v___x_1834_; 
lean_inc(v___y_1832_);
lean_inc_ref(v___y_1831_);
lean_inc(v___y_1830_);
lean_inc_ref(v___y_1829_);
lean_inc(v___y_1827_);
lean_inc_ref(v___y_1826_);
lean_inc(v___y_1825_);
v___x_1834_ = lean_apply_9(v_k_1824_, v_b_1828_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, lean_box(0));
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed(lean_object* v_k_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v_b_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(v_k_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v_b_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg(lean_object* v_name_1846_, uint8_t v_bi_1847_, lean_object* v_type_1848_, lean_object* v_k_1849_, uint8_t v_kind_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
lean_object* v___f_1859_; lean_object* v___x_1860_; 
lean_inc(v___y_1853_);
lean_inc_ref(v___y_1852_);
lean_inc(v___y_1851_);
v___f_1859_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1859_, 0, v_k_1849_);
lean_closure_set(v___f_1859_, 1, v___y_1851_);
lean_closure_set(v___f_1859_, 2, v___y_1852_);
lean_closure_set(v___f_1859_, 3, v___y_1853_);
v___x_1860_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1846_, v_bi_1847_, v_type_1848_, v___f_1859_, v_kind_1850_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
if (lean_obj_tag(v___x_1860_) == 0)
{
return v___x_1860_;
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1860_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1860_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg___boxed(lean_object* v_name_1869_, lean_object* v_bi_1870_, lean_object* v_type_1871_, lean_object* v_k_1872_, lean_object* v_kind_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
uint8_t v_bi_boxed_1882_; uint8_t v_kind_boxed_1883_; lean_object* v_res_1884_; 
v_bi_boxed_1882_ = lean_unbox(v_bi_1870_);
v_kind_boxed_1883_ = lean_unbox(v_kind_1873_);
v_res_1884_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg(v_name_1869_, v_bi_boxed_1882_, v_type_1871_, v_k_1872_, v_kind_boxed_1883_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11___redArg(lean_object* v_name_1885_, lean_object* v_type_1886_, lean_object* v_val_1887_, lean_object* v_k_1888_, uint8_t v_nondep_1889_, uint8_t v_kind_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v___f_1899_; lean_object* v___x_1900_; 
lean_inc(v___y_1893_);
lean_inc_ref(v___y_1892_);
lean_inc(v___y_1891_);
v___f_1899_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1899_, 0, v_k_1888_);
lean_closure_set(v___f_1899_, 1, v___y_1891_);
lean_closure_set(v___f_1899_, 2, v___y_1892_);
lean_closure_set(v___f_1899_, 3, v___y_1893_);
v___x_1900_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1885_, v_type_1886_, v_val_1887_, v___f_1899_, v_nondep_1889_, v_kind_1890_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
if (lean_obj_tag(v___x_1900_) == 0)
{
return v___x_1900_;
}
else
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1908_; 
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1903_ = v___x_1900_;
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1900_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1901_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11___redArg___boxed(lean_object* v_name_1909_, lean_object* v_type_1910_, lean_object* v_val_1911_, lean_object* v_k_1912_, lean_object* v_nondep_1913_, lean_object* v_kind_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
uint8_t v_nondep_boxed_1923_; uint8_t v_kind_boxed_1924_; lean_object* v_res_1925_; 
v_nondep_boxed_1923_ = lean_unbox(v_nondep_1913_);
v_kind_boxed_1924_ = lean_unbox(v_kind_1914_);
v_res_1925_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11___redArg(v_name_1909_, v_type_1910_, v_val_1911_, v_k_1912_, v_nondep_boxed_1923_, v_kind_boxed_1924_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
lean_dec(v___y_1915_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5_spec__6___redArg(lean_object* v_a_1926_, lean_object* v_x_1927_){
_start:
{
if (lean_obj_tag(v_x_1927_) == 0)
{
lean_object* v___x_1928_; 
v___x_1928_ = lean_box(0);
return v___x_1928_;
}
else
{
lean_object* v_key_1929_; lean_object* v_value_1930_; lean_object* v_tail_1931_; uint8_t v___x_1932_; 
v_key_1929_ = lean_ctor_get(v_x_1927_, 0);
v_value_1930_ = lean_ctor_get(v_x_1927_, 1);
v_tail_1931_ = lean_ctor_get(v_x_1927_, 2);
v___x_1932_ = l_Lean_ExprStructEq_beq(v_key_1929_, v_a_1926_);
if (v___x_1932_ == 0)
{
v_x_1927_ = v_tail_1931_;
goto _start;
}
else
{
lean_object* v___x_1934_; 
lean_inc(v_value_1930_);
v___x_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1934_, 0, v_value_1930_);
return v___x_1934_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object* v_a_1935_, lean_object* v_x_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5_spec__6___redArg(v_a_1935_, v_x_1936_);
lean_dec(v_x_1936_);
lean_dec_ref(v_a_1935_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5___redArg(lean_object* v_m_1938_, lean_object* v_a_1939_){
_start:
{
lean_object* v_buckets_1940_; lean_object* v___x_1941_; uint64_t v___x_1942_; uint64_t v___x_1943_; uint64_t v___x_1944_; uint64_t v_fold_1945_; uint64_t v___x_1946_; uint64_t v___x_1947_; uint64_t v___x_1948_; size_t v___x_1949_; size_t v___x_1950_; size_t v___x_1951_; size_t v___x_1952_; size_t v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
v_buckets_1940_ = lean_ctor_get(v_m_1938_, 1);
v___x_1941_ = lean_array_get_size(v_buckets_1940_);
v___x_1942_ = l_Lean_ExprStructEq_hash(v_a_1939_);
v___x_1943_ = 32ULL;
v___x_1944_ = lean_uint64_shift_right(v___x_1942_, v___x_1943_);
v_fold_1945_ = lean_uint64_xor(v___x_1942_, v___x_1944_);
v___x_1946_ = 16ULL;
v___x_1947_ = lean_uint64_shift_right(v_fold_1945_, v___x_1946_);
v___x_1948_ = lean_uint64_xor(v_fold_1945_, v___x_1947_);
v___x_1949_ = lean_uint64_to_usize(v___x_1948_);
v___x_1950_ = lean_usize_of_nat(v___x_1941_);
v___x_1951_ = ((size_t)1ULL);
v___x_1952_ = lean_usize_sub(v___x_1950_, v___x_1951_);
v___x_1953_ = lean_usize_land(v___x_1949_, v___x_1952_);
v___x_1954_ = lean_array_uget_borrowed(v_buckets_1940_, v___x_1953_);
v___x_1955_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5_spec__6___redArg(v_a_1939_, v___x_1954_);
return v___x_1955_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5___redArg___boxed(lean_object* v_m_1956_, lean_object* v_a_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5___redArg(v_m_1956_, v_a_1957_);
lean_dec_ref(v_a_1957_);
lean_dec_ref(v_m_1956_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_1959_, lean_object* v_x_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1968_ = lean_apply_1(v_x_1960_, lean_box(0));
v___x_1969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1968_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_1970_, lean_object* v_x_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__0(v_00_u03b1_1970_, v_x_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__18___redArg(lean_object* v_a_1980_, lean_object* v_b_1981_, lean_object* v_x_1982_){
_start:
{
if (lean_obj_tag(v_x_1982_) == 0)
{
lean_dec(v_b_1981_);
lean_dec_ref(v_a_1980_);
return v_x_1982_;
}
else
{
lean_object* v_key_1983_; lean_object* v_value_1984_; lean_object* v_tail_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1997_; 
v_key_1983_ = lean_ctor_get(v_x_1982_, 0);
v_value_1984_ = lean_ctor_get(v_x_1982_, 1);
v_tail_1985_ = lean_ctor_get(v_x_1982_, 2);
v_isSharedCheck_1997_ = !lean_is_exclusive(v_x_1982_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1987_ = v_x_1982_;
v_isShared_1988_ = v_isSharedCheck_1997_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_tail_1985_);
lean_inc(v_value_1984_);
lean_inc(v_key_1983_);
lean_dec(v_x_1982_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1997_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
uint8_t v___x_1989_; 
v___x_1989_ = l_Lean_ExprStructEq_beq(v_key_1983_, v_a_1980_);
if (v___x_1989_ == 0)
{
lean_object* v___x_1990_; lean_object* v___x_1992_; 
v___x_1990_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__18___redArg(v_a_1980_, v_b_1981_, v_tail_1985_);
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 2, v___x_1990_);
v___x_1992_ = v___x_1987_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_key_1983_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v_value_1984_);
lean_ctor_set(v_reuseFailAlloc_1993_, 2, v___x_1990_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
else
{
lean_object* v___x_1995_; 
lean_dec(v_value_1984_);
lean_dec(v_key_1983_);
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 1, v_b_1981_);
lean_ctor_set(v___x_1987_, 0, v_a_1980_);
v___x_1995_ = v___x_1987_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_a_1980_);
lean_ctor_set(v_reuseFailAlloc_1996_, 1, v_b_1981_);
lean_ctor_set(v_reuseFailAlloc_1996_, 2, v_tail_1985_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16___redArg(lean_object* v_a_1998_, lean_object* v_x_1999_){
_start:
{
if (lean_obj_tag(v_x_1999_) == 0)
{
uint8_t v___x_2000_; 
v___x_2000_ = 0;
return v___x_2000_;
}
else
{
lean_object* v_key_2001_; lean_object* v_tail_2002_; uint8_t v___x_2003_; 
v_key_2001_ = lean_ctor_get(v_x_1999_, 0);
v_tail_2002_ = lean_ctor_get(v_x_1999_, 2);
v___x_2003_ = l_Lean_ExprStructEq_beq(v_key_2001_, v_a_1998_);
if (v___x_2003_ == 0)
{
v_x_1999_ = v_tail_2002_;
goto _start;
}
else
{
return v___x_2003_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16___redArg___boxed(lean_object* v_a_2005_, lean_object* v_x_2006_){
_start:
{
uint8_t v_res_2007_; lean_object* v_r_2008_; 
v_res_2007_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2005_, v_x_2006_);
lean_dec(v_x_2006_);
lean_dec_ref(v_a_2005_);
v_r_2008_ = lean_box(v_res_2007_);
return v_r_2008_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(lean_object* v_x_2009_, lean_object* v_x_2010_){
_start:
{
if (lean_obj_tag(v_x_2010_) == 0)
{
return v_x_2009_;
}
else
{
lean_object* v_key_2011_; lean_object* v_value_2012_; lean_object* v_tail_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2036_; 
v_key_2011_ = lean_ctor_get(v_x_2010_, 0);
v_value_2012_ = lean_ctor_get(v_x_2010_, 1);
v_tail_2013_ = lean_ctor_get(v_x_2010_, 2);
v_isSharedCheck_2036_ = !lean_is_exclusive(v_x_2010_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2015_ = v_x_2010_;
v_isShared_2016_ = v_isSharedCheck_2036_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_tail_2013_);
lean_inc(v_value_2012_);
lean_inc(v_key_2011_);
lean_dec(v_x_2010_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2036_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2017_; uint64_t v___x_2018_; uint64_t v___x_2019_; uint64_t v___x_2020_; uint64_t v_fold_2021_; uint64_t v___x_2022_; uint64_t v___x_2023_; uint64_t v___x_2024_; size_t v___x_2025_; size_t v___x_2026_; size_t v___x_2027_; size_t v___x_2028_; size_t v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2032_; 
v___x_2017_ = lean_array_get_size(v_x_2009_);
v___x_2018_ = l_Lean_ExprStructEq_hash(v_key_2011_);
v___x_2019_ = 32ULL;
v___x_2020_ = lean_uint64_shift_right(v___x_2018_, v___x_2019_);
v_fold_2021_ = lean_uint64_xor(v___x_2018_, v___x_2020_);
v___x_2022_ = 16ULL;
v___x_2023_ = lean_uint64_shift_right(v_fold_2021_, v___x_2022_);
v___x_2024_ = lean_uint64_xor(v_fold_2021_, v___x_2023_);
v___x_2025_ = lean_uint64_to_usize(v___x_2024_);
v___x_2026_ = lean_usize_of_nat(v___x_2017_);
v___x_2027_ = ((size_t)1ULL);
v___x_2028_ = lean_usize_sub(v___x_2026_, v___x_2027_);
v___x_2029_ = lean_usize_land(v___x_2025_, v___x_2028_);
v___x_2030_ = lean_array_uget_borrowed(v_x_2009_, v___x_2029_);
lean_inc(v___x_2030_);
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 2, v___x_2030_);
v___x_2032_ = v___x_2015_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_key_2011_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v_value_2012_);
lean_ctor_set(v_reuseFailAlloc_2035_, 2, v___x_2030_);
v___x_2032_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
lean_object* v___x_2033_; 
v___x_2033_ = lean_array_uset(v_x_2009_, v___x_2029_, v___x_2032_);
v_x_2009_ = v___x_2033_;
v_x_2010_ = v_tail_2013_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(lean_object* v_i_2037_, lean_object* v_source_2038_, lean_object* v_target_2039_){
_start:
{
lean_object* v___x_2040_; uint8_t v___x_2041_; 
v___x_2040_ = lean_array_get_size(v_source_2038_);
v___x_2041_ = lean_nat_dec_lt(v_i_2037_, v___x_2040_);
if (v___x_2041_ == 0)
{
lean_dec_ref(v_source_2038_);
lean_dec(v_i_2037_);
return v_target_2039_;
}
else
{
lean_object* v_es_2042_; lean_object* v___x_2043_; lean_object* v_source_2044_; lean_object* v_target_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v_es_2042_ = lean_array_fget(v_source_2038_, v_i_2037_);
v___x_2043_ = lean_box(0);
v_source_2044_ = lean_array_fset(v_source_2038_, v_i_2037_, v___x_2043_);
v_target_2045_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_target_2039_, v_es_2042_);
v___x_2046_ = lean_unsigned_to_nat(1u);
v___x_2047_ = lean_nat_add(v_i_2037_, v___x_2046_);
lean_dec(v_i_2037_);
v_i_2037_ = v___x_2047_;
v_source_2038_ = v_source_2044_;
v_target_2039_ = v_target_2045_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17___redArg(lean_object* v_data_2049_){
_start:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v_nbuckets_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2050_ = lean_array_get_size(v_data_2049_);
v___x_2051_ = lean_unsigned_to_nat(2u);
v_nbuckets_2052_ = lean_nat_mul(v___x_2050_, v___x_2051_);
v___x_2053_ = lean_unsigned_to_nat(0u);
v___x_2054_ = lean_box(0);
v___x_2055_ = lean_mk_array(v_nbuckets_2052_, v___x_2054_);
v___x_2056_ = lean_array_propagate_mark(v_data_2049_, v___x_2055_);
v___x_2057_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v___x_2053_, v_data_2049_, v___x_2056_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11___redArg(lean_object* v_m_2058_, lean_object* v_a_2059_, lean_object* v_b_2060_){
_start:
{
lean_object* v_size_2061_; lean_object* v_buckets_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2105_; 
v_size_2061_ = lean_ctor_get(v_m_2058_, 0);
v_buckets_2062_ = lean_ctor_get(v_m_2058_, 1);
v_isSharedCheck_2105_ = !lean_is_exclusive(v_m_2058_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2064_ = v_m_2058_;
v_isShared_2065_ = v_isSharedCheck_2105_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_buckets_2062_);
lean_inc(v_size_2061_);
lean_dec(v_m_2058_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2105_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2066_; uint64_t v___x_2067_; uint64_t v___x_2068_; uint64_t v___x_2069_; uint64_t v_fold_2070_; uint64_t v___x_2071_; uint64_t v___x_2072_; uint64_t v___x_2073_; size_t v___x_2074_; size_t v___x_2075_; size_t v___x_2076_; size_t v___x_2077_; size_t v___x_2078_; lean_object* v_bkt_2079_; uint8_t v___x_2080_; 
v___x_2066_ = lean_array_get_size(v_buckets_2062_);
v___x_2067_ = l_Lean_ExprStructEq_hash(v_a_2059_);
v___x_2068_ = 32ULL;
v___x_2069_ = lean_uint64_shift_right(v___x_2067_, v___x_2068_);
v_fold_2070_ = lean_uint64_xor(v___x_2067_, v___x_2069_);
v___x_2071_ = 16ULL;
v___x_2072_ = lean_uint64_shift_right(v_fold_2070_, v___x_2071_);
v___x_2073_ = lean_uint64_xor(v_fold_2070_, v___x_2072_);
v___x_2074_ = lean_uint64_to_usize(v___x_2073_);
v___x_2075_ = lean_usize_of_nat(v___x_2066_);
v___x_2076_ = ((size_t)1ULL);
v___x_2077_ = lean_usize_sub(v___x_2075_, v___x_2076_);
v___x_2078_ = lean_usize_land(v___x_2074_, v___x_2077_);
v_bkt_2079_ = lean_array_uget_borrowed(v_buckets_2062_, v___x_2078_);
v___x_2080_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2059_, v_bkt_2079_);
if (v___x_2080_ == 0)
{
lean_object* v___x_2081_; lean_object* v_size_x27_2082_; lean_object* v___x_2083_; lean_object* v_buckets_x27_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; uint8_t v___x_2090_; 
v___x_2081_ = lean_unsigned_to_nat(1u);
v_size_x27_2082_ = lean_nat_add(v_size_2061_, v___x_2081_);
lean_dec(v_size_2061_);
lean_inc(v_bkt_2079_);
v___x_2083_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2083_, 0, v_a_2059_);
lean_ctor_set(v___x_2083_, 1, v_b_2060_);
lean_ctor_set(v___x_2083_, 2, v_bkt_2079_);
v_buckets_x27_2084_ = lean_array_uset(v_buckets_2062_, v___x_2078_, v___x_2083_);
v___x_2085_ = lean_unsigned_to_nat(4u);
v___x_2086_ = lean_nat_mul(v_size_x27_2082_, v___x_2085_);
v___x_2087_ = lean_unsigned_to_nat(3u);
v___x_2088_ = lean_nat_div(v___x_2086_, v___x_2087_);
lean_dec(v___x_2086_);
v___x_2089_ = lean_array_get_size(v_buckets_x27_2084_);
v___x_2090_ = lean_nat_dec_le(v___x_2088_, v___x_2089_);
lean_dec(v___x_2088_);
if (v___x_2090_ == 0)
{
lean_object* v_val_2091_; lean_object* v___x_2093_; 
v_val_2091_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17___redArg(v_buckets_x27_2084_);
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 1, v_val_2091_);
lean_ctor_set(v___x_2064_, 0, v_size_x27_2082_);
v___x_2093_ = v___x_2064_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_size_x27_2082_);
lean_ctor_set(v_reuseFailAlloc_2094_, 1, v_val_2091_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
else
{
lean_object* v___x_2096_; 
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 1, v_buckets_x27_2084_);
lean_ctor_set(v___x_2064_, 0, v_size_x27_2082_);
v___x_2096_ = v___x_2064_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_size_x27_2082_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v_buckets_x27_2084_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
else
{
lean_object* v___x_2098_; lean_object* v_buckets_x27_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2103_; 
lean_inc(v_bkt_2079_);
v___x_2098_ = lean_box(0);
v_buckets_x27_2099_ = lean_array_uset(v_buckets_2062_, v___x_2078_, v___x_2098_);
v___x_2100_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__18___redArg(v_a_2059_, v_b_2060_, v_bkt_2079_);
v___x_2101_ = lean_array_uset(v_buckets_x27_2099_, v___x_2078_, v___x_2100_);
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 1, v___x_2101_);
v___x_2103_ = v___x_2064_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_size_2061_);
lean_ctor_set(v_reuseFailAlloc_2104_, 1, v___x_2101_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__2(lean_object* v_a_2106_, lean_object* v_e_2107_, lean_object* v_a_2108_){
_start:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2110_ = lean_st_ref_take(v_a_2106_);
v___x_2111_ = lean_box(0);
v___x_2112_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11___redArg(v___x_2110_, v_e_2107_, v_a_2108_);
v___x_2113_ = lean_st_ref_put(v_a_2106_, v___x_2112_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__2___boxed(lean_object* v_a_2114_, lean_object* v_e_2115_, lean_object* v_a_2116_, lean_object* v___y_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__2(v_a_2114_, v_e_2115_, v_a_2116_);
lean_dec(v_a_2114_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6___lam__0___boxed(lean_object* v_fvars_2119_, lean_object* v_pre_2120_, lean_object* v_post_2121_, lean_object* v_usedLetOnly_2122_, lean_object* v_skipConstInApp_2123_, lean_object* v_skipInstances_2124_, lean_object* v_body_2125_, lean_object* v_x_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_){
_start:
{
uint8_t v_usedLetOnly_boxed_2135_; uint8_t v_skipConstInApp_boxed_2136_; uint8_t v_skipInstances_boxed_2137_; lean_object* v_res_2138_; 
v_usedLetOnly_boxed_2135_ = lean_unbox(v_usedLetOnly_2122_);
v_skipConstInApp_boxed_2136_ = lean_unbox(v_skipConstInApp_2123_);
v_skipInstances_boxed_2137_ = lean_unbox(v_skipInstances_2124_);
v_res_2138_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6___lam__0(v_fvars_2119_, v_pre_2120_, v_post_2121_, v_usedLetOnly_boxed_2135_, v_skipConstInApp_boxed_2136_, v_skipInstances_boxed_2137_, v_body_2125_, v_x_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v___y_2127_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7___lam__0(lean_object* v_fvars_2142_, lean_object* v_pre_2143_, lean_object* v_post_2144_, uint8_t v_usedLetOnly_2145_, uint8_t v_skipConstInApp_2146_, uint8_t v_skipInstances_2147_, lean_object* v_body_2148_, lean_object* v_x_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2158_ = lean_array_push(v_fvars_2142_, v_x_2149_);
v___x_2159_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7(v_pre_2143_, v_post_2144_, v_usedLetOnly_2145_, v_skipConstInApp_2146_, v_skipInstances_2147_, v___x_2158_, v_body_2148_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7___lam__0___boxed(lean_object* v_fvars_2160_, lean_object* v_pre_2161_, lean_object* v_post_2162_, lean_object* v_usedLetOnly_2163_, lean_object* v_skipConstInApp_2164_, lean_object* v_skipInstances_2165_, lean_object* v_body_2166_, lean_object* v_x_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
uint8_t v_usedLetOnly_boxed_2176_; uint8_t v_skipConstInApp_boxed_2177_; uint8_t v_skipInstances_boxed_2178_; lean_object* v_res_2179_; 
v_usedLetOnly_boxed_2176_ = lean_unbox(v_usedLetOnly_2163_);
v_skipConstInApp_boxed_2177_ = lean_unbox(v_skipConstInApp_2164_);
v_skipInstances_boxed_2178_ = lean_unbox(v_skipInstances_2165_);
v_res_2179_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7___lam__0(v_fvars_2160_, v_pre_2161_, v_post_2162_, v_usedLetOnly_boxed_2176_, v_skipConstInApp_boxed_2177_, v_skipInstances_boxed_2178_, v_body_2166_, v_x_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
lean_dec(v___y_2168_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(lean_object* v_pre_2180_, lean_object* v_post_2181_, uint8_t v_usedLetOnly_2182_, uint8_t v_skipConstInApp_2183_, uint8_t v_skipInstances_2184_, lean_object* v_e_2185_, lean_object* v_a_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
lean_object* v___x_2194_; 
lean_inc_ref(v_post_2181_);
lean_inc(v___y_2192_);
lean_inc_ref(v___y_2191_);
lean_inc(v___y_2190_);
lean_inc_ref(v___y_2189_);
lean_inc(v___y_2188_);
lean_inc_ref(v___y_2187_);
lean_inc_ref(v_e_2185_);
v___x_2194_ = lean_apply_8(v_post_2181_, v_e_2185_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, lean_box(0));
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2213_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2197_ = v___x_2194_;
v_isShared_2198_ = v_isSharedCheck_2213_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_a_2195_);
lean_dec(v___x_2194_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2213_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
switch(lean_obj_tag(v_a_2195_))
{
case 0:
{
lean_object* v_e_2199_; lean_object* v___x_2201_; 
lean_dec_ref(v_e_2185_);
lean_dec_ref(v_post_2181_);
lean_dec_ref(v_pre_2180_);
v_e_2199_ = lean_ctor_get(v_a_2195_, 0);
lean_inc_ref(v_e_2199_);
lean_dec_ref_known(v_a_2195_, 1);
if (v_isShared_2198_ == 0)
{
lean_ctor_set(v___x_2197_, 0, v_e_2199_);
v___x_2201_ = v___x_2197_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_e_2199_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
case 1:
{
lean_object* v_e_2203_; lean_object* v___x_2204_; 
lean_del_object(v___x_2197_);
lean_dec_ref(v_e_2185_);
v_e_2203_ = lean_ctor_get(v_a_2195_, 0);
lean_inc_ref(v_e_2203_);
lean_dec_ref_known(v_a_2195_, 1);
v___x_2204_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2180_, v_post_2181_, v_usedLetOnly_2182_, v_skipConstInApp_2183_, v_skipInstances_2184_, v_e_2203_, v_a_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
return v___x_2204_;
}
default: 
{
lean_object* v_e_x3f_2205_; 
lean_dec_ref(v_post_2181_);
lean_dec_ref(v_pre_2180_);
v_e_x3f_2205_ = lean_ctor_get(v_a_2195_, 0);
lean_inc(v_e_x3f_2205_);
lean_dec_ref_known(v_a_2195_, 1);
if (lean_obj_tag(v_e_x3f_2205_) == 0)
{
lean_object* v___x_2207_; 
if (v_isShared_2198_ == 0)
{
lean_ctor_set(v___x_2197_, 0, v_e_2185_);
v___x_2207_ = v___x_2197_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_e_2185_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
else
{
lean_object* v_val_2209_; lean_object* v___x_2211_; 
lean_dec_ref(v_e_2185_);
v_val_2209_ = lean_ctor_get(v_e_x3f_2205_, 0);
lean_inc(v_val_2209_);
lean_dec_ref_known(v_e_x3f_2205_, 1);
if (v_isShared_2198_ == 0)
{
lean_ctor_set(v___x_2197_, 0, v_val_2209_);
v___x_2211_ = v___x_2197_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_val_2209_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
}
}
else
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
lean_dec_ref(v_e_2185_);
lean_dec_ref(v_post_2181_);
lean_dec_ref(v_pre_2180_);
v_a_2214_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___x_2194_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2194_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2219_; 
if (v_isShared_2217_ == 0)
{
v___x_2219_ = v___x_2216_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_a_2214_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7(lean_object* v_pre_2222_, lean_object* v_post_2223_, uint8_t v_usedLetOnly_2224_, uint8_t v_skipConstInApp_2225_, uint8_t v_skipInstances_2226_, lean_object* v_fvars_2227_, lean_object* v_e_2228_, lean_object* v_a_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
if (lean_obj_tag(v_e_2228_) == 6)
{
lean_object* v_binderName_2237_; lean_object* v_binderType_2238_; lean_object* v_body_2239_; uint8_t v_binderInfo_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___f_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v_binderName_2237_ = lean_ctor_get(v_e_2228_, 0);
lean_inc(v_binderName_2237_);
v_binderType_2238_ = lean_ctor_get(v_e_2228_, 1);
lean_inc_ref(v_binderType_2238_);
v_body_2239_ = lean_ctor_get(v_e_2228_, 2);
lean_inc_ref(v_body_2239_);
v_binderInfo_2240_ = lean_ctor_get_uint8(v_e_2228_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2228_, 3);
v___x_2241_ = lean_box(v_usedLetOnly_2224_);
v___x_2242_ = lean_box(v_skipConstInApp_2225_);
v___x_2243_ = lean_box(v_skipInstances_2226_);
lean_inc_ref(v_post_2223_);
lean_inc_ref(v_pre_2222_);
lean_inc_ref(v_fvars_2227_);
v___f_2244_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7___lam__0___boxed), 16, 7);
lean_closure_set(v___f_2244_, 0, v_fvars_2227_);
lean_closure_set(v___f_2244_, 1, v_pre_2222_);
lean_closure_set(v___f_2244_, 2, v_post_2223_);
lean_closure_set(v___f_2244_, 3, v___x_2241_);
lean_closure_set(v___f_2244_, 4, v___x_2242_);
lean_closure_set(v___f_2244_, 5, v___x_2243_);
lean_closure_set(v___f_2244_, 6, v_body_2239_);
v___x_2245_ = lean_expr_instantiate_rev(v_binderType_2238_, v_fvars_2227_);
lean_dec_ref(v_fvars_2227_);
lean_dec_ref(v_binderType_2238_);
v___x_2246_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2222_, v_post_2223_, v_usedLetOnly_2224_, v_skipConstInApp_2225_, v_skipInstances_2226_, v___x_2245_, v_a_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v_a_2247_; uint8_t v___x_2248_; lean_object* v___x_2249_; 
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
lean_inc(v_a_2247_);
lean_dec_ref_known(v___x_2246_, 1);
v___x_2248_ = 0;
v___x_2249_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_2237_, v_binderInfo_2240_, v_a_2247_, v___f_2244_, v___x_2248_, v_a_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
return v___x_2249_;
}
else
{
lean_dec_ref(v___f_2244_);
lean_dec(v_binderName_2237_);
return v___x_2246_;
}
}
else
{
lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2250_ = lean_expr_instantiate_rev(v_e_2228_, v_fvars_2227_);
lean_dec_ref(v_e_2228_);
lean_inc_ref(v_post_2223_);
lean_inc_ref(v_pre_2222_);
v___x_2251_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2222_, v_post_2223_, v_usedLetOnly_2224_, v_skipConstInApp_2225_, v_skipInstances_2226_, v___x_2250_, v_a_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v_a_2252_; uint8_t v___x_2253_; uint8_t v___x_2254_; uint8_t v___x_2255_; lean_object* v___x_2256_; 
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_a_2252_);
lean_dec_ref_known(v___x_2251_, 1);
v___x_2253_ = 0;
v___x_2254_ = 1;
v___x_2255_ = 1;
v___x_2256_ = l_Lean_Meta_mkLambdaFVars(v_fvars_2227_, v_a_2252_, v___x_2253_, v_usedLetOnly_2224_, v___x_2253_, v___x_2254_, v___x_2255_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
lean_dec_ref(v_fvars_2227_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_a_2257_; lean_object* v___x_2258_; 
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
lean_inc(v_a_2257_);
lean_dec_ref_known(v___x_2256_, 1);
v___x_2258_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2222_, v_post_2223_, v_usedLetOnly_2224_, v_skipConstInApp_2225_, v_skipInstances_2226_, v_a_2257_, v_a_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
return v___x_2258_;
}
else
{
lean_dec_ref(v_post_2223_);
lean_dec_ref(v_pre_2222_);
return v___x_2256_;
}
}
else
{
lean_dec_ref(v_fvars_2227_);
lean_dec_ref(v_post_2223_);
lean_dec_ref(v_pre_2222_);
return v___x_2251_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8___lam__0(lean_object* v_fvars_2259_, lean_object* v_pre_2260_, lean_object* v_post_2261_, uint8_t v_usedLetOnly_2262_, uint8_t v_skipConstInApp_2263_, uint8_t v_skipInstances_2264_, lean_object* v_body_2265_, lean_object* v_x_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2275_ = lean_array_push(v_fvars_2259_, v_x_2266_);
v___x_2276_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8(v_pre_2260_, v_post_2261_, v_usedLetOnly_2262_, v_skipConstInApp_2263_, v_skipInstances_2264_, v___x_2275_, v_body_2265_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8___lam__0___boxed(lean_object* v_fvars_2277_, lean_object* v_pre_2278_, lean_object* v_post_2279_, lean_object* v_usedLetOnly_2280_, lean_object* v_skipConstInApp_2281_, lean_object* v_skipInstances_2282_, lean_object* v_body_2283_, lean_object* v_x_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
uint8_t v_usedLetOnly_boxed_2293_; uint8_t v_skipConstInApp_boxed_2294_; uint8_t v_skipInstances_boxed_2295_; lean_object* v_res_2296_; 
v_usedLetOnly_boxed_2293_ = lean_unbox(v_usedLetOnly_2280_);
v_skipConstInApp_boxed_2294_ = lean_unbox(v_skipConstInApp_2281_);
v_skipInstances_boxed_2295_ = lean_unbox(v_skipInstances_2282_);
v_res_2296_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8___lam__0(v_fvars_2277_, v_pre_2278_, v_post_2279_, v_usedLetOnly_boxed_2293_, v_skipConstInApp_boxed_2294_, v_skipInstances_boxed_2295_, v_body_2283_, v_x_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec(v___y_2285_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8(lean_object* v_pre_2297_, lean_object* v_post_2298_, uint8_t v_usedLetOnly_2299_, uint8_t v_skipConstInApp_2300_, uint8_t v_skipInstances_2301_, lean_object* v_fvars_2302_, lean_object* v_e_2303_, lean_object* v_a_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
if (lean_obj_tag(v_e_2303_) == 8)
{
lean_object* v_declName_2312_; lean_object* v_type_2313_; lean_object* v_value_2314_; lean_object* v_body_2315_; uint8_t v_nondep_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___f_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v_declName_2312_ = lean_ctor_get(v_e_2303_, 0);
lean_inc(v_declName_2312_);
v_type_2313_ = lean_ctor_get(v_e_2303_, 1);
lean_inc_ref(v_type_2313_);
v_value_2314_ = lean_ctor_get(v_e_2303_, 2);
lean_inc_ref(v_value_2314_);
v_body_2315_ = lean_ctor_get(v_e_2303_, 3);
lean_inc_ref(v_body_2315_);
v_nondep_2316_ = lean_ctor_get_uint8(v_e_2303_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2303_, 4);
v___x_2317_ = lean_box(v_usedLetOnly_2299_);
v___x_2318_ = lean_box(v_skipConstInApp_2300_);
v___x_2319_ = lean_box(v_skipInstances_2301_);
lean_inc_ref_n(v_post_2298_, 2);
lean_inc_ref_n(v_pre_2297_, 2);
lean_inc_ref(v_fvars_2302_);
v___f_2320_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8___lam__0___boxed), 16, 7);
lean_closure_set(v___f_2320_, 0, v_fvars_2302_);
lean_closure_set(v___f_2320_, 1, v_pre_2297_);
lean_closure_set(v___f_2320_, 2, v_post_2298_);
lean_closure_set(v___f_2320_, 3, v___x_2317_);
lean_closure_set(v___f_2320_, 4, v___x_2318_);
lean_closure_set(v___f_2320_, 5, v___x_2319_);
lean_closure_set(v___f_2320_, 6, v_body_2315_);
v___x_2321_ = lean_expr_instantiate_rev(v_type_2313_, v_fvars_2302_);
lean_dec_ref(v_type_2313_);
v___x_2322_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2297_, v_post_2298_, v_usedLetOnly_2299_, v_skipConstInApp_2300_, v_skipInstances_2301_, v___x_2321_, v_a_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_object* v_a_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
lean_inc(v_a_2323_);
lean_dec_ref_known(v___x_2322_, 1);
v___x_2324_ = lean_expr_instantiate_rev(v_value_2314_, v_fvars_2302_);
lean_dec_ref(v_fvars_2302_);
lean_dec_ref(v_value_2314_);
v___x_2325_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2297_, v_post_2298_, v_usedLetOnly_2299_, v_skipConstInApp_2300_, v_skipInstances_2301_, v___x_2324_, v_a_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; uint8_t v___x_2327_; lean_object* v___x_2328_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
lean_inc(v_a_2326_);
lean_dec_ref_known(v___x_2325_, 1);
v___x_2327_ = 0;
v___x_2328_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11___redArg(v_declName_2312_, v_a_2323_, v_a_2326_, v___f_2320_, v_nondep_2316_, v___x_2327_, v_a_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
return v___x_2328_;
}
else
{
lean_dec(v_a_2323_);
lean_dec_ref(v___f_2320_);
lean_dec(v_declName_2312_);
return v___x_2325_;
}
}
else
{
lean_dec_ref(v___f_2320_);
lean_dec_ref(v_value_2314_);
lean_dec(v_declName_2312_);
lean_dec_ref(v_fvars_2302_);
lean_dec_ref(v_post_2298_);
lean_dec_ref(v_pre_2297_);
return v___x_2322_;
}
}
else
{
lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2329_ = lean_expr_instantiate_rev(v_e_2303_, v_fvars_2302_);
lean_dec_ref(v_e_2303_);
lean_inc_ref(v_post_2298_);
lean_inc_ref(v_pre_2297_);
v___x_2330_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2297_, v_post_2298_, v_usedLetOnly_2299_, v_skipConstInApp_2300_, v_skipInstances_2301_, v___x_2329_, v_a_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v_a_2331_; uint8_t v___x_2332_; uint8_t v___x_2333_; lean_object* v___x_2334_; 
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
lean_inc(v_a_2331_);
lean_dec_ref_known(v___x_2330_, 1);
v___x_2332_ = 0;
v___x_2333_ = 1;
v___x_2334_ = l_Lean_Meta_mkLetFVars(v_fvars_2302_, v_a_2331_, v_usedLetOnly_2299_, v___x_2332_, v___x_2333_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
lean_dec_ref(v_fvars_2302_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; lean_object* v___x_2336_; 
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2335_);
lean_dec_ref_known(v___x_2334_, 1);
v___x_2336_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2297_, v_post_2298_, v_usedLetOnly_2299_, v_skipConstInApp_2300_, v_skipInstances_2301_, v_a_2335_, v_a_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
return v___x_2336_;
}
else
{
lean_dec_ref(v_post_2298_);
lean_dec_ref(v_pre_2297_);
return v___x_2334_;
}
}
else
{
lean_dec_ref(v_fvars_2302_);
lean_dec_ref(v_post_2298_);
lean_dec_ref(v_pre_2297_);
return v___x_2330_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2337_; lean_object* v_dummy_2338_; 
v___x_2337_ = lean_box(0);
v_dummy_2338_ = l_Lean_Expr_sort___override(v___x_2337_);
return v_dummy_2338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__2(lean_object* v_pre_2339_, lean_object* v_post_2340_, uint8_t v_usedLetOnly_2341_, uint8_t v_skipConstInApp_2342_, uint8_t v_skipInstances_2343_, size_t v_sz_2344_, size_t v_i_2345_, lean_object* v_bs_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
uint8_t v___x_2355_; 
v___x_2355_ = lean_usize_dec_lt(v_i_2345_, v_sz_2344_);
if (v___x_2355_ == 0)
{
lean_object* v___x_2356_; 
lean_dec_ref(v_post_2340_);
lean_dec_ref(v_pre_2339_);
v___x_2356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2356_, 0, v_bs_2346_);
return v___x_2356_;
}
else
{
lean_object* v_v_2357_; lean_object* v___x_2358_; lean_object* v_bs_x27_2359_; lean_object* v___x_2360_; 
v_v_2357_ = lean_array_uget(v_bs_2346_, v_i_2345_);
v___x_2358_ = lean_unsigned_to_nat(0u);
v_bs_x27_2359_ = lean_array_uset(v_bs_2346_, v_i_2345_, v___x_2358_);
lean_inc_ref(v_post_2340_);
lean_inc_ref(v_pre_2339_);
v___x_2360_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2339_, v_post_2340_, v_usedLetOnly_2341_, v_skipConstInApp_2342_, v_skipInstances_2343_, v_v_2357_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v_a_2361_; size_t v___x_2362_; size_t v___x_2363_; lean_object* v___x_2364_; 
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
lean_inc(v_a_2361_);
lean_dec_ref_known(v___x_2360_, 1);
v___x_2362_ = ((size_t)1ULL);
v___x_2363_ = lean_usize_add(v_i_2345_, v___x_2362_);
v___x_2364_ = lean_array_uset(v_bs_x27_2359_, v_i_2345_, v_a_2361_);
v_i_2345_ = v___x_2363_;
v_bs_2346_ = v___x_2364_;
goto _start;
}
else
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2373_; 
lean_dec_ref(v_bs_x27_2359_);
lean_dec_ref(v_post_2340_);
lean_dec_ref(v_pre_2339_);
v_a_2366_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2368_ = v___x_2360_;
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2360_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2371_; 
if (v_isShared_2369_ == 0)
{
v___x_2371_ = v___x_2368_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2366_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__0(lean_object* v_pre_2374_, lean_object* v_post_2375_, uint8_t v_usedLetOnly_2376_, uint8_t v_skipConstInApp_2377_, uint8_t v_skipInstances_2378_, lean_object* v___x_2379_, lean_object* v___y_2380_, lean_object* v_b_2381_, lean_object* v_a_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
lean_object* v___x_2390_; 
v___x_2390_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2374_, v_post_2375_, v_usedLetOnly_2376_, v_skipConstInApp_2377_, v_skipInstances_2378_, v___x_2379_, v___y_2380_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2400_; 
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2393_ = v___x_2390_;
v_isShared_2394_ = v_isSharedCheck_2400_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v___x_2390_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2400_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2398_; 
v___x_2395_ = lean_array_fset(v_b_2381_, v_a_2382_, v_a_2391_);
v___x_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2395_);
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 0, v___x_2396_);
v___x_2398_ = v___x_2393_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v___x_2396_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
}
else
{
lean_object* v_a_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2408_; 
lean_dec_ref(v_b_2381_);
v_a_2401_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2403_ = v___x_2390_;
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_a_2401_);
lean_dec(v___x_2390_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2406_; 
if (v_isShared_2404_ == 0)
{
v___x_2406_ = v___x_2403_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_a_2401_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__0___boxed(lean_object* v_pre_2409_, lean_object* v_post_2410_, lean_object* v_usedLetOnly_2411_, lean_object* v_skipConstInApp_2412_, lean_object* v_skipInstances_2413_, lean_object* v___x_2414_, lean_object* v___y_2415_, lean_object* v_b_2416_, lean_object* v_a_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_){
_start:
{
uint8_t v_usedLetOnly_boxed_2425_; uint8_t v_skipConstInApp_boxed_2426_; uint8_t v_skipInstances_boxed_2427_; lean_object* v_res_2428_; 
v_usedLetOnly_boxed_2425_ = lean_unbox(v_usedLetOnly_2411_);
v_skipConstInApp_boxed_2426_ = lean_unbox(v_skipConstInApp_2412_);
v_skipInstances_boxed_2427_ = lean_unbox(v_skipInstances_2413_);
v_res_2428_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__0(v_pre_2409_, v_post_2410_, v_usedLetOnly_boxed_2425_, v_skipConstInApp_boxed_2426_, v_skipInstances_boxed_2427_, v___x_2414_, v___y_2415_, v_b_2416_, v_a_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec(v_a_2417_);
lean_dec(v___y_2415_);
return v_res_2428_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg(lean_object* v_upperBound_2429_, lean_object* v___x_2430_, lean_object* v_pre_2431_, lean_object* v_post_2432_, uint8_t v_usedLetOnly_2433_, uint8_t v_skipConstInApp_2434_, uint8_t v_skipInstances_2435_, lean_object* v_a_2436_, lean_object* v_b_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
lean_object* v___y_2447_; uint8_t v___x_2470_; 
v___x_2470_ = lean_nat_dec_lt(v_a_2436_, v_upperBound_2429_);
if (v___x_2470_ == 0)
{
lean_object* v___x_2471_; 
lean_dec(v_a_2436_);
lean_dec_ref(v_post_2432_);
lean_dec_ref(v_pre_2431_);
v___x_2471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2471_, 0, v_b_2437_);
return v___x_2471_;
}
else
{
lean_object* v___x_2472_; lean_object* v___x_2473_; uint8_t v___x_2474_; 
v___x_2472_ = lean_array_fget_borrowed(v_b_2437_, v_a_2436_);
v___x_2473_ = lean_array_get_size(v___x_2430_);
v___x_2474_ = lean_nat_dec_lt(v_a_2436_, v___x_2473_);
if (v___x_2474_ == 0)
{
lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___f_2478_; 
lean_inc(v___x_2472_);
v___x_2475_ = lean_box(v_usedLetOnly_2433_);
v___x_2476_ = lean_box(v_skipConstInApp_2434_);
v___x_2477_ = lean_box(v_skipInstances_2435_);
lean_inc(v_a_2436_);
lean_inc(v___y_2438_);
lean_inc_ref(v_post_2432_);
lean_inc_ref(v_pre_2431_);
v___f_2478_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 16, 9);
lean_closure_set(v___f_2478_, 0, v_pre_2431_);
lean_closure_set(v___f_2478_, 1, v_post_2432_);
lean_closure_set(v___f_2478_, 2, v___x_2475_);
lean_closure_set(v___f_2478_, 3, v___x_2476_);
lean_closure_set(v___f_2478_, 4, v___x_2477_);
lean_closure_set(v___f_2478_, 5, v___x_2472_);
lean_closure_set(v___f_2478_, 6, v___y_2438_);
lean_closure_set(v___f_2478_, 7, v_b_2437_);
lean_closure_set(v___f_2478_, 8, v_a_2436_);
v___y_2447_ = v___f_2478_;
goto v___jp_2446_;
}
else
{
lean_object* v___x_2479_; uint8_t v_isInstance_2480_; 
v___x_2479_ = lean_array_fget_borrowed(v___x_2430_, v_a_2436_);
v_isInstance_2480_ = lean_ctor_get_uint8(v___x_2479_, sizeof(void*)*1 + 4);
if (v_isInstance_2480_ == 0)
{
lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___f_2484_; 
lean_inc(v___x_2472_);
v___x_2481_ = lean_box(v_usedLetOnly_2433_);
v___x_2482_ = lean_box(v_skipConstInApp_2434_);
v___x_2483_ = lean_box(v_skipInstances_2435_);
lean_inc(v_a_2436_);
lean_inc(v___y_2438_);
lean_inc_ref(v_post_2432_);
lean_inc_ref(v_pre_2431_);
v___f_2484_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 16, 9);
lean_closure_set(v___f_2484_, 0, v_pre_2431_);
lean_closure_set(v___f_2484_, 1, v_post_2432_);
lean_closure_set(v___f_2484_, 2, v___x_2481_);
lean_closure_set(v___f_2484_, 3, v___x_2482_);
lean_closure_set(v___f_2484_, 4, v___x_2483_);
lean_closure_set(v___f_2484_, 5, v___x_2472_);
lean_closure_set(v___f_2484_, 6, v___y_2438_);
lean_closure_set(v___f_2484_, 7, v_b_2437_);
lean_closure_set(v___f_2484_, 8, v_a_2436_);
v___y_2447_ = v___f_2484_;
goto v___jp_2446_;
}
else
{
lean_object* v___x_2485_; lean_object* v___f_2486_; 
v___x_2485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2485_, 0, v_b_2437_);
v___f_2486_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__2___boxed), 8, 1);
lean_closure_set(v___f_2486_, 0, v___x_2485_);
v___y_2447_ = v___f_2486_;
goto v___jp_2446_;
}
}
}
v___jp_2446_:
{
lean_object* v___x_2448_; 
lean_inc(v___y_2444_);
lean_inc_ref(v___y_2443_);
lean_inc(v___y_2442_);
lean_inc_ref(v___y_2441_);
lean_inc(v___y_2440_);
lean_inc_ref(v___y_2439_);
v___x_2448_ = lean_apply_7(v___y_2447_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, lean_box(0));
if (lean_obj_tag(v___x_2448_) == 0)
{
lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2461_; 
v_a_2449_ = lean_ctor_get(v___x_2448_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2451_ = v___x_2448_;
v_isShared_2452_ = v_isSharedCheck_2461_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_dec(v___x_2448_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2461_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
if (lean_obj_tag(v_a_2449_) == 0)
{
lean_object* v_a_2453_; lean_object* v___x_2455_; 
lean_dec(v_a_2436_);
lean_dec_ref(v_post_2432_);
lean_dec_ref(v_pre_2431_);
v_a_2453_ = lean_ctor_get(v_a_2449_, 0);
lean_inc(v_a_2453_);
lean_dec_ref_known(v_a_2449_, 1);
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 0, v_a_2453_);
v___x_2455_ = v___x_2451_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_a_2453_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
else
{
lean_object* v_a_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
lean_del_object(v___x_2451_);
v_a_2457_ = lean_ctor_get(v_a_2449_, 0);
lean_inc(v_a_2457_);
lean_dec_ref_known(v_a_2449_, 1);
v___x_2458_ = lean_unsigned_to_nat(1u);
v___x_2459_ = lean_nat_add(v_a_2436_, v___x_2458_);
lean_dec(v_a_2436_);
v_a_2436_ = v___x_2459_;
v_b_2437_ = v_a_2457_;
goto _start;
}
}
}
else
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
lean_dec(v_a_2436_);
lean_dec_ref(v_post_2432_);
lean_dec_ref(v_pre_2431_);
v_a_2462_ = lean_ctor_get(v___x_2448_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2448_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2448_);
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__9(uint8_t v_skipInstances_2487_, lean_object* v_pre_2488_, lean_object* v_post_2489_, uint8_t v_usedLetOnly_2490_, uint8_t v_skipConstInApp_2491_, lean_object* v_x_2492_, lean_object* v_x_2493_, lean_object* v_x_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_){
_start:
{
lean_object* v_f_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v___y_2511_; 
if (lean_obj_tag(v_x_2492_) == 5)
{
lean_object* v_fn_2554_; lean_object* v_arg_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
v_fn_2554_ = lean_ctor_get(v_x_2492_, 0);
lean_inc_ref(v_fn_2554_);
v_arg_2555_ = lean_ctor_get(v_x_2492_, 1);
lean_inc_ref(v_arg_2555_);
lean_dec_ref_known(v_x_2492_, 2);
v___x_2556_ = lean_array_set(v_x_2493_, v_x_2494_, v_arg_2555_);
v___x_2557_ = lean_unsigned_to_nat(1u);
v___x_2558_ = lean_nat_sub(v_x_2494_, v___x_2557_);
lean_dec(v_x_2494_);
v_x_2492_ = v_fn_2554_;
v_x_2493_ = v___x_2556_;
v_x_2494_ = v___x_2558_;
goto _start;
}
else
{
lean_dec(v_x_2494_);
if (v_skipConstInApp_2491_ == 0)
{
goto v___jp_2551_;
}
else
{
uint8_t v___x_2560_; 
v___x_2560_ = l_Lean_Expr_isConst(v_x_2492_);
if (v___x_2560_ == 0)
{
goto v___jp_2551_;
}
else
{
v_f_2504_ = v_x_2492_;
v___y_2505_ = v___y_2495_;
v___y_2506_ = v___y_2496_;
v___y_2507_ = v___y_2497_;
v___y_2508_ = v___y_2498_;
v___y_2509_ = v___y_2499_;
v___y_2510_ = v___y_2500_;
v___y_2511_ = v___y_2501_;
goto v___jp_2503_;
}
}
}
v___jp_2503_:
{
if (v_skipInstances_2487_ == 0)
{
size_t v_sz_2512_; size_t v___x_2513_; lean_object* v___x_2514_; 
v_sz_2512_ = lean_array_size(v_x_2493_);
v___x_2513_ = ((size_t)0ULL);
lean_inc_ref(v_post_2489_);
lean_inc_ref(v_pre_2488_);
v___x_2514_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__2(v_pre_2488_, v_post_2489_, v_usedLetOnly_2490_, v_skipConstInApp_2491_, v_skipInstances_2487_, v_sz_2512_, v___x_2513_, v_x_2493_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v_a_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_a_2515_);
lean_dec_ref_known(v___x_2514_, 1);
v___x_2516_ = l_Lean_mkAppN(v_f_2504_, v_a_2515_);
lean_dec(v_a_2515_);
v___x_2517_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2488_, v_post_2489_, v_usedLetOnly_2490_, v_skipConstInApp_2491_, v_skipInstances_2487_, v___x_2516_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
return v___x_2517_;
}
else
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2525_; 
lean_dec_ref(v_f_2504_);
lean_dec_ref(v_post_2489_);
lean_dec_ref(v_pre_2488_);
v_a_2518_ = lean_ctor_get(v___x_2514_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2514_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2520_ = v___x_2514_;
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2514_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2521_ == 0)
{
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2518_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
else
{
lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2526_ = lean_array_get_size(v_x_2493_);
lean_inc_ref(v_f_2504_);
v___x_2527_ = l_Lean_Meta_getFunInfoNArgs(v_f_2504_, v___x_2526_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_object* v_a_2528_; lean_object* v_paramInfo_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
v_a_2528_ = lean_ctor_get(v___x_2527_, 0);
lean_inc(v_a_2528_);
lean_dec_ref_known(v___x_2527_, 1);
v_paramInfo_2529_ = lean_ctor_get(v_a_2528_, 0);
lean_inc_ref(v_paramInfo_2529_);
lean_dec(v_a_2528_);
v___x_2530_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_2489_);
lean_inc_ref(v_pre_2488_);
v___x_2531_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg(v___x_2526_, v_paramInfo_2529_, v_pre_2488_, v_post_2489_, v_usedLetOnly_2490_, v_skipConstInApp_2491_, v_skipInstances_2487_, v___x_2530_, v_x_2493_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
lean_dec_ref(v_paramInfo_2529_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v_a_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
lean_inc(v_a_2532_);
lean_dec_ref_known(v___x_2531_, 1);
v___x_2533_ = l_Lean_mkAppN(v_f_2504_, v_a_2532_);
lean_dec(v_a_2532_);
v___x_2534_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2488_, v_post_2489_, v_usedLetOnly_2490_, v_skipConstInApp_2491_, v_skipInstances_2487_, v___x_2533_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
return v___x_2534_;
}
else
{
lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2542_; 
lean_dec_ref(v_f_2504_);
lean_dec_ref(v_post_2489_);
lean_dec_ref(v_pre_2488_);
v_a_2535_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2537_ = v___x_2531_;
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_dec(v___x_2531_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2540_; 
if (v_isShared_2538_ == 0)
{
v___x_2540_ = v___x_2537_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_a_2535_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
}
else
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
lean_dec_ref(v_f_2504_);
lean_dec_ref(v_x_2493_);
lean_dec_ref(v_post_2489_);
lean_dec_ref(v_pre_2488_);
v_a_2543_ = lean_ctor_get(v___x_2527_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2545_ = v___x_2527_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2527_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2548_; 
if (v_isShared_2546_ == 0)
{
v___x_2548_ = v___x_2545_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2543_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
}
}
v___jp_2551_:
{
lean_object* v___x_2552_; 
lean_inc_ref(v_post_2489_);
lean_inc_ref(v_pre_2488_);
v___x_2552_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2488_, v_post_2489_, v_usedLetOnly_2490_, v_skipConstInApp_2491_, v_skipInstances_2487_, v_x_2492_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_a_2553_);
lean_dec_ref_known(v___x_2552_, 1);
v_f_2504_ = v_a_2553_;
v___y_2505_ = v___y_2495_;
v___y_2506_ = v___y_2496_;
v___y_2507_ = v___y_2497_;
v___y_2508_ = v___y_2498_;
v___y_2509_ = v___y_2499_;
v___y_2510_ = v___y_2500_;
v___y_2511_ = v___y_2501_;
goto v___jp_2503_;
}
else
{
lean_dec_ref(v_x_2493_);
lean_dec_ref(v_post_2489_);
lean_dec_ref(v_pre_2488_);
return v___x_2552_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1(lean_object* v___x_2561_, lean_object* v_pre_2562_, lean_object* v_e_2563_, lean_object* v_post_2564_, uint8_t v_usedLetOnly_2565_, uint8_t v_skipConstInApp_2566_, uint8_t v_skipInstances_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_){
_start:
{
lean_object* v___x_2576_; 
v___x_2576_ = l_Lean_Core_checkSystem(v___x_2561_, v___y_2573_, v___y_2574_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v___x_2577_; 
lean_dec_ref_known(v___x_2576_, 1);
lean_inc_ref(v_pre_2562_);
lean_inc(v___y_2574_);
lean_inc_ref(v___y_2573_);
lean_inc(v___y_2572_);
lean_inc_ref(v___y_2571_);
lean_inc(v___y_2570_);
lean_inc_ref(v___y_2569_);
lean_inc_ref(v_e_2563_);
v___x_2577_ = lean_apply_8(v_pre_2562_, v_e_2563_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, lean_box(0));
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2626_; 
v_a_2578_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2580_ = v___x_2577_;
v_isShared_2581_ = v_isSharedCheck_2626_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2577_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2626_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___y_2583_; 
switch(lean_obj_tag(v_a_2578_))
{
case 0:
{
lean_object* v_e_2618_; lean_object* v___x_2620_; 
lean_dec_ref(v_post_2564_);
lean_dec_ref(v_e_2563_);
lean_dec_ref(v_pre_2562_);
v_e_2618_ = lean_ctor_get(v_a_2578_, 0);
lean_inc_ref(v_e_2618_);
lean_dec_ref_known(v_a_2578_, 1);
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 0, v_e_2618_);
v___x_2620_ = v___x_2580_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_e_2618_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
case 1:
{
lean_object* v_e_2622_; lean_object* v___x_2623_; 
lean_del_object(v___x_2580_);
lean_dec_ref(v_e_2563_);
v_e_2622_ = lean_ctor_get(v_a_2578_, 0);
lean_inc_ref(v_e_2622_);
lean_dec_ref_known(v_a_2578_, 1);
v___x_2623_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2562_, v_post_2564_, v_usedLetOnly_2565_, v_skipConstInApp_2566_, v_skipInstances_2567_, v_e_2622_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
return v___x_2623_;
}
default: 
{
lean_object* v_e_x3f_2624_; 
lean_del_object(v___x_2580_);
v_e_x3f_2624_ = lean_ctor_get(v_a_2578_, 0);
lean_inc(v_e_x3f_2624_);
lean_dec_ref_known(v_a_2578_, 1);
if (lean_obj_tag(v_e_x3f_2624_) == 0)
{
v___y_2583_ = v_e_2563_;
goto v___jp_2582_;
}
else
{
lean_object* v_val_2625_; 
lean_dec_ref(v_e_2563_);
v_val_2625_ = lean_ctor_get(v_e_x3f_2624_, 0);
lean_inc(v_val_2625_);
lean_dec_ref_known(v_e_x3f_2624_, 1);
v___y_2583_ = v_val_2625_;
goto v___jp_2582_;
}
}
}
v___jp_2582_:
{
switch(lean_obj_tag(v___y_2583_))
{
case 7:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2584_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___closed__0));
v___x_2585_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6(v_pre_2562_, v_post_2564_, v_usedLetOnly_2565_, v_skipConstInApp_2566_, v_skipInstances_2567_, v___x_2584_, v___y_2583_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
return v___x_2585_;
}
case 6:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2586_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___closed__0));
v___x_2587_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7(v_pre_2562_, v_post_2564_, v_usedLetOnly_2565_, v_skipConstInApp_2566_, v_skipInstances_2567_, v___x_2586_, v___y_2583_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
return v___x_2587_;
}
case 8:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2588_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___closed__0));
v___x_2589_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8(v_pre_2562_, v_post_2564_, v_usedLetOnly_2565_, v_skipConstInApp_2566_, v_skipInstances_2567_, v___x_2588_, v___y_2583_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
return v___x_2589_;
}
case 5:
{
lean_object* v_dummy_2590_; lean_object* v_nargs_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v_dummy_2590_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___closed__1);
v_nargs_2591_ = l_Lean_Expr_getAppNumArgs(v___y_2583_);
lean_inc(v_nargs_2591_);
v___x_2592_ = lean_mk_array(v_nargs_2591_, v_dummy_2590_);
v___x_2593_ = lean_unsigned_to_nat(1u);
v___x_2594_ = lean_nat_sub(v_nargs_2591_, v___x_2593_);
lean_dec(v_nargs_2591_);
v___x_2595_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__9(v_skipInstances_2567_, v_pre_2562_, v_post_2564_, v_usedLetOnly_2565_, v_skipConstInApp_2566_, v___y_2583_, v___x_2592_, v___x_2594_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
return v___x_2595_;
}
case 10:
{
lean_object* v_data_2596_; lean_object* v_expr_2597_; lean_object* v___x_2598_; 
v_data_2596_ = lean_ctor_get(v___y_2583_, 0);
v_expr_2597_ = lean_ctor_get(v___y_2583_, 1);
lean_inc_ref(v_expr_2597_);
lean_inc_ref(v_post_2564_);
lean_inc_ref(v_pre_2562_);
v___x_2598_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2562_, v_post_2564_, v_usedLetOnly_2565_, v_skipConstInApp_2566_, v_skipInstances_2567_, v_expr_2597_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v_a_2599_; size_t v___x_2600_; size_t v___x_2601_; uint8_t v___x_2602_; 
v_a_2599_ = lean_ctor_get(v___x_2598_, 0);
lean_inc(v_a_2599_);
lean_dec_ref_known(v___x_2598_, 1);
v___x_2600_ = lean_ptr_addr(v_expr_2597_);
v___x_2601_ = lean_ptr_addr(v_a_2599_);
v___x_2602_ = lean_usize_dec_eq(v___x_2600_, v___x_2601_);
if (v___x_2602_ == 0)
{
lean_object* v___x_2603_; lean_object* v___x_2604_; 
lean_inc(v_data_2596_);
lean_dec_ref_known(v___y_2583_, 2);
v___x_2603_ = l_Lean_Expr_mdata___override(v_data_2596_, v_a_2599_);
v___x_2604_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2562_, v_post_2564_, v_usedLetOnly_2565_, v_skipConstInApp_2566_, v_skipInstances_2567_, v___x_2603_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
return v___x_2604_;
}
else
{
lean_object* v___x_2605_; 
lean_dec(v_a_2599_);
v___x_2605_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2562_, v_post_2564_, v_usedLetOnly_2565_, v_skipConstInApp_2566_, v_skipInstances_2567_, v___y_2583_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
return v___x_2605_;
}
}
else
{
lean_dec_ref_known(v___y_2583_, 2);
lean_dec_ref(v_post_2564_);
lean_dec_ref(v_pre_2562_);
return v___x_2598_;
}
}
case 11:
{
lean_object* v_typeName_2606_; lean_object* v_idx_2607_; lean_object* v_struct_2608_; lean_object* v___x_2609_; 
v_typeName_2606_ = lean_ctor_get(v___y_2583_, 0);
v_idx_2607_ = lean_ctor_get(v___y_2583_, 1);
v_struct_2608_ = lean_ctor_get(v___y_2583_, 2);
lean_inc_ref(v_struct_2608_);
lean_inc_ref(v_post_2564_);
lean_inc_ref(v_pre_2562_);
v___x_2609_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2562_, v_post_2564_, v_usedLetOnly_2565_, v_skipConstInApp_2566_, v_skipInstances_2567_, v_struct_2608_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
if (lean_obj_tag(v___x_2609_) == 0)
{
lean_object* v_a_2610_; size_t v___x_2611_; size_t v___x_2612_; uint8_t v___x_2613_; 
v_a_2610_ = lean_ctor_get(v___x_2609_, 0);
lean_inc(v_a_2610_);
lean_dec_ref_known(v___x_2609_, 1);
v___x_2611_ = lean_ptr_addr(v_struct_2608_);
v___x_2612_ = lean_ptr_addr(v_a_2610_);
v___x_2613_ = lean_usize_dec_eq(v___x_2611_, v___x_2612_);
if (v___x_2613_ == 0)
{
lean_object* v___x_2614_; lean_object* v___x_2615_; 
lean_inc(v_idx_2607_);
lean_inc(v_typeName_2606_);
lean_dec_ref_known(v___y_2583_, 3);
v___x_2614_ = l_Lean_Expr_proj___override(v_typeName_2606_, v_idx_2607_, v_a_2610_);
v___x_2615_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2562_, v_post_2564_, v_usedLetOnly_2565_, v_skipConstInApp_2566_, v_skipInstances_2567_, v___x_2614_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
return v___x_2615_;
}
else
{
lean_object* v___x_2616_; 
lean_dec(v_a_2610_);
v___x_2616_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2562_, v_post_2564_, v_usedLetOnly_2565_, v_skipConstInApp_2566_, v_skipInstances_2567_, v___y_2583_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
return v___x_2616_;
}
}
else
{
lean_dec_ref_known(v___y_2583_, 3);
lean_dec_ref(v_post_2564_);
lean_dec_ref(v_pre_2562_);
return v___x_2609_;
}
}
default: 
{
lean_object* v___x_2617_; 
v___x_2617_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2562_, v_post_2564_, v_usedLetOnly_2565_, v_skipConstInApp_2566_, v_skipInstances_2567_, v___y_2583_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
return v___x_2617_;
}
}
}
}
}
else
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2634_; 
lean_dec_ref(v_post_2564_);
lean_dec_ref(v_e_2563_);
lean_dec_ref(v_pre_2562_);
v_a_2627_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2629_ = v___x_2577_;
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2577_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2632_; 
if (v_isShared_2630_ == 0)
{
v___x_2632_ = v___x_2629_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2627_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
}
}
else
{
lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2642_; 
lean_dec_ref(v_post_2564_);
lean_dec_ref(v_e_2563_);
lean_dec_ref(v_pre_2562_);
v_a_2635_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2637_ = v___x_2576_;
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v___x_2576_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2640_; 
if (v_isShared_2638_ == 0)
{
v___x_2640_ = v___x_2637_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_a_2635_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___boxed(lean_object* v___x_2643_, lean_object* v_pre_2644_, lean_object* v_e_2645_, lean_object* v_post_2646_, lean_object* v_usedLetOnly_2647_, lean_object* v_skipConstInApp_2648_, lean_object* v_skipInstances_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_){
_start:
{
uint8_t v_usedLetOnly_boxed_2658_; uint8_t v_skipConstInApp_boxed_2659_; uint8_t v_skipInstances_boxed_2660_; lean_object* v_res_2661_; 
v_usedLetOnly_boxed_2658_ = lean_unbox(v_usedLetOnly_2647_);
v_skipConstInApp_boxed_2659_ = lean_unbox(v_skipConstInApp_2648_);
v_skipInstances_boxed_2660_ = lean_unbox(v_skipInstances_2649_);
v_res_2661_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1(v___x_2643_, v_pre_2644_, v_e_2645_, v_post_2646_, v_usedLetOnly_boxed_2658_, v_skipConstInApp_boxed_2659_, v_skipInstances_boxed_2660_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec(v___y_2650_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(lean_object* v_pre_2662_, lean_object* v_post_2663_, uint8_t v_usedLetOnly_2664_, uint8_t v_skipConstInApp_2665_, uint8_t v_skipInstances_2666_, lean_object* v_e_2667_, lean_object* v_a_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_){
_start:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; 
lean_inc(v_a_2668_);
v___x_2676_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2676_, 0, lean_box(0));
lean_closure_set(v___x_2676_, 1, lean_box(0));
lean_closure_set(v___x_2676_, 2, v_a_2668_);
v___x_2677_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__0(lean_box(0), v___x_2676_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_object* v_a_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2712_; 
v_a_2678_ = lean_ctor_get(v___x_2677_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2677_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2680_ = v___x_2677_;
v_isShared_2681_ = v_isSharedCheck_2712_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_a_2678_);
lean_dec(v___x_2677_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2712_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2682_; 
v___x_2682_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5___redArg(v_a_2678_, v_e_2667_);
lean_dec(v_a_2678_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___f_2687_; lean_object* v___x_2688_; 
lean_del_object(v___x_2680_);
v___x_2683_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___closed__0));
v___x_2684_ = lean_box(v_usedLetOnly_2664_);
v___x_2685_ = lean_box(v_skipConstInApp_2665_);
v___x_2686_ = lean_box(v_skipInstances_2666_);
lean_inc_ref(v_e_2667_);
v___f_2687_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___boxed), 15, 7);
lean_closure_set(v___f_2687_, 0, v___x_2683_);
lean_closure_set(v___f_2687_, 1, v_pre_2662_);
lean_closure_set(v___f_2687_, 2, v_e_2667_);
lean_closure_set(v___f_2687_, 3, v_post_2663_);
lean_closure_set(v___f_2687_, 4, v___x_2684_);
lean_closure_set(v___f_2687_, 5, v___x_2685_);
lean_closure_set(v___f_2687_, 6, v___x_2686_);
v___x_2688_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10___redArg(v___f_2687_, v_a_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_);
if (lean_obj_tag(v___x_2688_) == 0)
{
lean_object* v_a_2689_; lean_object* v___f_2690_; lean_object* v___x_2691_; 
v_a_2689_ = lean_ctor_get(v___x_2688_, 0);
lean_inc_n(v_a_2689_, 2);
lean_dec_ref_known(v___x_2688_, 1);
lean_inc(v_a_2668_);
v___f_2690_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2690_, 0, v_a_2668_);
lean_closure_set(v___f_2690_, 1, v_e_2667_);
lean_closure_set(v___f_2690_, 2, v_a_2689_);
v___x_2691_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__0(lean_box(0), v___f_2690_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_);
if (lean_obj_tag(v___x_2691_) == 0)
{
lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2698_; 
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2698_ == 0)
{
lean_object* v_unused_2699_; 
v_unused_2699_ = lean_ctor_get(v___x_2691_, 0);
lean_dec(v_unused_2699_);
v___x_2693_ = v___x_2691_;
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
else
{
lean_dec(v___x_2691_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2696_; 
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 0, v_a_2689_);
v___x_2696_ = v___x_2693_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_a_2689_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
else
{
lean_object* v_a_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2707_; 
lean_dec(v_a_2689_);
v_a_2700_ = lean_ctor_get(v___x_2691_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2702_ = v___x_2691_;
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_a_2700_);
lean_dec(v___x_2691_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v___x_2705_; 
if (v_isShared_2703_ == 0)
{
v___x_2705_ = v___x_2702_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_a_2700_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
}
else
{
lean_dec_ref(v_e_2667_);
return v___x_2688_;
}
}
else
{
lean_object* v_val_2708_; lean_object* v___x_2710_; 
lean_dec_ref(v_e_2667_);
lean_dec_ref(v_post_2663_);
lean_dec_ref(v_pre_2662_);
v_val_2708_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_val_2708_);
lean_dec_ref_known(v___x_2682_, 1);
if (v_isShared_2681_ == 0)
{
lean_ctor_set(v___x_2680_, 0, v_val_2708_);
v___x_2710_ = v___x_2680_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_val_2708_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
}
else
{
lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2720_; 
lean_dec_ref(v_e_2667_);
lean_dec_ref(v_post_2663_);
lean_dec_ref(v_pre_2662_);
v_a_2713_ = lean_ctor_get(v___x_2677_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2677_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2715_ = v___x_2677_;
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v___x_2677_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2718_; 
if (v_isShared_2716_ == 0)
{
v___x_2718_ = v___x_2715_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_a_2713_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6(lean_object* v_pre_2721_, lean_object* v_post_2722_, uint8_t v_usedLetOnly_2723_, uint8_t v_skipConstInApp_2724_, uint8_t v_skipInstances_2725_, lean_object* v_fvars_2726_, lean_object* v_e_2727_, lean_object* v_a_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_){
_start:
{
if (lean_obj_tag(v_e_2727_) == 7)
{
lean_object* v_binderName_2736_; lean_object* v_binderType_2737_; lean_object* v_body_2738_; uint8_t v_binderInfo_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___f_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
v_binderName_2736_ = lean_ctor_get(v_e_2727_, 0);
lean_inc(v_binderName_2736_);
v_binderType_2737_ = lean_ctor_get(v_e_2727_, 1);
lean_inc_ref(v_binderType_2737_);
v_body_2738_ = lean_ctor_get(v_e_2727_, 2);
lean_inc_ref(v_body_2738_);
v_binderInfo_2739_ = lean_ctor_get_uint8(v_e_2727_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2727_, 3);
v___x_2740_ = lean_box(v_usedLetOnly_2723_);
v___x_2741_ = lean_box(v_skipConstInApp_2724_);
v___x_2742_ = lean_box(v_skipInstances_2725_);
lean_inc_ref(v_post_2722_);
lean_inc_ref(v_pre_2721_);
lean_inc_ref(v_fvars_2726_);
v___f_2743_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6___lam__0___boxed), 16, 7);
lean_closure_set(v___f_2743_, 0, v_fvars_2726_);
lean_closure_set(v___f_2743_, 1, v_pre_2721_);
lean_closure_set(v___f_2743_, 2, v_post_2722_);
lean_closure_set(v___f_2743_, 3, v___x_2740_);
lean_closure_set(v___f_2743_, 4, v___x_2741_);
lean_closure_set(v___f_2743_, 5, v___x_2742_);
lean_closure_set(v___f_2743_, 6, v_body_2738_);
v___x_2744_ = lean_expr_instantiate_rev(v_binderType_2737_, v_fvars_2726_);
lean_dec_ref(v_fvars_2726_);
lean_dec_ref(v_binderType_2737_);
v___x_2745_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2721_, v_post_2722_, v_usedLetOnly_2723_, v_skipConstInApp_2724_, v_skipInstances_2725_, v___x_2744_, v_a_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
if (lean_obj_tag(v___x_2745_) == 0)
{
lean_object* v_a_2746_; uint8_t v___x_2747_; lean_object* v___x_2748_; 
v_a_2746_ = lean_ctor_get(v___x_2745_, 0);
lean_inc(v_a_2746_);
lean_dec_ref_known(v___x_2745_, 1);
v___x_2747_ = 0;
v___x_2748_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_2736_, v_binderInfo_2739_, v_a_2746_, v___f_2743_, v___x_2747_, v_a_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
return v___x_2748_;
}
else
{
lean_dec_ref(v___f_2743_);
lean_dec(v_binderName_2736_);
return v___x_2745_;
}
}
else
{
lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2749_ = lean_expr_instantiate_rev(v_e_2727_, v_fvars_2726_);
lean_dec_ref(v_e_2727_);
lean_inc_ref(v_post_2722_);
lean_inc_ref(v_pre_2721_);
v___x_2750_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2721_, v_post_2722_, v_usedLetOnly_2723_, v_skipConstInApp_2724_, v_skipInstances_2725_, v___x_2749_, v_a_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v_a_2751_; uint8_t v___x_2752_; uint8_t v___x_2753_; uint8_t v___x_2754_; lean_object* v___x_2755_; 
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
lean_inc(v_a_2751_);
lean_dec_ref_known(v___x_2750_, 1);
v___x_2752_ = 0;
v___x_2753_ = 1;
v___x_2754_ = 1;
v___x_2755_ = l_Lean_Meta_mkForallFVars(v_fvars_2726_, v_a_2751_, v___x_2752_, v_usedLetOnly_2723_, v___x_2753_, v___x_2754_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
lean_dec_ref(v_fvars_2726_);
if (lean_obj_tag(v___x_2755_) == 0)
{
lean_object* v_a_2756_; lean_object* v___x_2757_; 
v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
lean_inc(v_a_2756_);
lean_dec_ref_known(v___x_2755_, 1);
v___x_2757_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2721_, v_post_2722_, v_usedLetOnly_2723_, v_skipConstInApp_2724_, v_skipInstances_2725_, v_a_2756_, v_a_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
return v___x_2757_;
}
else
{
lean_dec_ref(v_post_2722_);
lean_dec_ref(v_pre_2721_);
return v___x_2755_;
}
}
else
{
lean_dec_ref(v_fvars_2726_);
lean_dec_ref(v_post_2722_);
lean_dec_ref(v_pre_2721_);
return v___x_2750_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6___lam__0(lean_object* v_fvars_2758_, lean_object* v_pre_2759_, lean_object* v_post_2760_, uint8_t v_usedLetOnly_2761_, uint8_t v_skipConstInApp_2762_, uint8_t v_skipInstances_2763_, lean_object* v_body_2764_, lean_object* v_x_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_){
_start:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; 
v___x_2774_ = lean_array_push(v_fvars_2758_, v_x_2765_);
v___x_2775_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6(v_pre_2759_, v_post_2760_, v_usedLetOnly_2761_, v_skipConstInApp_2762_, v_skipInstances_2763_, v___x_2774_, v_body_2764_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_);
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_2776_, lean_object* v_post_2777_, lean_object* v_usedLetOnly_2778_, lean_object* v_skipConstInApp_2779_, lean_object* v_skipInstances_2780_, lean_object* v_e_2781_, lean_object* v_a_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_){
_start:
{
uint8_t v_usedLetOnly_boxed_2790_; uint8_t v_skipConstInApp_boxed_2791_; uint8_t v_skipInstances_boxed_2792_; lean_object* v_res_2793_; 
v_usedLetOnly_boxed_2790_ = lean_unbox(v_usedLetOnly_2778_);
v_skipConstInApp_boxed_2791_ = lean_unbox(v_skipConstInApp_2779_);
v_skipInstances_boxed_2792_ = lean_unbox(v_skipInstances_2780_);
v_res_2793_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2776_, v_post_2777_, v_usedLetOnly_boxed_2790_, v_skipConstInApp_boxed_2791_, v_skipInstances_boxed_2792_, v_e_2781_, v_a_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
lean_dec(v___y_2788_);
lean_dec_ref(v___y_2787_);
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
lean_dec(v___y_2784_);
lean_dec_ref(v___y_2783_);
lean_dec(v_a_2782_);
return v_res_2793_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_2794_, lean_object* v_post_2795_, lean_object* v_usedLetOnly_2796_, lean_object* v_skipConstInApp_2797_, lean_object* v_skipInstances_2798_, lean_object* v_sz_2799_, lean_object* v_i_2800_, lean_object* v_bs_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_){
_start:
{
uint8_t v_usedLetOnly_boxed_2810_; uint8_t v_skipConstInApp_boxed_2811_; uint8_t v_skipInstances_boxed_2812_; size_t v_sz_boxed_2813_; size_t v_i_boxed_2814_; lean_object* v_res_2815_; 
v_usedLetOnly_boxed_2810_ = lean_unbox(v_usedLetOnly_2796_);
v_skipConstInApp_boxed_2811_ = lean_unbox(v_skipConstInApp_2797_);
v_skipInstances_boxed_2812_ = lean_unbox(v_skipInstances_2798_);
v_sz_boxed_2813_ = lean_unbox_usize(v_sz_2799_);
lean_dec(v_sz_2799_);
v_i_boxed_2814_ = lean_unbox_usize(v_i_2800_);
lean_dec(v_i_2800_);
v_res_2815_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__2(v_pre_2794_, v_post_2795_, v_usedLetOnly_boxed_2810_, v_skipConstInApp_boxed_2811_, v_skipInstances_boxed_2812_, v_sz_boxed_2813_, v_i_boxed_2814_, v_bs_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
lean_dec(v___y_2802_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___boxed(lean_object* v_pre_2816_, lean_object* v_post_2817_, lean_object* v_usedLetOnly_2818_, lean_object* v_skipConstInApp_2819_, lean_object* v_skipInstances_2820_, lean_object* v_e_2821_, lean_object* v_a_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
uint8_t v_usedLetOnly_boxed_2830_; uint8_t v_skipConstInApp_boxed_2831_; uint8_t v_skipInstances_boxed_2832_; lean_object* v_res_2833_; 
v_usedLetOnly_boxed_2830_ = lean_unbox(v_usedLetOnly_2818_);
v_skipConstInApp_boxed_2831_ = lean_unbox(v_skipConstInApp_2819_);
v_skipInstances_boxed_2832_ = lean_unbox(v_skipInstances_2820_);
v_res_2833_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2816_, v_post_2817_, v_usedLetOnly_boxed_2830_, v_skipConstInApp_boxed_2831_, v_skipInstances_boxed_2832_, v_e_2821_, v_a_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2823_);
lean_dec(v_a_2822_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6___boxed(lean_object* v_pre_2834_, lean_object* v_post_2835_, lean_object* v_usedLetOnly_2836_, lean_object* v_skipConstInApp_2837_, lean_object* v_skipInstances_2838_, lean_object* v_fvars_2839_, lean_object* v_e_2840_, lean_object* v_a_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
uint8_t v_usedLetOnly_boxed_2849_; uint8_t v_skipConstInApp_boxed_2850_; uint8_t v_skipInstances_boxed_2851_; lean_object* v_res_2852_; 
v_usedLetOnly_boxed_2849_ = lean_unbox(v_usedLetOnly_2836_);
v_skipConstInApp_boxed_2850_ = lean_unbox(v_skipConstInApp_2837_);
v_skipInstances_boxed_2851_ = lean_unbox(v_skipInstances_2838_);
v_res_2852_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6(v_pre_2834_, v_post_2835_, v_usedLetOnly_boxed_2849_, v_skipConstInApp_boxed_2850_, v_skipInstances_boxed_2851_, v_fvars_2839_, v_e_2840_, v_a_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v_a_2841_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7___boxed(lean_object* v_pre_2853_, lean_object* v_post_2854_, lean_object* v_usedLetOnly_2855_, lean_object* v_skipConstInApp_2856_, lean_object* v_skipInstances_2857_, lean_object* v_fvars_2858_, lean_object* v_e_2859_, lean_object* v_a_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_){
_start:
{
uint8_t v_usedLetOnly_boxed_2868_; uint8_t v_skipConstInApp_boxed_2869_; uint8_t v_skipInstances_boxed_2870_; lean_object* v_res_2871_; 
v_usedLetOnly_boxed_2868_ = lean_unbox(v_usedLetOnly_2855_);
v_skipConstInApp_boxed_2869_ = lean_unbox(v_skipConstInApp_2856_);
v_skipInstances_boxed_2870_ = lean_unbox(v_skipInstances_2857_);
v_res_2871_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7(v_pre_2853_, v_post_2854_, v_usedLetOnly_boxed_2868_, v_skipConstInApp_boxed_2869_, v_skipInstances_boxed_2870_, v_fvars_2858_, v_e_2859_, v_a_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_);
lean_dec(v___y_2866_);
lean_dec_ref(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2861_);
lean_dec(v_a_2860_);
return v_res_2871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8___boxed(lean_object* v_pre_2872_, lean_object* v_post_2873_, lean_object* v_usedLetOnly_2874_, lean_object* v_skipConstInApp_2875_, lean_object* v_skipInstances_2876_, lean_object* v_fvars_2877_, lean_object* v_e_2878_, lean_object* v_a_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_){
_start:
{
uint8_t v_usedLetOnly_boxed_2887_; uint8_t v_skipConstInApp_boxed_2888_; uint8_t v_skipInstances_boxed_2889_; lean_object* v_res_2890_; 
v_usedLetOnly_boxed_2887_ = lean_unbox(v_usedLetOnly_2874_);
v_skipConstInApp_boxed_2888_ = lean_unbox(v_skipConstInApp_2875_);
v_skipInstances_boxed_2889_ = lean_unbox(v_skipInstances_2876_);
v_res_2890_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8(v_pre_2872_, v_post_2873_, v_usedLetOnly_boxed_2887_, v_skipConstInApp_boxed_2888_, v_skipInstances_boxed_2889_, v_fvars_2877_, v_e_2878_, v_a_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
lean_dec(v_a_2879_);
return v_res_2890_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_2891_ = _args[0];
lean_object* v___x_2892_ = _args[1];
lean_object* v_pre_2893_ = _args[2];
lean_object* v_post_2894_ = _args[3];
lean_object* v_usedLetOnly_2895_ = _args[4];
lean_object* v_skipConstInApp_2896_ = _args[5];
lean_object* v_skipInstances_2897_ = _args[6];
lean_object* v_a_2898_ = _args[7];
lean_object* v_b_2899_ = _args[8];
lean_object* v___y_2900_ = _args[9];
lean_object* v___y_2901_ = _args[10];
lean_object* v___y_2902_ = _args[11];
lean_object* v___y_2903_ = _args[12];
lean_object* v___y_2904_ = _args[13];
lean_object* v___y_2905_ = _args[14];
lean_object* v___y_2906_ = _args[15];
lean_object* v___y_2907_ = _args[16];
_start:
{
uint8_t v_usedLetOnly_boxed_2908_; uint8_t v_skipConstInApp_boxed_2909_; uint8_t v_skipInstances_boxed_2910_; lean_object* v_res_2911_; 
v_usedLetOnly_boxed_2908_ = lean_unbox(v_usedLetOnly_2895_);
v_skipConstInApp_boxed_2909_ = lean_unbox(v_skipConstInApp_2896_);
v_skipInstances_boxed_2910_ = lean_unbox(v_skipInstances_2897_);
v_res_2911_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg(v_upperBound_2891_, v___x_2892_, v_pre_2893_, v_post_2894_, v_usedLetOnly_boxed_2908_, v_skipConstInApp_boxed_2909_, v_skipInstances_boxed_2910_, v_a_2898_, v_b_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_);
lean_dec(v___y_2906_);
lean_dec_ref(v___y_2905_);
lean_dec(v___y_2904_);
lean_dec_ref(v___y_2903_);
lean_dec(v___y_2902_);
lean_dec_ref(v___y_2901_);
lean_dec(v___y_2900_);
lean_dec_ref(v___x_2892_);
lean_dec(v_upperBound_2891_);
return v_res_2911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__9___boxed(lean_object* v_skipInstances_2912_, lean_object* v_pre_2913_, lean_object* v_post_2914_, lean_object* v_usedLetOnly_2915_, lean_object* v_skipConstInApp_2916_, lean_object* v_x_2917_, lean_object* v_x_2918_, lean_object* v_x_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
uint8_t v_skipInstances_boxed_2928_; uint8_t v_usedLetOnly_boxed_2929_; uint8_t v_skipConstInApp_boxed_2930_; lean_object* v_res_2931_; 
v_skipInstances_boxed_2928_ = lean_unbox(v_skipInstances_2912_);
v_usedLetOnly_boxed_2929_ = lean_unbox(v_usedLetOnly_2915_);
v_skipConstInApp_boxed_2930_ = lean_unbox(v_skipConstInApp_2916_);
v_res_2931_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__9(v_skipInstances_boxed_2928_, v_pre_2913_, v_post_2914_, v_usedLetOnly_boxed_2929_, v_skipConstInApp_boxed_2930_, v_x_2917_, v_x_2918_, v_x_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec(v___y_2920_);
return v_res_2931_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2932_ = lean_box(0);
v___x_2933_ = lean_unsigned_to_nat(16u);
v___x_2934_ = lean_mk_array(v___x_2933_, v___x_2932_);
return v___x_2934_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; 
v___x_2935_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__0);
v___x_2936_ = lean_unsigned_to_nat(0u);
v___x_2937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2936_);
lean_ctor_set(v___x_2937_, 1, v___x_2935_);
return v___x_2937_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__2(void){
_start:
{
lean_object* v___x_2938_; lean_object* v___x_2939_; 
v___x_2938_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__1, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__1);
v___x_2939_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2939_, 0, lean_box(0));
lean_closure_set(v___x_2939_, 1, lean_box(0));
lean_closure_set(v___x_2939_, 2, v___x_2938_);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1(lean_object* v_input_2940_, lean_object* v_pre_2941_, lean_object* v_post_2942_, uint8_t v_usedLetOnly_2943_, uint8_t v_skipConstInApp_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
uint8_t v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v_a_2955_; lean_object* v___x_2956_; 
v___x_2952_ = 0;
v___x_2953_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__2, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__2);
v___x_2954_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___lam__0(lean_box(0), v___x_2953_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
v_a_2955_ = lean_ctor_get(v___x_2954_, 0);
lean_inc(v_a_2955_);
lean_dec_ref(v___x_2954_);
v___x_2956_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2941_, v_post_2942_, v_usedLetOnly_2943_, v_skipConstInApp_2944_, v___x_2952_, v_input_2940_, v_a_2955_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_a_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2966_; 
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
lean_inc(v_a_2957_);
lean_dec_ref_known(v___x_2956_, 1);
v___x_2958_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2958_, 0, lean_box(0));
lean_closure_set(v___x_2958_, 1, lean_box(0));
lean_closure_set(v___x_2958_, 2, v_a_2955_);
v___x_2959_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___lam__0(lean_box(0), v___x_2958_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
v_isSharedCheck_2966_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_2966_ == 0)
{
lean_object* v_unused_2967_; 
v_unused_2967_ = lean_ctor_get(v___x_2959_, 0);
lean_dec(v_unused_2967_);
v___x_2961_ = v___x_2959_;
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
else
{
lean_dec(v___x_2959_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2964_; 
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 0, v_a_2957_);
v___x_2964_ = v___x_2961_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_a_2957_);
v___x_2964_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
return v___x_2964_;
}
}
}
else
{
lean_dec(v_a_2955_);
return v___x_2956_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___boxed(lean_object* v_input_2968_, lean_object* v_pre_2969_, lean_object* v_post_2970_, lean_object* v_usedLetOnly_2971_, lean_object* v_skipConstInApp_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_){
_start:
{
uint8_t v_usedLetOnly_boxed_2980_; uint8_t v_skipConstInApp_boxed_2981_; lean_object* v_res_2982_; 
v_usedLetOnly_boxed_2980_ = lean_unbox(v_usedLetOnly_2971_);
v_skipConstInApp_boxed_2981_ = lean_unbox(v_skipConstInApp_2972_);
v_res_2982_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1(v_input_2968_, v_pre_2969_, v_post_2970_, v_usedLetOnly_boxed_2980_, v_skipConstInApp_boxed_2981_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_);
lean_dec(v___y_2978_);
lean_dec_ref(v___y_2977_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2975_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
return v_res_2982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts(lean_object* v_stx_3013_, lean_object* v_expectedType_x3f_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_){
_start:
{
lean_object* v___f_3022_; lean_object* v___f_3023_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___x_3055_; 
v___f_3022_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__0));
v___f_3023_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__1));
lean_inc(v_expectedType_x3f_3014_);
v___x_3055_ = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(v_expectedType_x3f_3014_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_);
if (lean_obj_tag(v___x_3055_) == 0)
{
lean_dec_ref_known(v___x_3055_, 1);
if (lean_obj_tag(v_expectedType_x3f_3014_) == 1)
{
lean_object* v_val_3056_; lean_object* v___x_3057_; lean_object* v_a_3058_; uint8_t v___x_3059_; 
v_val_3056_ = lean_ctor_get(v_expectedType_x3f_3014_, 0);
lean_inc(v_val_3056_);
v___x_3057_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0___redArg(v_val_3056_, v_a_3018_);
v_a_3058_ = lean_ctor_get(v___x_3057_, 0);
lean_inc(v_a_3058_);
lean_dec_ref(v___x_3057_);
v___x_3059_ = l_Lean_Expr_hasExprMVar(v_a_3058_);
lean_dec(v_a_3058_);
if (v___x_3059_ == 0)
{
v___y_3025_ = v_a_3015_;
v___y_3026_ = v_a_3016_;
v___y_3027_ = v_a_3017_;
v___y_3028_ = v_a_3018_;
v___y_3029_ = v_a_3019_;
v___y_3030_ = v_a_3020_;
goto v___jp_3024_;
}
else
{
lean_object* v___x_3060_; 
v___x_3060_ = l_Lean_Elab_Term_tryPostpone(v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_);
if (lean_obj_tag(v___x_3060_) == 0)
{
lean_dec_ref_known(v___x_3060_, 1);
v___y_3025_ = v_a_3015_;
v___y_3026_ = v_a_3016_;
v___y_3027_ = v_a_3017_;
v___y_3028_ = v_a_3018_;
v___y_3029_ = v_a_3019_;
v___y_3030_ = v_a_3020_;
goto v___jp_3024_;
}
else
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3068_; 
lean_dec_ref_known(v_expectedType_x3f_3014_, 1);
v_a_3061_ = lean_ctor_get(v___x_3060_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___x_3060_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_3060_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
if (v_isShared_3064_ == 0)
{
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3061_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
}
}
else
{
v___y_3025_ = v_a_3015_;
v___y_3026_ = v_a_3016_;
v___y_3027_ = v_a_3017_;
v___y_3028_ = v_a_3018_;
v___y_3029_ = v_a_3019_;
v___y_3030_ = v_a_3020_;
goto v___jp_3024_;
}
}
else
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3076_; 
lean_dec(v_expectedType_x3f_3014_);
v_a_3069_ = lean_ctor_get(v___x_3055_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3071_ = v___x_3055_;
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_3055_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3074_; 
if (v_isShared_3072_ == 0)
{
v___x_3074_ = v___x_3071_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_a_3069_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
return v___x_3074_;
}
}
}
v___jp_3024_:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; uint8_t v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; uint8_t v___x_3037_; lean_object* v___x_3038_; 
v___x_3031_ = lean_unsigned_to_nat(1u);
v___x_3032_ = l_Lean_Syntax_getArg(v_stx_3013_, v___x_3031_);
v___x_3033_ = 1;
v___x_3034_ = lean_box(v___x_3033_);
v___x_3035_ = lean_box(v___x_3033_);
v___x_3036_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(v___x_3036_, 0, v___x_3032_);
lean_closure_set(v___x_3036_, 1, v_expectedType_x3f_3014_);
lean_closure_set(v___x_3036_, 2, v___x_3034_);
lean_closure_set(v___x_3036_, 3, v___x_3035_);
v___x_3037_ = 1;
v___x_3038_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_3036_, v___x_3037_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v_a_3039_; lean_object* v___x_3040_; lean_object* v_a_3041_; uint8_t v___x_3042_; lean_object* v___x_3043_; 
v_a_3039_ = lean_ctor_get(v___x_3038_, 0);
lean_inc(v_a_3039_);
lean_dec_ref_known(v___x_3038_, 1);
v___x_3040_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0___redArg(v_a_3039_, v___y_3028_);
v_a_3041_ = lean_ctor_get(v___x_3040_, 0);
lean_inc_n(v_a_3041_, 2);
lean_dec_ref(v___x_3040_);
v___x_3042_ = 0;
v___x_3043_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1(v_a_3041_, v___f_3023_, v___f_3022_, v___x_3042_, v___x_3042_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_);
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_object* v_a_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3054_; 
v_a_3044_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3046_ = v___x_3043_;
v_isShared_3047_ = v_isSharedCheck_3054_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_a_3044_);
lean_dec(v___x_3043_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3054_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
uint8_t v___x_3048_; 
v___x_3048_ = lean_expr_eqv(v_a_3044_, v_a_3041_);
if (v___x_3048_ == 0)
{
lean_object* v___x_3049_; lean_object* v___x_3050_; 
lean_del_object(v___x_3046_);
lean_dec(v_a_3041_);
v___x_3049_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__10));
v___x_3050_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith(v___x_3049_, v_a_3044_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_);
return v___x_3050_;
}
else
{
lean_object* v___x_3052_; 
lean_dec(v_a_3044_);
if (v_isShared_3047_ == 0)
{
lean_ctor_set(v___x_3046_, 0, v_a_3041_);
v___x_3052_ = v___x_3046_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_a_3041_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
}
}
else
{
lean_dec(v_a_3041_);
return v___x_3043_;
}
}
else
{
return v___x_3038_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts___boxed(lean_object* v_stx_3077_, lean_object* v_expectedType_x3f_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_){
_start:
{
lean_object* v_res_3086_; 
v_res_3086_ = l_Lean_Elab_Tactic_Do_elabContractEPosts(v_stx_3077_, v_expectedType_x3f_3078_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_);
lean_dec(v_a_3084_);
lean_dec_ref(v_a_3083_);
lean_dec(v_a_3082_);
lean_dec_ref(v_a_3081_);
lean_dec(v_a_3080_);
lean_dec_ref(v_a_3079_);
lean_dec(v_stx_3077_);
return v_res_3086_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4(lean_object* v_upperBound_3087_, lean_object* v___x_3088_, lean_object* v_pre_3089_, lean_object* v_post_3090_, uint8_t v_usedLetOnly_3091_, uint8_t v_skipConstInApp_3092_, uint8_t v_skipInstances_3093_, lean_object* v___x_3094_, lean_object* v_inst_3095_, lean_object* v_R_3096_, lean_object* v_a_3097_, lean_object* v_b_3098_, lean_object* v_c_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_){
_start:
{
lean_object* v___x_3108_; 
v___x_3108_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg(v_upperBound_3087_, v___x_3088_, v_pre_3089_, v_post_3090_, v_usedLetOnly_3091_, v_skipConstInApp_3092_, v_skipInstances_3093_, v_a_3097_, v_b_3098_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_);
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_3109_ = _args[0];
lean_object* v___x_3110_ = _args[1];
lean_object* v_pre_3111_ = _args[2];
lean_object* v_post_3112_ = _args[3];
lean_object* v_usedLetOnly_3113_ = _args[4];
lean_object* v_skipConstInApp_3114_ = _args[5];
lean_object* v_skipInstances_3115_ = _args[6];
lean_object* v___x_3116_ = _args[7];
lean_object* v_inst_3117_ = _args[8];
lean_object* v_R_3118_ = _args[9];
lean_object* v_a_3119_ = _args[10];
lean_object* v_b_3120_ = _args[11];
lean_object* v_c_3121_ = _args[12];
lean_object* v___y_3122_ = _args[13];
lean_object* v___y_3123_ = _args[14];
lean_object* v___y_3124_ = _args[15];
lean_object* v___y_3125_ = _args[16];
lean_object* v___y_3126_ = _args[17];
lean_object* v___y_3127_ = _args[18];
lean_object* v___y_3128_ = _args[19];
lean_object* v___y_3129_ = _args[20];
_start:
{
uint8_t v_usedLetOnly_boxed_3130_; uint8_t v_skipConstInApp_boxed_3131_; uint8_t v_skipInstances_boxed_3132_; lean_object* v_res_3133_; 
v_usedLetOnly_boxed_3130_ = lean_unbox(v_usedLetOnly_3113_);
v_skipConstInApp_boxed_3131_ = lean_unbox(v_skipConstInApp_3114_);
v_skipInstances_boxed_3132_ = lean_unbox(v_skipInstances_3115_);
v_res_3133_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4(v_upperBound_3109_, v___x_3110_, v_pre_3111_, v_post_3112_, v_usedLetOnly_boxed_3130_, v_skipConstInApp_boxed_3131_, v_skipInstances_boxed_3132_, v___x_3116_, v_inst_3117_, v_R_3118_, v_a_3119_, v_b_3120_, v_c_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
lean_dec(v___y_3126_);
lean_dec_ref(v___y_3125_);
lean_dec(v___y_3124_);
lean_dec_ref(v___y_3123_);
lean_dec(v___y_3122_);
lean_dec(v___x_3116_);
lean_dec_ref(v___x_3110_);
lean_dec(v_upperBound_3109_);
return v_res_3133_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5(lean_object* v_00_u03b2_3134_, lean_object* v_m_3135_, lean_object* v_a_3136_){
_start:
{
lean_object* v___x_3137_; 
v___x_3137_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5___redArg(v_m_3135_, v_a_3136_);
return v___x_3137_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5___boxed(lean_object* v_00_u03b2_3138_, lean_object* v_m_3139_, lean_object* v_a_3140_){
_start:
{
lean_object* v_res_3141_; 
v_res_3141_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5(v_00_u03b2_3138_, v_m_3139_, v_a_3140_);
lean_dec_ref(v_a_3140_);
lean_dec_ref(v_m_3139_);
return v_res_3141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8(lean_object* v_00_u03b1_3142_, lean_object* v_name_3143_, uint8_t v_bi_3144_, lean_object* v_type_3145_, lean_object* v_k_3146_, uint8_t v_kind_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_){
_start:
{
lean_object* v___x_3156_; 
v___x_3156_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg(v_name_3143_, v_bi_3144_, v_type_3145_, v_k_3146_, v_kind_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
return v___x_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___boxed(lean_object* v_00_u03b1_3157_, lean_object* v_name_3158_, lean_object* v_bi_3159_, lean_object* v_type_3160_, lean_object* v_k_3161_, lean_object* v_kind_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
uint8_t v_bi_boxed_3171_; uint8_t v_kind_boxed_3172_; lean_object* v_res_3173_; 
v_bi_boxed_3171_ = lean_unbox(v_bi_3159_);
v_kind_boxed_3172_ = lean_unbox(v_kind_3162_);
v_res_3173_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8(v_00_u03b1_3157_, v_name_3158_, v_bi_boxed_3171_, v_type_3160_, v_k_3161_, v_kind_boxed_3172_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3163_);
return v_res_3173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11(lean_object* v_00_u03b1_3174_, lean_object* v_name_3175_, lean_object* v_type_3176_, lean_object* v_val_3177_, lean_object* v_k_3178_, uint8_t v_nondep_3179_, uint8_t v_kind_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
lean_object* v___x_3189_; 
v___x_3189_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11___redArg(v_name_3175_, v_type_3176_, v_val_3177_, v_k_3178_, v_nondep_3179_, v_kind_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
return v___x_3189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11___boxed(lean_object* v_00_u03b1_3190_, lean_object* v_name_3191_, lean_object* v_type_3192_, lean_object* v_val_3193_, lean_object* v_k_3194_, lean_object* v_nondep_3195_, lean_object* v_kind_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_){
_start:
{
uint8_t v_nondep_boxed_3205_; uint8_t v_kind_boxed_3206_; lean_object* v_res_3207_; 
v_nondep_boxed_3205_ = lean_unbox(v_nondep_3195_);
v_kind_boxed_3206_ = lean_unbox(v_kind_3196_);
v_res_3207_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11(v_00_u03b1_3190_, v_name_3191_, v_type_3192_, v_val_3193_, v_k_3194_, v_nondep_boxed_3205_, v_kind_boxed_3206_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
lean_dec(v___y_3201_);
lean_dec_ref(v___y_3200_);
lean_dec(v___y_3199_);
lean_dec_ref(v___y_3198_);
lean_dec(v___y_3197_);
return v_res_3207_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14(lean_object* v_00_u03b1_3208_, lean_object* v_ref_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_){
_start:
{
lean_object* v___x_3215_; 
v___x_3215_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_3209_);
return v___x_3215_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___boxed(lean_object* v_00_u03b1_3216_, lean_object* v_ref_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_){
_start:
{
lean_object* v_res_3223_; 
v_res_3223_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14(v_00_u03b1_3216_, v_ref_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_);
lean_dec(v___y_3221_);
lean_dec_ref(v___y_3220_);
lean_dec(v___y_3219_);
lean_dec_ref(v___y_3218_);
return v_res_3223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10(lean_object* v_00_u03b1_3224_, lean_object* v_x_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
lean_object* v___x_3234_; 
v___x_3234_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10___redArg(v_x_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
return v___x_3234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10___boxed(lean_object* v_00_u03b1_3235_, lean_object* v_x_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_){
_start:
{
lean_object* v_res_3245_; 
v_res_3245_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10(v_00_u03b1_3235_, v_x_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
lean_dec(v___y_3239_);
lean_dec_ref(v___y_3238_);
lean_dec(v___y_3237_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11(lean_object* v_00_u03b2_3246_, lean_object* v_m_3247_, lean_object* v_a_3248_, lean_object* v_b_3249_){
_start:
{
lean_object* v___x_3250_; 
v___x_3250_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11___redArg(v_m_3247_, v_a_3248_, v_b_3249_);
return v___x_3250_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5_spec__6(lean_object* v_00_u03b2_3251_, lean_object* v_a_3252_, lean_object* v_x_3253_){
_start:
{
lean_object* v___x_3254_; 
v___x_3254_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5_spec__6___redArg(v_a_3252_, v_x_3253_);
return v___x_3254_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5_spec__6___boxed(lean_object* v_00_u03b2_3255_, lean_object* v_a_3256_, lean_object* v_x_3257_){
_start:
{
lean_object* v_res_3258_; 
v_res_3258_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5_spec__6(v_00_u03b2_3255_, v_a_3256_, v_x_3257_);
lean_dec(v_x_3257_);
lean_dec_ref(v_a_3256_);
return v_res_3258_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16(lean_object* v_00_u03b2_3259_, lean_object* v_a_3260_, lean_object* v_x_3261_){
_start:
{
uint8_t v___x_3262_; 
v___x_3262_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16___redArg(v_a_3260_, v_x_3261_);
return v___x_3262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16___boxed(lean_object* v_00_u03b2_3263_, lean_object* v_a_3264_, lean_object* v_x_3265_){
_start:
{
uint8_t v_res_3266_; lean_object* v_r_3267_; 
v_res_3266_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16(v_00_u03b2_3263_, v_a_3264_, v_x_3265_);
lean_dec(v_x_3265_);
lean_dec_ref(v_a_3264_);
v_r_3267_ = lean_box(v_res_3266_);
return v_r_3267_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17(lean_object* v_00_u03b2_3268_, lean_object* v_data_3269_){
_start:
{
lean_object* v___x_3270_; 
v___x_3270_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17___redArg(v_data_3269_);
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__18(lean_object* v_00_u03b2_3271_, lean_object* v_a_3272_, lean_object* v_b_3273_, lean_object* v_x_3274_){
_start:
{
lean_object* v___x_3275_; 
v___x_3275_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__18___redArg(v_a_3272_, v_b_3273_, v_x_3274_);
return v___x_3275_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17_spec__18(lean_object* v_00_u03b2_3276_, lean_object* v_i_3277_, lean_object* v_source_3278_, lean_object* v_target_3279_){
_start:
{
lean_object* v___x_3280_; 
v___x_3280_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v_i_3277_, v_source_3278_, v_target_3279_);
return v___x_3280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19(lean_object* v_00_u03b2_3281_, lean_object* v_x_3282_, lean_object* v_x_3283_){
_start:
{
lean_object* v___x_3284_; 
v___x_3284_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_x_3282_, v_x_3283_);
return v___x_3284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1(){
_start:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3298_ = l_Lean_Elab_Term_termElabAttribute;
v___x_3299_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___closed__0));
v___x_3300_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___closed__2));
v___x_3301_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elabContractEPosts___boxed), 9, 0);
v___x_3302_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3298_, v___x_3299_, v___x_3300_, v___x_3301_);
return v___x_3302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___boxed(lean_object* v_a_3303_){
_start:
{
lean_object* v_res_3304_; 
v_res_3304_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1();
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts_docString__3(){
_start:
{
lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; 
v___x_3307_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___closed__2));
v___x_3308_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts_docString__3___closed__0));
v___x_3309_ = l_Lean_addBuiltinDocString(v___x_3307_, v___x_3308_);
return v___x_3309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts_docString__3___boxed(lean_object* v_a_3310_){
_start:
{
lean_object* v_res_3311_; 
v_res_3311_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts_docString__3();
return v_res_3311_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0(uint8_t v_suppressElabErrors_3313_, lean_object* v_x_3314_){
_start:
{
if (lean_obj_tag(v_x_3314_) == 1)
{
lean_object* v_pre_3315_; 
v_pre_3315_ = lean_ctor_get(v_x_3314_, 0);
if (lean_obj_tag(v_pre_3315_) == 0)
{
lean_object* v_str_3316_; lean_object* v___x_3317_; uint8_t v___x_3318_; 
v_str_3316_ = lean_ctor_get(v_x_3314_, 1);
v___x_3317_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0___closed__0));
v___x_3318_ = lean_string_dec_eq(v_str_3316_, v___x_3317_);
if (v___x_3318_ == 0)
{
return v___x_3318_;
}
else
{
return v_suppressElabErrors_3313_;
}
}
else
{
uint8_t v___x_3319_; 
v___x_3319_ = 0;
return v___x_3319_;
}
}
else
{
uint8_t v___x_3320_; 
v___x_3320_ = 0;
return v___x_3320_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0___boxed(lean_object* v_suppressElabErrors_3321_, lean_object* v_x_3322_){
_start:
{
uint8_t v_suppressElabErrors_boxed_3323_; uint8_t v_res_3324_; lean_object* v_r_3325_; 
v_suppressElabErrors_boxed_3323_ = lean_unbox(v_suppressElabErrors_3321_);
v_res_3324_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0(v_suppressElabErrors_boxed_3323_, v_x_3322_);
lean_dec(v_x_3322_);
v_r_3325_ = lean_box(v_res_3324_);
return v_r_3325_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0(lean_object* v_opts_3326_, lean_object* v_opt_3327_){
_start:
{
lean_object* v_name_3328_; lean_object* v_defValue_3329_; lean_object* v_map_3330_; lean_object* v___x_3331_; 
v_name_3328_ = lean_ctor_get(v_opt_3327_, 0);
v_defValue_3329_ = lean_ctor_get(v_opt_3327_, 1);
v_map_3330_ = lean_ctor_get(v_opts_3326_, 0);
v___x_3331_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3330_, v_name_3328_);
if (lean_obj_tag(v___x_3331_) == 0)
{
uint8_t v___x_3332_; 
v___x_3332_ = lean_unbox(v_defValue_3329_);
return v___x_3332_;
}
else
{
lean_object* v_val_3333_; 
v_val_3333_ = lean_ctor_get(v___x_3331_, 0);
lean_inc(v_val_3333_);
lean_dec_ref_known(v___x_3331_, 1);
if (lean_obj_tag(v_val_3333_) == 1)
{
uint8_t v_v_3334_; 
v_v_3334_ = lean_ctor_get_uint8(v_val_3333_, 0);
lean_dec_ref_known(v_val_3333_, 0);
return v_v_3334_;
}
else
{
uint8_t v___x_3335_; 
lean_dec(v_val_3333_);
v___x_3335_ = lean_unbox(v_defValue_3329_);
return v___x_3335_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0___boxed(lean_object* v_opts_3336_, lean_object* v_opt_3337_){
_start:
{
uint8_t v_res_3338_; lean_object* v_r_3339_; 
v_res_3338_ = l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0(v_opts_3336_, v_opt_3337_);
lean_dec_ref(v_opt_3337_);
lean_dec_ref(v_opts_3336_);
v_r_3339_ = lean_box(v_res_3338_);
return v_r_3339_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3340_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0);
v___x_3341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3340_);
return v___x_3341_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3342_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__0);
v___x_3343_ = lean_unsigned_to_nat(0u);
v___x_3344_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3343_);
lean_ctor_set(v___x_3344_, 1, v___x_3343_);
lean_ctor_set(v___x_3344_, 2, v___x_3343_);
lean_ctor_set(v___x_3344_, 3, v___x_3343_);
lean_ctor_set(v___x_3344_, 4, v___x_3342_);
lean_ctor_set(v___x_3344_, 5, v___x_3342_);
lean_ctor_set(v___x_3344_, 6, v___x_3342_);
lean_ctor_set(v___x_3344_, 7, v___x_3342_);
lean_ctor_set(v___x_3344_, 8, v___x_3342_);
lean_ctor_set(v___x_3344_, 9, v___x_3342_);
lean_ctor_set(v___x_3344_, 10, v___x_3342_);
return v___x_3344_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3345_ = lean_unsigned_to_nat(32u);
v___x_3346_ = lean_mk_empty_array_with_capacity(v___x_3345_);
v___x_3347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3346_);
return v___x_3347_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__3(void){
_start:
{
size_t v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; 
v___x_3348_ = ((size_t)5ULL);
v___x_3349_ = lean_unsigned_to_nat(0u);
v___x_3350_ = lean_unsigned_to_nat(32u);
v___x_3351_ = lean_mk_empty_array_with_capacity(v___x_3350_);
v___x_3352_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__2);
v___x_3353_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3353_, 0, v___x_3352_);
lean_ctor_set(v___x_3353_, 1, v___x_3351_);
lean_ctor_set(v___x_3353_, 2, v___x_3349_);
lean_ctor_set(v___x_3353_, 3, v___x_3349_);
lean_ctor_set_usize(v___x_3353_, 4, v___x_3348_);
return v___x_3353_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__4(void){
_start:
{
lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; 
v___x_3354_ = lean_box(1);
v___x_3355_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__3);
v___x_3356_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__0);
v___x_3357_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3356_);
lean_ctor_set(v___x_3357_, 1, v___x_3355_);
lean_ctor_set(v___x_3357_, 2, v___x_3354_);
return v___x_3357_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_msgData_3358_, lean_object* v___y_3359_){
_start:
{
lean_object* v___x_3361_; lean_object* v_env_3362_; uint8_t v___x_3363_; lean_object* v_env_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v_scopes_3367_; lean_object* v___x_3368_; lean_object* v_opts_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; 
v___x_3361_ = lean_st_ref_get(v___y_3359_);
v_env_3362_ = lean_ctor_get(v___x_3361_, 0);
lean_inc_ref(v_env_3362_);
lean_dec(v___x_3361_);
v___x_3363_ = 0;
v_env_3364_ = l_Lean_Environment_setRecordingDeps(v_env_3362_, v___x_3363_);
v___x_3365_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3366_ = lean_st_ref_get(v___y_3359_);
v_scopes_3367_ = lean_ctor_get(v___x_3366_, 2);
lean_inc(v_scopes_3367_);
lean_dec(v___x_3366_);
v___x_3368_ = l_List_head_x21___redArg(v___x_3365_, v_scopes_3367_);
lean_dec(v_scopes_3367_);
v_opts_3369_ = lean_ctor_get(v___x_3368_, 1);
lean_inc_ref(v_opts_3369_);
lean_dec(v___x_3368_);
v___x_3370_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__1);
v___x_3371_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__4);
v___x_3372_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3372_, 0, v_env_3364_);
lean_ctor_set(v___x_3372_, 1, v___x_3370_);
lean_ctor_set(v___x_3372_, 2, v___x_3371_);
lean_ctor_set(v___x_3372_, 3, v_opts_3369_);
v___x_3373_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3373_, 0, v___x_3372_);
lean_ctor_set(v___x_3373_, 1, v_msgData_3358_);
v___x_3374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3373_);
return v___x_3374_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_msgData_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_){
_start:
{
lean_object* v_res_3378_; 
v_res_3378_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg(v_msgData_3375_, v___y_3376_);
lean_dec(v___y_3376_);
return v_res_3378_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2(lean_object* v_ref_3379_, lean_object* v_msgData_3380_, uint8_t v_severity_3381_, uint8_t v_isSilent_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_){
_start:
{
lean_object* v___y_3387_; uint8_t v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; uint8_t v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3452_; uint8_t v___y_3453_; uint8_t v___y_3454_; lean_object* v___y_3455_; uint8_t v___y_3478_; uint8_t v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; uint8_t v___y_3485_; uint8_t v___y_3486_; uint8_t v___x_3501_; uint8_t v___y_3503_; uint8_t v___x_3513_; 
v___x_3501_ = 2;
v___x_3513_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3381_, v___x_3501_);
if (v___x_3513_ == 0)
{
v___y_3503_ = v___x_3513_;
goto v___jp_3502_;
}
else
{
uint8_t v___x_3514_; 
lean_inc_ref(v_msgData_3380_);
v___x_3514_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3380_);
if (v___x_3514_ == 0)
{
v___y_3503_ = v___x_3514_;
goto v___jp_3502_;
}
else
{
lean_object* v___x_3515_; lean_object* v___x_3516_; 
lean_dec_ref(v_msgData_3380_);
v___x_3515_ = lean_box(0);
v___x_3516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3516_, 0, v___x_3515_);
return v___x_3516_;
}
}
v___jp_3386_:
{
lean_object* v___x_3395_; 
v___x_3395_ = l_Lean_Elab_Command_getScope___redArg(v___y_3394_);
if (lean_obj_tag(v___x_3395_) == 0)
{
lean_object* v_a_3396_; lean_object* v_currNamespace_3397_; lean_object* v___x_3398_; 
v_a_3396_ = lean_ctor_get(v___x_3395_, 0);
lean_inc(v_a_3396_);
lean_dec_ref_known(v___x_3395_, 1);
v_currNamespace_3397_ = lean_ctor_get(v_a_3396_, 2);
lean_inc(v_currNamespace_3397_);
lean_dec(v_a_3396_);
v___x_3398_ = l_Lean_Elab_Command_getScope___redArg(v___y_3394_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v_a_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3434_; 
v_a_3399_ = lean_ctor_get(v___x_3398_, 0);
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3401_ = v___x_3398_;
v_isShared_3402_ = v_isSharedCheck_3434_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_a_3399_);
lean_dec(v___x_3398_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3434_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v_openDecls_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v_env_3408_; lean_object* v_messages_3409_; lean_object* v_scopes_3410_; lean_object* v_usedQuotCtxts_3411_; lean_object* v_nextMacroScope_3412_; lean_object* v_maxRecDepth_3413_; lean_object* v_ngen_3414_; lean_object* v_auxDeclNGen_3415_; lean_object* v_infoState_3416_; lean_object* v_traceState_3417_; lean_object* v_snapshotTasks_3418_; lean_object* v_prevLinterStates_3419_; lean_object* v_codeQualityEntryTasks_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3433_; 
v_openDecls_3403_ = lean_ctor_get(v_a_3399_, 3);
lean_inc(v_openDecls_3403_);
lean_dec(v_a_3399_);
v___x_3404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3404_, 0, v_currNamespace_3397_);
lean_ctor_set(v___x_3404_, 1, v_openDecls_3403_);
v___x_3405_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3404_);
lean_ctor_set(v___x_3405_, 1, v___y_3390_);
lean_inc_ref(v___y_3387_);
lean_inc_ref(v___y_3389_);
v___x_3406_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3406_, 0, v___y_3389_);
lean_ctor_set(v___x_3406_, 1, v___y_3392_);
lean_ctor_set(v___x_3406_, 2, v___y_3393_);
lean_ctor_set(v___x_3406_, 3, v___y_3387_);
lean_ctor_set(v___x_3406_, 4, v___x_3405_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*5, v___y_3388_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*5 + 1, v___y_3391_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*5 + 2, v_isSilent_3382_);
v___x_3407_ = lean_st_ref_take(v___y_3394_);
v_env_3408_ = lean_ctor_get(v___x_3407_, 0);
v_messages_3409_ = lean_ctor_get(v___x_3407_, 1);
v_scopes_3410_ = lean_ctor_get(v___x_3407_, 2);
v_usedQuotCtxts_3411_ = lean_ctor_get(v___x_3407_, 3);
v_nextMacroScope_3412_ = lean_ctor_get(v___x_3407_, 4);
v_maxRecDepth_3413_ = lean_ctor_get(v___x_3407_, 5);
v_ngen_3414_ = lean_ctor_get(v___x_3407_, 6);
v_auxDeclNGen_3415_ = lean_ctor_get(v___x_3407_, 7);
v_infoState_3416_ = lean_ctor_get(v___x_3407_, 8);
v_traceState_3417_ = lean_ctor_get(v___x_3407_, 9);
v_snapshotTasks_3418_ = lean_ctor_get(v___x_3407_, 10);
v_prevLinterStates_3419_ = lean_ctor_get(v___x_3407_, 11);
v_codeQualityEntryTasks_3420_ = lean_ctor_get(v___x_3407_, 12);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3422_ = v___x_3407_;
v_isShared_3423_ = v_isSharedCheck_3433_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3420_);
lean_inc(v_prevLinterStates_3419_);
lean_inc(v_snapshotTasks_3418_);
lean_inc(v_traceState_3417_);
lean_inc(v_infoState_3416_);
lean_inc(v_auxDeclNGen_3415_);
lean_inc(v_ngen_3414_);
lean_inc(v_maxRecDepth_3413_);
lean_inc(v_nextMacroScope_3412_);
lean_inc(v_usedQuotCtxts_3411_);
lean_inc(v_scopes_3410_);
lean_inc(v_messages_3409_);
lean_inc(v_env_3408_);
lean_dec(v___x_3407_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3433_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3427_; 
v___x_3424_ = lean_box(0);
v___x_3425_ = l_Lean_MessageLog_add(v___x_3406_, v_messages_3409_);
if (v_isShared_3423_ == 0)
{
lean_ctor_set(v___x_3422_, 1, v___x_3425_);
v___x_3427_ = v___x_3422_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_env_3408_);
lean_ctor_set(v_reuseFailAlloc_3432_, 1, v___x_3425_);
lean_ctor_set(v_reuseFailAlloc_3432_, 2, v_scopes_3410_);
lean_ctor_set(v_reuseFailAlloc_3432_, 3, v_usedQuotCtxts_3411_);
lean_ctor_set(v_reuseFailAlloc_3432_, 4, v_nextMacroScope_3412_);
lean_ctor_set(v_reuseFailAlloc_3432_, 5, v_maxRecDepth_3413_);
lean_ctor_set(v_reuseFailAlloc_3432_, 6, v_ngen_3414_);
lean_ctor_set(v_reuseFailAlloc_3432_, 7, v_auxDeclNGen_3415_);
lean_ctor_set(v_reuseFailAlloc_3432_, 8, v_infoState_3416_);
lean_ctor_set(v_reuseFailAlloc_3432_, 9, v_traceState_3417_);
lean_ctor_set(v_reuseFailAlloc_3432_, 10, v_snapshotTasks_3418_);
lean_ctor_set(v_reuseFailAlloc_3432_, 11, v_prevLinterStates_3419_);
lean_ctor_set(v_reuseFailAlloc_3432_, 12, v_codeQualityEntryTasks_3420_);
v___x_3427_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
lean_object* v___x_3428_; lean_object* v___x_3430_; 
v___x_3428_ = lean_st_ref_put(v___y_3394_, v___x_3427_);
if (v_isShared_3402_ == 0)
{
lean_ctor_set(v___x_3401_, 0, v___x_3424_);
v___x_3430_ = v___x_3401_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3424_);
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
}
else
{
lean_object* v_a_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3442_; 
lean_dec(v_currNamespace_3397_);
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
lean_dec_ref(v___y_3390_);
v_a_3435_ = lean_ctor_get(v___x_3398_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3437_ = v___x_3398_;
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_a_3435_);
lean_dec(v___x_3398_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3440_; 
if (v_isShared_3438_ == 0)
{
v___x_3440_ = v___x_3437_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_a_3435_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
}
}
else
{
lean_object* v_a_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3450_; 
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
lean_dec_ref(v___y_3390_);
v_a_3443_ = lean_ctor_get(v___x_3395_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3445_ = v___x_3395_;
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_a_3443_);
lean_dec(v___x_3395_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3448_; 
if (v_isShared_3446_ == 0)
{
v___x_3448_ = v___x_3445_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_a_3443_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
return v___x_3448_;
}
}
}
}
v___jp_3451_:
{
lean_object* v_fileName_3456_; lean_object* v_fileMap_3457_; uint8_t v_suppressElabErrors_3458_; lean_object* v___x_3459_; lean_object* v___f_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v_a_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3476_; 
v_fileName_3456_ = lean_ctor_get(v___y_3383_, 0);
v_fileMap_3457_ = lean_ctor_get(v___y_3383_, 1);
v_suppressElabErrors_3458_ = lean_ctor_get_uint8(v___y_3383_, sizeof(void*)*10);
v___x_3459_ = lean_box(v_suppressElabErrors_3458_);
v___f_3460_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3460_, 0, v___x_3459_);
v___x_3461_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3380_);
v___x_3462_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg(v___x_3461_, v___y_3384_);
v_a_3463_ = lean_ctor_get(v___x_3462_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3465_ = v___x_3462_;
v_isShared_3466_ = v_isSharedCheck_3476_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___x_3462_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3476_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
lean_inc_ref_n(v_fileMap_3457_, 2);
v___x_3467_ = l_Lean_FileMap_toPosition(v_fileMap_3457_, v___y_3452_);
lean_dec(v___y_3452_);
v___x_3468_ = l_Lean_FileMap_toPosition(v_fileMap_3457_, v___y_3455_);
lean_dec(v___y_3455_);
v___x_3469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3468_);
v___x_3470_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__19));
if (v_suppressElabErrors_3458_ == 0)
{
lean_del_object(v___x_3465_);
lean_dec_ref(v___f_3460_);
v___y_3387_ = v___x_3470_;
v___y_3388_ = v___y_3453_;
v___y_3389_ = v_fileName_3456_;
v___y_3390_ = v_a_3463_;
v___y_3391_ = v___y_3454_;
v___y_3392_ = v___x_3467_;
v___y_3393_ = v___x_3469_;
v___y_3394_ = v___y_3384_;
goto v___jp_3386_;
}
else
{
uint8_t v___x_3471_; 
lean_inc(v_a_3463_);
v___x_3471_ = l_Lean_MessageData_hasTag(v___f_3460_, v_a_3463_);
if (v___x_3471_ == 0)
{
lean_object* v___x_3472_; lean_object* v___x_3474_; 
lean_dec_ref_known(v___x_3469_, 1);
lean_dec_ref(v___x_3467_);
lean_dec(v_a_3463_);
v___x_3472_ = lean_box(0);
if (v_isShared_3466_ == 0)
{
lean_ctor_set(v___x_3465_, 0, v___x_3472_);
v___x_3474_ = v___x_3465_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v___x_3472_);
v___x_3474_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
return v___x_3474_;
}
}
else
{
lean_del_object(v___x_3465_);
v___y_3387_ = v___x_3470_;
v___y_3388_ = v___y_3453_;
v___y_3389_ = v_fileName_3456_;
v___y_3390_ = v_a_3463_;
v___y_3391_ = v___y_3454_;
v___y_3392_ = v___x_3467_;
v___y_3393_ = v___x_3469_;
v___y_3394_ = v___y_3384_;
goto v___jp_3386_;
}
}
}
}
v___jp_3477_:
{
lean_object* v___x_3482_; 
v___x_3482_ = l_Lean_Syntax_getTailPos_x3f(v___y_3480_, v___y_3478_);
lean_dec(v___y_3480_);
if (lean_obj_tag(v___x_3482_) == 0)
{
lean_inc(v___y_3481_);
v___y_3452_ = v___y_3481_;
v___y_3453_ = v___y_3478_;
v___y_3454_ = v___y_3479_;
v___y_3455_ = v___y_3481_;
goto v___jp_3451_;
}
else
{
lean_object* v_val_3483_; 
v_val_3483_ = lean_ctor_get(v___x_3482_, 0);
lean_inc(v_val_3483_);
lean_dec_ref_known(v___x_3482_, 1);
v___y_3452_ = v___y_3481_;
v___y_3453_ = v___y_3478_;
v___y_3454_ = v___y_3479_;
v___y_3455_ = v_val_3483_;
goto v___jp_3451_;
}
}
v___jp_3484_:
{
lean_object* v___x_3487_; 
v___x_3487_ = l_Lean_Elab_Command_getRef___redArg(v___y_3383_);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_object* v_a_3488_; lean_object* v_ref_3489_; lean_object* v___x_3490_; 
v_a_3488_ = lean_ctor_get(v___x_3487_, 0);
lean_inc(v_a_3488_);
lean_dec_ref_known(v___x_3487_, 1);
v_ref_3489_ = l_Lean_replaceRef(v_ref_3379_, v_a_3488_);
lean_dec(v_a_3488_);
v___x_3490_ = l_Lean_Syntax_getPos_x3f(v_ref_3489_, v___y_3485_);
if (lean_obj_tag(v___x_3490_) == 0)
{
lean_object* v___x_3491_; 
v___x_3491_ = lean_unsigned_to_nat(0u);
v___y_3478_ = v___y_3485_;
v___y_3479_ = v___y_3486_;
v___y_3480_ = v_ref_3489_;
v___y_3481_ = v___x_3491_;
goto v___jp_3477_;
}
else
{
lean_object* v_val_3492_; 
v_val_3492_ = lean_ctor_get(v___x_3490_, 0);
lean_inc(v_val_3492_);
lean_dec_ref_known(v___x_3490_, 1);
v___y_3478_ = v___y_3485_;
v___y_3479_ = v___y_3486_;
v___y_3480_ = v_ref_3489_;
v___y_3481_ = v_val_3492_;
goto v___jp_3477_;
}
}
else
{
lean_object* v_a_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3500_; 
lean_dec_ref(v_msgData_3380_);
v_a_3493_ = lean_ctor_get(v___x_3487_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3487_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3495_ = v___x_3487_;
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_a_3493_);
lean_dec(v___x_3487_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v___x_3498_; 
if (v_isShared_3496_ == 0)
{
v___x_3498_ = v___x_3495_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v_a_3493_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
return v___x_3498_;
}
}
}
}
v___jp_3502_:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v_scopes_3506_; lean_object* v___x_3507_; lean_object* v_opts_3508_; uint8_t v___x_3509_; uint8_t v___x_3510_; 
v___x_3504_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3505_ = lean_st_ref_get(v___y_3384_);
v_scopes_3506_ = lean_ctor_get(v___x_3505_, 2);
lean_inc(v_scopes_3506_);
lean_dec(v___x_3505_);
v___x_3507_ = l_List_head_x21___redArg(v___x_3504_, v_scopes_3506_);
lean_dec(v_scopes_3506_);
v_opts_3508_ = lean_ctor_get(v___x_3507_, 1);
lean_inc_ref(v_opts_3508_);
lean_dec(v___x_3507_);
v___x_3509_ = 1;
v___x_3510_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3381_, v___x_3509_);
if (v___x_3510_ == 0)
{
lean_dec_ref(v_opts_3508_);
v___y_3485_ = v___y_3503_;
v___y_3486_ = v_severity_3381_;
goto v___jp_3484_;
}
else
{
lean_object* v___x_3511_; uint8_t v___x_3512_; 
v___x_3511_ = l_Lean_warningAsError;
v___x_3512_ = l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0(v_opts_3508_, v___x_3511_);
lean_dec_ref(v_opts_3508_);
if (v___x_3512_ == 0)
{
v___y_3485_ = v___y_3503_;
v___y_3486_ = v_severity_3381_;
goto v___jp_3484_;
}
else
{
v___y_3485_ = v___y_3503_;
v___y_3486_ = v___x_3501_;
goto v___jp_3484_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___boxed(lean_object* v_ref_3517_, lean_object* v_msgData_3518_, lean_object* v_severity_3519_, lean_object* v_isSilent_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_){
_start:
{
uint8_t v_severity_boxed_3524_; uint8_t v_isSilent_boxed_3525_; lean_object* v_res_3526_; 
v_severity_boxed_3524_ = lean_unbox(v_severity_3519_);
v_isSilent_boxed_3525_ = lean_unbox(v_isSilent_3520_);
v_res_3526_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2(v_ref_3517_, v_msgData_3518_, v_severity_boxed_3524_, v_isSilent_boxed_3525_, v___y_3521_, v___y_3522_);
lean_dec(v___y_3522_);
lean_dec_ref(v___y_3521_);
lean_dec(v_ref_3517_);
return v_res_3526_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1(lean_object* v_ref_3527_, lean_object* v_msgData_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_){
_start:
{
uint8_t v___x_3532_; uint8_t v___x_3533_; lean_object* v___x_3534_; 
v___x_3532_ = 1;
v___x_3533_ = 0;
v___x_3534_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2(v_ref_3527_, v_msgData_3528_, v___x_3532_, v___x_3533_, v___y_3529_, v___y_3530_);
return v___x_3534_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1___boxed(lean_object* v_ref_3535_, lean_object* v_msgData_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_){
_start:
{
lean_object* v_res_3540_; 
v_res_3540_ = l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1(v_ref_3535_, v_msgData_3536_, v___y_3537_, v___y_3538_);
lean_dec(v___y_3538_);
lean_dec_ref(v___y_3537_);
lean_dec(v_ref_3535_);
return v_res_3540_;
}
}
static lean_object* _init_l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3542_ = ((lean_object*)(l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__0));
v___x_3543_ = l_Lean_stringToMessageData(v___x_3542_);
return v___x_3543_;
}
}
static lean_object* _init_l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3545_; lean_object* v___x_3546_; 
v___x_3545_ = ((lean_object*)(l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__2));
v___x_3546_ = l_Lean_stringToMessageData(v___x_3545_);
return v___x_3546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0(lean_object* v_kw_3547_, lean_object* v_what_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_){
_start:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v_scopes_3554_; lean_object* v___x_3555_; lean_object* v_opts_3556_; lean_object* v___x_3557_; uint8_t v___x_3558_; 
v___x_3552_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3553_ = lean_st_ref_get(v___y_3550_);
v_scopes_3554_ = lean_ctor_get(v___x_3553_, 2);
lean_inc(v_scopes_3554_);
lean_dec(v___x_3553_);
v___x_3555_ = l_List_head_x21___redArg(v___x_3552_, v_scopes_3554_);
lean_dec(v_scopes_3554_);
v_opts_3556_ = lean_ctor_get(v___x_3555_, 1);
lean_inc_ref(v_opts_3556_);
lean_dec(v___x_3555_);
v___x_3557_ = l_Lean_Elab_Do_experimental_intrinsic;
v___x_3558_ = l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0(v_opts_3556_, v___x_3557_);
lean_dec_ref(v_opts_3556_);
if (v___x_3558_ == 0)
{
lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; 
v___x_3559_ = lean_obj_once(&l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1, &l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1_once, _init_l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1);
v___x_3560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3560_, 0, v___x_3559_);
lean_ctor_set(v___x_3560_, 1, v_what_3548_);
v___x_3561_ = lean_obj_once(&l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3, &l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3_once, _init_l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3);
v___x_3562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3562_, 0, v___x_3560_);
lean_ctor_set(v___x_3562_, 1, v___x_3561_);
v___x_3563_ = l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1(v_kw_3547_, v___x_3562_, v___y_3549_, v___y_3550_);
return v___x_3563_;
}
else
{
lean_object* v___x_3564_; lean_object* v___x_3565_; 
lean_dec_ref(v_what_3548_);
v___x_3564_ = lean_box(0);
v___x_3565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3565_, 0, v___x_3564_);
return v___x_3565_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___boxed(lean_object* v_kw_3566_, lean_object* v_what_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_){
_start:
{
lean_object* v_res_3571_; 
v_res_3571_ = l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0(v_kw_3566_, v_what_3567_, v___y_3568_, v___y_3569_);
lean_dec(v___y_3569_);
lean_dec_ref(v___y_3568_);
lean_dec(v_kw_3566_);
return v_res_3571_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; 
v___x_3573_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__0));
v___x_3574_ = l_Lean_stringToMessageData(v___x_3573_);
return v___x_3574_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__3(void){
_start:
{
lean_object* v___x_3576_; lean_object* v___x_3577_; 
v___x_3576_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__2));
v___x_3577_ = l_Lean_stringToMessageData(v___x_3576_);
return v___x_3577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1(lean_object* v_as_3578_, size_t v_sz_3579_, size_t v_i_3580_, lean_object* v_b_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_){
_start:
{
uint8_t v___x_3585_; 
v___x_3585_ = lean_usize_dec_lt(v_i_3580_, v_sz_3579_);
if (v___x_3585_ == 0)
{
lean_object* v___x_3586_; 
v___x_3586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3586_, 0, v_b_3581_);
return v___x_3586_;
}
else
{
lean_object* v___x_3587_; lean_object* v_a_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; 
v___x_3587_ = lean_box(0);
v_a_3588_ = lean_array_uget_borrowed(v_as_3578_, v_i_3580_);
v___x_3589_ = lean_unsigned_to_nat(0u);
v___x_3590_ = l_Lean_Syntax_getArg(v_a_3588_, v___x_3589_);
v___x_3591_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__1);
v___x_3592_ = l_Lean_Syntax_getAtomVal(v___x_3590_);
v___x_3593_ = l_Lean_stringToMessageData(v___x_3592_);
v___x_3594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3594_, 0, v___x_3591_);
lean_ctor_set(v___x_3594_, 1, v___x_3593_);
v___x_3595_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__3);
v___x_3596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3596_, 0, v___x_3594_);
lean_ctor_set(v___x_3596_, 1, v___x_3595_);
v___x_3597_ = l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0(v___x_3590_, v___x_3596_, v___y_3582_, v___y_3583_);
lean_dec(v___x_3590_);
if (lean_obj_tag(v___x_3597_) == 0)
{
size_t v___x_3598_; size_t v___x_3599_; 
lean_dec_ref_known(v___x_3597_, 1);
v___x_3598_ = ((size_t)1ULL);
v___x_3599_ = lean_usize_add(v_i_3580_, v___x_3598_);
v_i_3580_ = v___x_3599_;
v_b_3581_ = v___x_3587_;
goto _start;
}
else
{
return v___x_3597_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___boxed(lean_object* v_as_3601_, lean_object* v_sz_3602_, lean_object* v_i_3603_, lean_object* v_b_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_){
_start:
{
size_t v_sz_boxed_3608_; size_t v_i_boxed_3609_; lean_object* v_res_3610_; 
v_sz_boxed_3608_ = lean_unbox_usize(v_sz_3602_);
lean_dec(v_sz_3602_);
v_i_boxed_3609_ = lean_unbox_usize(v_i_3603_);
lean_dec(v_i_3603_);
v_res_3610_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1(v_as_3601_, v_sz_boxed_3608_, v_i_boxed_3609_, v_b_3604_, v___y_3605_, v___y_3606_);
lean_dec(v___y_3606_);
lean_dec_ref(v___y_3605_);
lean_dec_ref(v_as_3601_);
return v_res_3610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__2(lean_object* v_as_3611_, size_t v_sz_3612_, size_t v_i_3613_, lean_object* v_b_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_){
_start:
{
uint8_t v___x_3618_; 
v___x_3618_ = lean_usize_dec_lt(v_i_3613_, v_sz_3612_);
if (v___x_3618_ == 0)
{
lean_object* v___x_3619_; 
v___x_3619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3619_, 0, v_b_3614_);
return v___x_3619_;
}
else
{
lean_object* v___x_3620_; lean_object* v_a_3621_; lean_object* v___x_3622_; size_t v_sz_3623_; size_t v___x_3624_; lean_object* v___x_3625_; 
v___x_3620_ = lean_box(0);
v_a_3621_ = lean_array_uget_borrowed(v_as_3611_, v_i_3613_);
v___x_3622_ = l_Lean_Syntax_getArgs(v_a_3621_);
v_sz_3623_ = lean_array_size(v___x_3622_);
v___x_3624_ = ((size_t)0ULL);
v___x_3625_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1(v___x_3622_, v_sz_3623_, v___x_3624_, v___x_3620_, v___y_3615_, v___y_3616_);
lean_dec_ref(v___x_3622_);
if (lean_obj_tag(v___x_3625_) == 0)
{
size_t v___x_3626_; size_t v___x_3627_; 
lean_dec_ref_known(v___x_3625_, 1);
v___x_3626_ = ((size_t)1ULL);
v___x_3627_ = lean_usize_add(v_i_3613_, v___x_3626_);
v_i_3613_ = v___x_3627_;
v_b_3614_ = v___x_3620_;
goto _start;
}
else
{
return v___x_3625_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__2___boxed(lean_object* v_as_3629_, lean_object* v_sz_3630_, lean_object* v_i_3631_, lean_object* v_b_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_){
_start:
{
size_t v_sz_boxed_3636_; size_t v_i_boxed_3637_; lean_object* v_res_3638_; 
v_sz_boxed_3636_ = lean_unbox_usize(v_sz_3630_);
lean_dec(v_sz_3630_);
v_i_boxed_3637_ = lean_unbox_usize(v_i_3631_);
lean_dec(v_i_3631_);
v_res_3638_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__2(v_as_3629_, v_sz_boxed_3636_, v_i_boxed_3637_, v_b_3632_, v___y_3633_, v___y_3634_);
lean_dec(v___y_3634_);
lean_dec_ref(v___y_3633_);
lean_dec_ref(v_as_3629_);
return v_res_3638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractNotice(lean_object* v_stx_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_){
_start:
{
lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; size_t v_sz_3646_; size_t v___x_3647_; lean_object* v___x_3648_; 
v___x_3643_ = l_Lean_Syntax_getArgs(v_stx_3639_);
v___x_3644_ = lean_array_pop(v___x_3643_);
v___x_3645_ = lean_box(0);
v_sz_3646_ = lean_array_size(v___x_3644_);
v___x_3647_ = ((size_t)0ULL);
v___x_3648_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__2(v___x_3644_, v_sz_3646_, v___x_3647_, v___x_3645_, v_a_3640_, v_a_3641_);
lean_dec_ref(v___x_3644_);
if (lean_obj_tag(v___x_3648_) == 0)
{
lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3655_; 
v_isSharedCheck_3655_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3655_ == 0)
{
lean_object* v_unused_3656_; 
v_unused_3656_ = lean_ctor_get(v___x_3648_, 0);
lean_dec(v_unused_3656_);
v___x_3650_ = v___x_3648_;
v_isShared_3651_ = v_isSharedCheck_3655_;
goto v_resetjp_3649_;
}
else
{
lean_dec(v___x_3648_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3655_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v___x_3653_; 
if (v_isShared_3651_ == 0)
{
lean_ctor_set(v___x_3650_, 0, v___x_3645_);
v___x_3653_ = v___x_3650_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v___x_3645_);
v___x_3653_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
return v___x_3653_;
}
}
}
else
{
return v___x_3648_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractNotice___boxed(lean_object* v_stx_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_){
_start:
{
lean_object* v_res_3661_; 
v_res_3661_ = l_Lean_Elab_Tactic_Do_elabContractNotice(v_stx_3657_, v_a_3658_, v_a_3659_);
lean_dec(v_a_3659_);
lean_dec_ref(v_a_3658_);
lean_dec(v_stx_3657_);
return v_res_3661_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5(lean_object* v_msgData_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_){
_start:
{
lean_object* v___x_3666_; 
v___x_3666_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg(v_msgData_3662_, v___y_3664_);
return v___x_3666_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___boxed(lean_object* v_msgData_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_){
_start:
{
lean_object* v_res_3671_; 
v_res_3671_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5(v_msgData_3667_, v___y_3668_, v___y_3669_);
lean_dec(v___y_3669_);
lean_dec_ref(v___y_3668_);
return v_res_3671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1(){
_start:
{
lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; 
v___x_3680_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3681_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__1));
v___x_3682_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__1));
v___x_3683_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elabContractNotice___boxed), 4, 0);
v___x_3684_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3680_, v___x_3681_, v___x_3682_, v___x_3683_);
return v___x_3684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___boxed(lean_object* v_a_3685_){
_start:
{
lean_object* v_res_3686_; 
v_res_3686_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1();
return v_res_3686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice_docString__3(){
_start:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; 
v___x_3689_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__1));
v___x_3690_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice_docString__3___closed__0));
v___x_3691_ = l_Lean_addBuiltinDocString(v___x_3689_, v___x_3690_);
return v___x_3691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice_docString__3___boxed(lean_object* v_a_3692_){
_start:
{
lean_object* v_res_3693_; 
v_res_3693_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice_docString__3();
return v_res_3693_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; 
v___x_3694_ = lean_box(0);
v___x_3695_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3696_, 0, v___x_3695_);
lean_ctor_set(v___x_3696_, 1, v___x_3694_);
return v___x_3696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg(){
_start:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; 
v___x_3698_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg___closed__0);
v___x_3699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3698_);
return v___x_3699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg___boxed(lean_object* v___y_3700_){
_start:
{
lean_object* v_res_3701_; 
v_res_3701_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg();
return v_res_3701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2(lean_object* v_00_u03b1_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_){
_start:
{
lean_object* v___x_3711_; 
v___x_3711_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg();
return v___x_3711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___boxed(lean_object* v_00_u03b1_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_){
_start:
{
lean_object* v_res_3721_; 
v_res_3721_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2(v_00_u03b1_3712_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_);
lean_dec(v___y_3719_);
lean_dec_ref(v___y_3718_);
lean_dec(v___y_3717_);
lean_dec_ref(v___y_3716_);
lean_dec(v___y_3715_);
lean_dec_ref(v___y_3714_);
lean_dec_ref(v___y_3713_);
return v_res_3721_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2_spec__5(lean_object* v_msgData_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_){
_start:
{
lean_object* v___x_3728_; lean_object* v_env_3729_; uint8_t v___x_3730_; lean_object* v_env_3731_; lean_object* v___x_3732_; lean_object* v_toCold_3733_; lean_object* v_mctx_3734_; lean_object* v_lctx_3735_; lean_object* v_options_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; 
v___x_3728_ = lean_st_ref_get(v___y_3726_);
v_env_3729_ = lean_ctor_get(v___x_3728_, 0);
lean_inc_ref(v_env_3729_);
lean_dec(v___x_3728_);
v___x_3730_ = 0;
v_env_3731_ = l_Lean_Environment_setRecordingDeps(v_env_3729_, v___x_3730_);
v___x_3732_ = lean_st_ref_get(v___y_3724_);
v_toCold_3733_ = lean_ctor_get(v___y_3725_, 0);
v_mctx_3734_ = lean_ctor_get(v___x_3732_, 0);
lean_inc_ref(v_mctx_3734_);
lean_dec(v___x_3732_);
v_lctx_3735_ = lean_ctor_get(v___y_3723_, 2);
v_options_3736_ = lean_ctor_get(v_toCold_3733_, 2);
lean_inc_ref(v_options_3736_);
lean_inc_ref(v_lctx_3735_);
v___x_3737_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3737_, 0, v_env_3731_);
lean_ctor_set(v___x_3737_, 1, v_mctx_3734_);
lean_ctor_set(v___x_3737_, 2, v_lctx_3735_);
lean_ctor_set(v___x_3737_, 3, v_options_3736_);
v___x_3738_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3737_);
lean_ctor_set(v___x_3738_, 1, v_msgData_3722_);
v___x_3739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3738_);
return v___x_3739_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2_spec__5___boxed(lean_object* v_msgData_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_){
_start:
{
lean_object* v_res_3746_; 
v_res_3746_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2_spec__5(v_msgData_3740_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_);
lean_dec(v___y_3744_);
lean_dec_ref(v___y_3743_);
lean_dec(v___y_3742_);
lean_dec_ref(v___y_3741_);
return v_res_3746_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0(uint8_t v_suppressElabErrors_3752_, lean_object* v_x_3753_){
_start:
{
if (lean_obj_tag(v_x_3753_) == 1)
{
lean_object* v_pre_3754_; 
v_pre_3754_ = lean_ctor_get(v_x_3753_, 0);
switch(lean_obj_tag(v_pre_3754_))
{
case 1:
{
lean_object* v_pre_3755_; 
v_pre_3755_ = lean_ctor_get(v_pre_3754_, 0);
switch(lean_obj_tag(v_pre_3755_))
{
case 0:
{
lean_object* v_str_3756_; lean_object* v_str_3757_; lean_object* v___x_3758_; uint8_t v___x_3759_; 
v_str_3756_ = lean_ctor_get(v_x_3753_, 1);
v_str_3757_ = lean_ctor_get(v_pre_3754_, 1);
v___x_3758_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__21));
v___x_3759_ = lean_string_dec_eq(v_str_3757_, v___x_3758_);
if (v___x_3759_ == 0)
{
lean_object* v___x_3760_; uint8_t v___x_3761_; 
v___x_3760_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__22));
v___x_3761_ = lean_string_dec_eq(v_str_3757_, v___x_3760_);
if (v___x_3761_ == 0)
{
return v___x_3761_;
}
else
{
lean_object* v___x_3762_; uint8_t v___x_3763_; 
v___x_3762_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__0));
v___x_3763_ = lean_string_dec_eq(v_str_3756_, v___x_3762_);
if (v___x_3763_ == 0)
{
return v___x_3763_;
}
else
{
return v_suppressElabErrors_3752_;
}
}
}
else
{
lean_object* v___x_3764_; uint8_t v___x_3765_; 
v___x_3764_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__1));
v___x_3765_ = lean_string_dec_eq(v_str_3756_, v___x_3764_);
if (v___x_3765_ == 0)
{
return v___x_3765_;
}
else
{
return v_suppressElabErrors_3752_;
}
}
}
case 1:
{
lean_object* v_pre_3766_; 
v_pre_3766_ = lean_ctor_get(v_pre_3755_, 0);
if (lean_obj_tag(v_pre_3766_) == 0)
{
lean_object* v_str_3767_; lean_object* v_str_3768_; lean_object* v_str_3769_; lean_object* v___x_3770_; uint8_t v___x_3771_; 
v_str_3767_ = lean_ctor_get(v_x_3753_, 1);
v_str_3768_ = lean_ctor_get(v_pre_3754_, 1);
v_str_3769_ = lean_ctor_get(v_pre_3755_, 1);
v___x_3770_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__2));
v___x_3771_ = lean_string_dec_eq(v_str_3769_, v___x_3770_);
if (v___x_3771_ == 0)
{
return v___x_3771_;
}
else
{
lean_object* v___x_3772_; uint8_t v___x_3773_; 
v___x_3772_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__3));
v___x_3773_ = lean_string_dec_eq(v_str_3768_, v___x_3772_);
if (v___x_3773_ == 0)
{
return v___x_3773_;
}
else
{
lean_object* v___x_3774_; uint8_t v___x_3775_; 
v___x_3774_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__4));
v___x_3775_ = lean_string_dec_eq(v_str_3767_, v___x_3774_);
if (v___x_3775_ == 0)
{
return v___x_3775_;
}
else
{
return v_suppressElabErrors_3752_;
}
}
}
}
else
{
uint8_t v___x_3776_; 
v___x_3776_ = 0;
return v___x_3776_;
}
}
default: 
{
uint8_t v___x_3777_; 
v___x_3777_ = 0;
return v___x_3777_;
}
}
}
case 0:
{
lean_object* v_str_3778_; lean_object* v___x_3779_; uint8_t v___x_3780_; 
v_str_3778_ = lean_ctor_get(v_x_3753_, 1);
v___x_3779_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0___closed__0));
v___x_3780_ = lean_string_dec_eq(v_str_3778_, v___x_3779_);
if (v___x_3780_ == 0)
{
return v___x_3780_;
}
else
{
return v_suppressElabErrors_3752_;
}
}
default: 
{
uint8_t v___x_3781_; 
v___x_3781_ = 0;
return v___x_3781_;
}
}
}
else
{
uint8_t v___x_3782_; 
v___x_3782_ = 0;
return v___x_3782_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_3783_, lean_object* v_x_3784_){
_start:
{
uint8_t v_suppressElabErrors_boxed_3785_; uint8_t v_res_3786_; lean_object* v_r_3787_; 
v_suppressElabErrors_boxed_3785_ = lean_unbox(v_suppressElabErrors_3783_);
v_res_3786_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0(v_suppressElabErrors_boxed_3785_, v_x_3784_);
lean_dec(v_x_3784_);
v_r_3787_ = lean_box(v_res_3786_);
return v_r_3787_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_3788_, lean_object* v_msgData_3789_, uint8_t v_severity_3790_, uint8_t v_isSilent_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_){
_start:
{
lean_object* v___y_3798_; uint8_t v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; uint8_t v___y_3804_; lean_object* v_toCold_3805_; lean_object* v___y_3806_; lean_object* v___y_3835_; lean_object* v___y_3836_; uint8_t v___y_3837_; uint8_t v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; uint8_t v___y_3841_; lean_object* v___y_3842_; uint8_t v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3864_; uint8_t v___y_3865_; lean_object* v___y_3866_; uint8_t v___y_3867_; lean_object* v___y_3868_; uint8_t v___y_3872_; uint8_t v___y_3873_; uint8_t v___x_3883_; uint8_t v___y_3885_; uint8_t v___x_3891_; 
v___x_3883_ = 2;
v___x_3891_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3790_, v___x_3883_);
if (v___x_3891_ == 0)
{
v___y_3885_ = v___x_3891_;
goto v___jp_3884_;
}
else
{
uint8_t v___x_3892_; 
lean_inc_ref(v_msgData_3789_);
v___x_3892_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3789_);
if (v___x_3892_ == 0)
{
v___y_3885_ = v___x_3892_;
goto v___jp_3884_;
}
else
{
lean_object* v___x_3893_; lean_object* v___x_3894_; 
lean_dec_ref(v_msgData_3789_);
v___x_3893_ = lean_box(0);
v___x_3894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3894_, 0, v___x_3893_);
return v___x_3894_;
}
}
v___jp_3797_:
{
lean_object* v_currNamespace_3807_; lean_object* v_openDecls_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v_env_3813_; lean_object* v_nextMacroScope_3814_; lean_object* v_ngen_3815_; lean_object* v_auxDeclNGen_3816_; lean_object* v_traceState_3817_; lean_object* v_cache_3818_; lean_object* v_recordedDeps_3819_; lean_object* v_messages_3820_; lean_object* v_infoState_3821_; lean_object* v_snapshotTasks_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3833_; 
v_currNamespace_3807_ = lean_ctor_get(v_toCold_3805_, 4);
v_openDecls_3808_ = lean_ctor_get(v_toCold_3805_, 5);
lean_inc(v_openDecls_3808_);
lean_inc(v_currNamespace_3807_);
v___x_3809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3809_, 0, v_currNamespace_3807_);
lean_ctor_set(v___x_3809_, 1, v_openDecls_3808_);
v___x_3810_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3810_, 0, v___x_3809_);
lean_ctor_set(v___x_3810_, 1, v___y_3801_);
lean_inc_ref(v___y_3803_);
lean_inc_ref(v___y_3802_);
v___x_3811_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3811_, 0, v___y_3802_);
lean_ctor_set(v___x_3811_, 1, v___y_3800_);
lean_ctor_set(v___x_3811_, 2, v___y_3798_);
lean_ctor_set(v___x_3811_, 3, v___y_3803_);
lean_ctor_set(v___x_3811_, 4, v___x_3810_);
lean_ctor_set_uint8(v___x_3811_, sizeof(void*)*5, v___y_3799_);
lean_ctor_set_uint8(v___x_3811_, sizeof(void*)*5 + 1, v___y_3804_);
lean_ctor_set_uint8(v___x_3811_, sizeof(void*)*5 + 2, v_isSilent_3791_);
v___x_3812_ = lean_st_ref_take(v___y_3806_);
v_env_3813_ = lean_ctor_get(v___x_3812_, 0);
v_nextMacroScope_3814_ = lean_ctor_get(v___x_3812_, 1);
v_ngen_3815_ = lean_ctor_get(v___x_3812_, 2);
v_auxDeclNGen_3816_ = lean_ctor_get(v___x_3812_, 3);
v_traceState_3817_ = lean_ctor_get(v___x_3812_, 4);
v_cache_3818_ = lean_ctor_get(v___x_3812_, 5);
v_recordedDeps_3819_ = lean_ctor_get(v___x_3812_, 6);
v_messages_3820_ = lean_ctor_get(v___x_3812_, 7);
v_infoState_3821_ = lean_ctor_get(v___x_3812_, 8);
v_snapshotTasks_3822_ = lean_ctor_get(v___x_3812_, 9);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3812_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3824_ = v___x_3812_;
v_isShared_3825_ = v_isSharedCheck_3833_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_snapshotTasks_3822_);
lean_inc(v_infoState_3821_);
lean_inc(v_messages_3820_);
lean_inc(v_recordedDeps_3819_);
lean_inc(v_cache_3818_);
lean_inc(v_traceState_3817_);
lean_inc(v_auxDeclNGen_3816_);
lean_inc(v_ngen_3815_);
lean_inc(v_nextMacroScope_3814_);
lean_inc(v_env_3813_);
lean_dec(v___x_3812_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3833_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3829_; 
v___x_3826_ = lean_box(0);
v___x_3827_ = l_Lean_MessageLog_add(v___x_3811_, v_messages_3820_);
if (v_isShared_3825_ == 0)
{
lean_ctor_set(v___x_3824_, 7, v___x_3827_);
v___x_3829_ = v___x_3824_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_env_3813_);
lean_ctor_set(v_reuseFailAlloc_3832_, 1, v_nextMacroScope_3814_);
lean_ctor_set(v_reuseFailAlloc_3832_, 2, v_ngen_3815_);
lean_ctor_set(v_reuseFailAlloc_3832_, 3, v_auxDeclNGen_3816_);
lean_ctor_set(v_reuseFailAlloc_3832_, 4, v_traceState_3817_);
lean_ctor_set(v_reuseFailAlloc_3832_, 5, v_cache_3818_);
lean_ctor_set(v_reuseFailAlloc_3832_, 6, v_recordedDeps_3819_);
lean_ctor_set(v_reuseFailAlloc_3832_, 7, v___x_3827_);
lean_ctor_set(v_reuseFailAlloc_3832_, 8, v_infoState_3821_);
lean_ctor_set(v_reuseFailAlloc_3832_, 9, v_snapshotTasks_3822_);
v___x_3829_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
lean_object* v___x_3830_; lean_object* v___x_3831_; 
v___x_3830_ = lean_st_ref_put(v___y_3806_, v___x_3829_);
v___x_3831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3831_, 0, v___x_3826_);
return v___x_3831_;
}
}
}
v___jp_3834_:
{
lean_object* v_fileName_3843_; lean_object* v_fileMap_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v_a_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3860_; 
v_fileName_3843_ = lean_ctor_get(v___y_3839_, 0);
v_fileMap_3844_ = lean_ctor_get(v___y_3839_, 1);
v___x_3845_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3789_);
v___x_3846_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2_spec__5(v___x_3845_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_);
v_a_3847_ = lean_ctor_get(v___x_3846_, 0);
v_isSharedCheck_3860_ = !lean_is_exclusive(v___x_3846_);
if (v_isSharedCheck_3860_ == 0)
{
v___x_3849_ = v___x_3846_;
v_isShared_3850_ = v_isSharedCheck_3860_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_a_3847_);
lean_dec(v___x_3846_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3860_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; 
lean_inc_ref_n(v_fileMap_3844_, 2);
v___x_3851_ = l_Lean_FileMap_toPosition(v_fileMap_3844_, v___y_3840_);
lean_dec(v___y_3840_);
v___x_3852_ = l_Lean_FileMap_toPosition(v_fileMap_3844_, v___y_3842_);
lean_dec(v___y_3842_);
v___x_3853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3853_, 0, v___x_3852_);
v___x_3854_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__19));
if (v___y_3837_ == 0)
{
lean_del_object(v___x_3849_);
lean_dec_ref(v___y_3836_);
v___y_3798_ = v___x_3853_;
v___y_3799_ = v___y_3838_;
v___y_3800_ = v___x_3851_;
v___y_3801_ = v_a_3847_;
v___y_3802_ = v_fileName_3843_;
v___y_3803_ = v___x_3854_;
v___y_3804_ = v___y_3841_;
v_toCold_3805_ = v___y_3835_;
v___y_3806_ = v___y_3795_;
goto v___jp_3797_;
}
else
{
uint8_t v___x_3855_; 
lean_inc(v_a_3847_);
v___x_3855_ = l_Lean_MessageData_hasTag(v___y_3836_, v_a_3847_);
if (v___x_3855_ == 0)
{
lean_object* v___x_3856_; lean_object* v___x_3858_; 
lean_dec_ref_known(v___x_3853_, 1);
lean_dec_ref(v___x_3851_);
lean_dec(v_a_3847_);
v___x_3856_ = lean_box(0);
if (v_isShared_3850_ == 0)
{
lean_ctor_set(v___x_3849_, 0, v___x_3856_);
v___x_3858_ = v___x_3849_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3859_, 0, v___x_3856_);
v___x_3858_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
return v___x_3858_;
}
}
else
{
lean_del_object(v___x_3849_);
v___y_3798_ = v___x_3853_;
v___y_3799_ = v___y_3838_;
v___y_3800_ = v___x_3851_;
v___y_3801_ = v_a_3847_;
v___y_3802_ = v_fileName_3843_;
v___y_3803_ = v___x_3854_;
v___y_3804_ = v___y_3841_;
v_toCold_3805_ = v___y_3835_;
v___y_3806_ = v___y_3795_;
goto v___jp_3797_;
}
}
}
}
v___jp_3861_:
{
lean_object* v___x_3869_; 
v___x_3869_ = l_Lean_Syntax_getTailPos_x3f(v___y_3866_, v___y_3865_);
lean_dec(v___y_3866_);
if (lean_obj_tag(v___x_3869_) == 0)
{
lean_inc(v___y_3868_);
v___y_3835_ = v___y_3863_;
v___y_3836_ = v___y_3864_;
v___y_3837_ = v___y_3862_;
v___y_3838_ = v___y_3865_;
v___y_3839_ = v___y_3863_;
v___y_3840_ = v___y_3868_;
v___y_3841_ = v___y_3867_;
v___y_3842_ = v___y_3868_;
goto v___jp_3834_;
}
else
{
lean_object* v_val_3870_; 
v_val_3870_ = lean_ctor_get(v___x_3869_, 0);
lean_inc(v_val_3870_);
lean_dec_ref_known(v___x_3869_, 1);
v___y_3835_ = v___y_3863_;
v___y_3836_ = v___y_3864_;
v___y_3837_ = v___y_3862_;
v___y_3838_ = v___y_3865_;
v___y_3839_ = v___y_3863_;
v___y_3840_ = v___y_3868_;
v___y_3841_ = v___y_3867_;
v___y_3842_ = v_val_3870_;
goto v___jp_3834_;
}
}
v___jp_3871_:
{
lean_object* v_toCold_3874_; lean_object* v_ref_3875_; uint8_t v_suppressElabErrors_3876_; lean_object* v___x_3877_; lean_object* v___f_3878_; lean_object* v_ref_3879_; lean_object* v___x_3880_; 
v_toCold_3874_ = lean_ctor_get(v___y_3794_, 0);
v_ref_3875_ = lean_ctor_get(v___y_3794_, 2);
v_suppressElabErrors_3876_ = lean_ctor_get_uint8(v___y_3794_, sizeof(void*)*3 + 2);
v___x_3877_ = lean_box(v_suppressElabErrors_3876_);
v___f_3878_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3878_, 0, v___x_3877_);
v_ref_3879_ = l_Lean_replaceRef(v_ref_3788_, v_ref_3875_);
v___x_3880_ = l_Lean_Syntax_getPos_x3f(v_ref_3879_, v___y_3872_);
if (lean_obj_tag(v___x_3880_) == 0)
{
lean_object* v___x_3881_; 
v___x_3881_ = lean_unsigned_to_nat(0u);
v___y_3862_ = v_suppressElabErrors_3876_;
v___y_3863_ = v_toCold_3874_;
v___y_3864_ = v___f_3878_;
v___y_3865_ = v___y_3872_;
v___y_3866_ = v_ref_3879_;
v___y_3867_ = v___y_3873_;
v___y_3868_ = v___x_3881_;
goto v___jp_3861_;
}
else
{
lean_object* v_val_3882_; 
v_val_3882_ = lean_ctor_get(v___x_3880_, 0);
lean_inc(v_val_3882_);
lean_dec_ref_known(v___x_3880_, 1);
v___y_3862_ = v_suppressElabErrors_3876_;
v___y_3863_ = v_toCold_3874_;
v___y_3864_ = v___f_3878_;
v___y_3865_ = v___y_3872_;
v___y_3866_ = v_ref_3879_;
v___y_3867_ = v___y_3873_;
v___y_3868_ = v_val_3882_;
goto v___jp_3861_;
}
}
v___jp_3884_:
{
uint8_t v___x_3886_; uint8_t v___x_3887_; 
v___x_3886_ = 1;
v___x_3887_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3790_, v___x_3886_);
if (v___x_3887_ == 0)
{
v___y_3872_ = v___y_3885_;
v___y_3873_ = v_severity_3790_;
goto v___jp_3871_;
}
else
{
lean_object* v___x_3888_; lean_object* v___x_3889_; uint8_t v___x_3890_; 
v___x_3888_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3794_);
v___x_3889_ = l_Lean_warningAsError;
v___x_3890_ = l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0(v___x_3888_, v___x_3889_);
lean_dec_ref(v___x_3888_);
if (v___x_3890_ == 0)
{
v___y_3872_ = v___y_3885_;
v___y_3873_ = v_severity_3790_;
goto v___jp_3871_;
}
else
{
v___y_3872_ = v___y_3885_;
v___y_3873_ = v___x_3883_;
goto v___jp_3871_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_3895_, lean_object* v_msgData_3896_, lean_object* v_severity_3897_, lean_object* v_isSilent_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_){
_start:
{
uint8_t v_severity_boxed_3904_; uint8_t v_isSilent_boxed_3905_; lean_object* v_res_3906_; 
v_severity_boxed_3904_ = lean_unbox(v_severity_3897_);
v_isSilent_boxed_3905_ = lean_unbox(v_isSilent_3898_);
v_res_3906_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg(v_ref_3895_, v_msgData_3896_, v_severity_boxed_3904_, v_isSilent_boxed_3905_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_);
lean_dec(v___y_3902_);
lean_dec_ref(v___y_3901_);
lean_dec(v___y_3900_);
lean_dec_ref(v___y_3899_);
lean_dec(v_ref_3895_);
return v_res_3906_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0(lean_object* v_ref_3907_, lean_object* v_msgData_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_){
_start:
{
uint8_t v___x_3917_; uint8_t v___x_3918_; lean_object* v___x_3919_; 
v___x_3917_ = 1;
v___x_3918_ = 0;
v___x_3919_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg(v_ref_3907_, v_msgData_3908_, v___x_3917_, v___x_3918_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_);
return v___x_3919_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0___boxed(lean_object* v_ref_3920_, lean_object* v_msgData_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_){
_start:
{
lean_object* v_res_3930_; 
v_res_3930_ = l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0(v_ref_3920_, v_msgData_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_);
lean_dec(v___y_3928_);
lean_dec_ref(v___y_3927_);
lean_dec(v___y_3926_);
lean_dec_ref(v___y_3925_);
lean_dec(v___y_3924_);
lean_dec_ref(v___y_3923_);
lean_dec_ref(v___y_3922_);
lean_dec(v_ref_3920_);
return v_res_3930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0(lean_object* v_kw_3931_, lean_object* v_what_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_){
_start:
{
lean_object* v___x_3941_; lean_object* v___x_3942_; uint8_t v___x_3943_; 
v___x_3941_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3938_);
v___x_3942_ = l_Lean_Elab_Do_experimental_intrinsic;
v___x_3943_ = l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0(v___x_3941_, v___x_3942_);
lean_dec_ref(v___x_3941_);
if (v___x_3943_ == 0)
{
lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; 
v___x_3944_ = lean_obj_once(&l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1, &l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1_once, _init_l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1);
v___x_3945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3945_, 0, v___x_3944_);
lean_ctor_set(v___x_3945_, 1, v_what_3932_);
v___x_3946_ = lean_obj_once(&l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3, &l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3_once, _init_l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3);
v___x_3947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3947_, 0, v___x_3945_);
lean_ctor_set(v___x_3947_, 1, v___x_3946_);
v___x_3948_ = l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0(v_kw_3931_, v___x_3947_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_);
return v___x_3948_;
}
else
{
lean_object* v___x_3949_; lean_object* v___x_3950_; 
lean_dec_ref(v_what_3932_);
v___x_3949_ = lean_box(0);
v___x_3950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3950_, 0, v___x_3949_);
return v___x_3950_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0___boxed(lean_object* v_kw_3951_, lean_object* v_what_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_){
_start:
{
lean_object* v_res_3961_; 
v_res_3961_ = l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0(v_kw_3951_, v_what_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_);
lean_dec(v___y_3959_);
lean_dec_ref(v___y_3958_);
lean_dec(v___y_3957_);
lean_dec_ref(v___y_3956_);
lean_dec(v___y_3955_);
lean_dec_ref(v___y_3954_);
lean_dec_ref(v___y_3953_);
lean_dec(v_kw_3951_);
return v_res_3961_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2___redArg(lean_object* v_msg_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_){
_start:
{
lean_object* v_ref_3968_; lean_object* v___x_3969_; lean_object* v_a_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_3978_; 
v_ref_3968_ = lean_ctor_get(v___y_3965_, 2);
v___x_3969_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2_spec__5(v_msg_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_);
v_a_3970_ = lean_ctor_get(v___x_3969_, 0);
v_isSharedCheck_3978_ = !lean_is_exclusive(v___x_3969_);
if (v_isSharedCheck_3978_ == 0)
{
v___x_3972_ = v___x_3969_;
v_isShared_3973_ = v_isSharedCheck_3978_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_a_3970_);
lean_dec(v___x_3969_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_3978_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___x_3974_; lean_object* v___x_3976_; 
lean_inc(v_ref_3968_);
v___x_3974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3974_, 0, v_ref_3968_);
lean_ctor_set(v___x_3974_, 1, v_a_3970_);
if (v_isShared_3973_ == 0)
{
lean_ctor_set_tag(v___x_3972_, 1);
lean_ctor_set(v___x_3972_, 0, v___x_3974_);
v___x_3976_ = v___x_3972_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v___x_3974_);
v___x_3976_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
return v___x_3976_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2___redArg___boxed(lean_object* v_msg_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_){
_start:
{
lean_object* v_res_3985_; 
v_res_3985_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2___redArg(v_msg_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_);
lean_dec(v___y_3983_);
lean_dec_ref(v___y_3982_);
lean_dec(v___y_3981_);
lean_dec_ref(v___y_3980_);
return v_res_3985_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg(lean_object* v_ref_3986_, lean_object* v_msg_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_){
_start:
{
lean_object* v_toCold_3996_; lean_object* v_currRecDepth_3997_; lean_object* v_ref_3998_; uint16_t v_optionFlags_3999_; uint8_t v_suppressElabErrors_4000_; uint8_t v_checkDeprecated_4001_; uint8_t v_isRecordingDeps_4002_; lean_object* v_ref_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; 
v_toCold_3996_ = lean_ctor_get(v___y_3993_, 0);
v_currRecDepth_3997_ = lean_ctor_get(v___y_3993_, 1);
v_ref_3998_ = lean_ctor_get(v___y_3993_, 2);
v_optionFlags_3999_ = lean_ctor_get_uint16(v___y_3993_, sizeof(void*)*3);
v_suppressElabErrors_4000_ = lean_ctor_get_uint8(v___y_3993_, sizeof(void*)*3 + 2);
v_checkDeprecated_4001_ = lean_ctor_get_uint8(v___y_3993_, sizeof(void*)*3 + 3);
v_isRecordingDeps_4002_ = lean_ctor_get_uint8(v___y_3993_, sizeof(void*)*3 + 4);
v_ref_4003_ = l_Lean_replaceRef(v_ref_3986_, v_ref_3998_);
lean_inc(v_currRecDepth_3997_);
lean_inc_ref(v_toCold_3996_);
v___x_4004_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_4004_, 0, v_toCold_3996_);
lean_ctor_set(v___x_4004_, 1, v_currRecDepth_3997_);
lean_ctor_set(v___x_4004_, 2, v_ref_4003_);
lean_ctor_set_uint16(v___x_4004_, sizeof(void*)*3, v_optionFlags_3999_);
lean_ctor_set_uint8(v___x_4004_, sizeof(void*)*3 + 2, v_suppressElabErrors_4000_);
lean_ctor_set_uint8(v___x_4004_, sizeof(void*)*3 + 3, v_checkDeprecated_4001_);
lean_ctor_set_uint8(v___x_4004_, sizeof(void*)*3 + 4, v_isRecordingDeps_4002_);
v___x_4005_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2___redArg(v_msg_3987_, v___y_3991_, v___y_3992_, v___x_4004_, v___y_3994_);
lean_dec_ref_known(v___x_4004_, 3);
return v___x_4005_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg___boxed(lean_object* v_ref_4006_, lean_object* v_msg_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_){
_start:
{
lean_object* v_res_4016_; 
v_res_4016_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg(v_ref_4006_, v_msg_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_);
lean_dec(v___y_4014_);
lean_dec_ref(v___y_4013_);
lean_dec(v___y_4012_);
lean_dec_ref(v___y_4011_);
lean_dec(v___y_4010_);
lean_dec_ref(v___y_4009_);
lean_dec_ref(v___y_4008_);
lean_dec(v_ref_4006_);
return v_res_4016_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__1(void){
_start:
{
lean_object* v___x_4018_; lean_object* v___x_4019_; 
v___x_4018_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__0));
v___x_4019_ = l_Lean_stringToMessageData(v___x_4018_);
return v___x_4019_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__9(void){
_start:
{
lean_object* v___x_4043_; lean_object* v___x_4044_; 
v___x_4043_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__8));
v___x_4044_ = l_Lean_mkCIdent(v___x_4043_);
return v___x_4044_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__11(void){
_start:
{
lean_object* v___x_4046_; lean_object* v___x_4047_; 
v___x_4046_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__10));
v___x_4047_ = l_Lean_stringToMessageData(v___x_4046_);
return v___x_4047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion(lean_object* v_stx_4054_, lean_object* v_dec_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_){
_start:
{
lean_object* v___x_4064_; lean_object* v_tk_4065_; lean_object* v___y_4067_; lean_object* v___y_4068_; lean_object* v___y_4069_; lean_object* v___y_4070_; lean_object* v___y_4071_; lean_object* v___y_4072_; lean_object* v___y_4073_; lean_object* v___y_4074_; lean_object* v_as_4144_; lean_object* v___y_4145_; lean_object* v___y_4146_; lean_object* v___y_4147_; lean_object* v___y_4148_; lean_object* v___y_4149_; lean_object* v___y_4150_; lean_object* v___y_4151_; lean_object* v___x_4167_; uint8_t v___x_4168_; 
v___x_4064_ = lean_unsigned_to_nat(0u);
v_tk_4065_ = l_Lean_Syntax_getArg(v_stx_4054_, v___x_4064_);
v___x_4167_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__13));
lean_inc(v_stx_4054_);
v___x_4168_ = l_Lean_Syntax_isOfKind(v_stx_4054_, v___x_4167_);
if (v___x_4168_ == 0)
{
lean_object* v___x_4169_; lean_object* v_a_4170_; lean_object* v___x_4172_; uint8_t v_isShared_4173_; uint8_t v_isSharedCheck_4177_; 
lean_dec(v_tk_4065_);
lean_dec_ref(v_dec_4055_);
lean_dec(v_stx_4054_);
v___x_4169_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg();
v_a_4170_ = lean_ctor_get(v___x_4169_, 0);
v_isSharedCheck_4177_ = !lean_is_exclusive(v___x_4169_);
if (v_isSharedCheck_4177_ == 0)
{
v___x_4172_ = v___x_4169_;
v_isShared_4173_ = v_isSharedCheck_4177_;
goto v_resetjp_4171_;
}
else
{
lean_inc(v_a_4170_);
lean_dec(v___x_4169_);
v___x_4172_ = lean_box(0);
v_isShared_4173_ = v_isSharedCheck_4177_;
goto v_resetjp_4171_;
}
v_resetjp_4171_:
{
lean_object* v___x_4175_; 
if (v_isShared_4173_ == 0)
{
v___x_4175_ = v___x_4172_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v_a_4170_);
v___x_4175_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4174_;
}
v_reusejp_4174_:
{
return v___x_4175_;
}
}
}
else
{
lean_object* v___x_4178_; lean_object* v_p_4179_; lean_object* v___x_4180_; uint8_t v___x_4181_; 
v___x_4178_ = lean_unsigned_to_nat(1u);
v_p_4179_ = l_Lean_Syntax_getArg(v_stx_4054_, v___x_4178_);
lean_dec(v_stx_4054_);
v___x_4180_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__3));
lean_inc(v_p_4179_);
v___x_4181_ = l_Lean_Syntax_isOfKind(v_p_4179_, v___x_4180_);
if (v___x_4181_ == 0)
{
v_as_4144_ = v_p_4179_;
v___y_4145_ = v_a_4056_;
v___y_4146_ = v_a_4057_;
v___y_4147_ = v_a_4058_;
v___y_4148_ = v_a_4059_;
v___y_4149_ = v_a_4060_;
v___y_4150_ = v_a_4061_;
v___y_4151_ = v_a_4062_;
goto v___jp_4143_;
}
else
{
lean_object* v_ref_4182_; uint8_t v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; 
v_ref_4182_ = lean_ctor_get(v_a_4061_, 2);
v___x_4183_ = 0;
v___x_4184_ = l_Lean_SourceInfo_fromRef(v_ref_4182_, v___x_4183_);
v___x_4185_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__40));
v___x_4186_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__41));
lean_inc(v___x_4184_);
v___x_4187_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4187_, 0, v___x_4184_);
lean_ctor_set(v___x_4187_, 1, v___x_4185_);
v___x_4188_ = l_Lean_Syntax_node2(v___x_4184_, v___x_4186_, v___x_4187_, v_p_4179_);
v_as_4144_ = v___x_4188_;
v___y_4145_ = v_a_4056_;
v___y_4146_ = v_a_4057_;
v___y_4147_ = v_a_4058_;
v___y_4148_ = v_a_4059_;
v___y_4149_ = v_a_4060_;
v___y_4150_ = v_a_4061_;
v___y_4151_ = v_a_4062_;
goto v___jp_4143_;
}
}
v___jp_4066_:
{
lean_object* v___x_4075_; lean_object* v___x_4076_; 
v___x_4075_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__1, &l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__1_once, _init_l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__1);
v___x_4076_ = l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0(v_tk_4065_, v___x_4075_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
if (lean_obj_tag(v___x_4076_) == 0)
{
lean_object* v___x_4077_; 
lean_dec_ref_known(v___x_4076_, 1);
v___x_4077_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_4055_, v_tk_4065_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
lean_dec(v_tk_4065_);
if (lean_obj_tag(v___x_4077_) == 0)
{
lean_object* v_toCold_4078_; lean_object* v_a_4079_; lean_object* v_ref_4080_; lean_object* v_quotContext_4081_; lean_object* v_currMacroScope_4082_; uint8_t v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; 
v_toCold_4078_ = lean_ctor_get(v___y_4073_, 0);
v_a_4079_ = lean_ctor_get(v___x_4077_, 0);
lean_inc(v_a_4079_);
lean_dec_ref_known(v___x_4077_, 1);
v_ref_4080_ = lean_ctor_get(v___y_4073_, 2);
v_quotContext_4081_ = lean_ctor_get(v_toCold_4078_, 8);
v_currMacroScope_4082_ = lean_ctor_get(v_toCold_4078_, 9);
v___x_4083_ = 0;
v___x_4084_ = l_Lean_SourceInfo_fromRef(v_ref_4080_, v___x_4083_);
v___x_4085_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__1));
v___x_4086_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__2));
lean_inc_n(v___x_4084_, 9);
v___x_4087_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4087_, 0, v___x_4084_);
lean_ctor_set(v___x_4087_, 1, v___x_4085_);
v___x_4088_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__3));
v___x_4089_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__3));
v___x_4090_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4090_, 0, v___x_4084_);
lean_ctor_set(v___x_4090_, 1, v___x_4089_);
v___x_4091_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__2));
v___x_4092_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_expandDefContract___closed__5, &l_Lean_Elab_Tactic_Do_expandDefContract___closed__5_once, _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__5);
v___x_4093_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__29));
lean_inc_n(v_currMacroScope_4082_, 2);
lean_inc_n(v_quotContext_4081_, 2);
v___x_4094_ = l_Lean_addMacroScope(v_quotContext_4081_, v___x_4093_, v_currMacroScope_4082_);
v___x_4095_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__4));
v___x_4096_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4096_, 0, v___x_4084_);
lean_ctor_set(v___x_4096_, 1, v___x_4092_);
lean_ctor_set(v___x_4096_, 2, v___x_4094_);
lean_ctor_set(v___x_4096_, 3, v___x_4095_);
v___x_4097_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_expandDefContract___closed__7, &l_Lean_Elab_Tactic_Do_expandDefContract___closed__7_once, _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__7);
v___x_4098_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__27));
v___x_4099_ = l_Lean_addMacroScope(v_quotContext_4081_, v___x_4098_, v_currMacroScope_4082_);
v___x_4100_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__5));
v___x_4101_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4101_, 0, v___x_4084_);
lean_ctor_set(v___x_4101_, 1, v___x_4097_);
lean_ctor_set(v___x_4101_, 2, v___x_4099_);
lean_ctor_set(v___x_4101_, 3, v___x_4100_);
v___x_4102_ = l_Lean_Syntax_node2(v___x_4084_, v___x_4091_, v___x_4096_, v___x_4101_);
v___x_4103_ = l_Lean_Syntax_node2(v___x_4084_, v___x_4088_, v___x_4090_, v___x_4102_);
v___x_4104_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__0));
v___x_4105_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4105_, 0, v___x_4084_);
lean_ctor_set(v___x_4105_, 1, v___x_4104_);
v___x_4106_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__7));
v___x_4107_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__9, &l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__9_once, _init_l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__9);
v___x_4108_ = l_Lean_Syntax_node1(v___x_4084_, v___x_4091_, v___y_4067_);
v___x_4109_ = l_Lean_Syntax_node2(v___x_4084_, v___x_4106_, v___x_4107_, v___x_4108_);
v___x_4110_ = l_Lean_Syntax_node4(v___x_4084_, v___x_4086_, v___x_4087_, v___x_4103_, v___x_4105_, v___x_4109_);
v___x_4111_ = l_Lean_Elab_Do_mkPUnit___redArg(v___y_4068_);
if (lean_obj_tag(v___x_4111_) == 0)
{
lean_object* v_a_4112_; lean_object* v___x_4113_; 
v_a_4112_ = lean_ctor_get(v___x_4111_, 0);
lean_inc(v_a_4112_);
lean_dec_ref_known(v___x_4111_, 1);
v___x_4113_ = l_Lean_Elab_Do_mkMonadApp(v_a_4112_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
if (lean_obj_tag(v___x_4113_) == 0)
{
lean_object* v_a_4114_; lean_object* v___x_4116_; uint8_t v_isShared_4117_; uint8_t v_isSharedCheck_4126_; 
v_a_4114_ = lean_ctor_get(v___x_4113_, 0);
v_isSharedCheck_4126_ = !lean_is_exclusive(v___x_4113_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_4116_ = v___x_4113_;
v_isShared_4117_ = v_isSharedCheck_4126_;
goto v_resetjp_4115_;
}
else
{
lean_inc(v_a_4114_);
lean_dec(v___x_4113_);
v___x_4116_ = lean_box(0);
v_isShared_4117_ = v_isSharedCheck_4126_;
goto v_resetjp_4115_;
}
v_resetjp_4115_:
{
lean_object* v___x_4119_; 
if (v_isShared_4117_ == 0)
{
lean_ctor_set_tag(v___x_4116_, 1);
v___x_4119_ = v___x_4116_;
goto v_reusejp_4118_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v_a_4114_);
v___x_4119_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4118_;
}
v_reusejp_4118_:
{
uint8_t v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; 
v___x_4120_ = 1;
v___x_4121_ = lean_box(0);
v___x_4122_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_4110_, v___x_4119_, v___x_4120_, v___x_4120_, v___x_4121_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
if (lean_obj_tag(v___x_4122_) == 0)
{
lean_object* v_a_4123_; lean_object* v___x_4124_; 
v_a_4123_ = lean_ctor_get(v___x_4122_, 0);
lean_inc(v_a_4123_);
lean_dec_ref_known(v___x_4122_, 1);
v___x_4124_ = l_Lean_Elab_Do_DoElemCont_mkBindUnlessPure(v_a_4079_, v_a_4123_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
return v___x_4124_;
}
else
{
lean_dec(v_a_4079_);
return v___x_4122_;
}
}
}
}
else
{
lean_dec(v___x_4110_);
lean_dec(v_a_4079_);
return v___x_4113_;
}
}
else
{
lean_dec(v___x_4110_);
lean_dec(v_a_4079_);
return v___x_4111_;
}
}
else
{
lean_object* v_a_4127_; lean_object* v___x_4129_; uint8_t v_isShared_4130_; uint8_t v_isSharedCheck_4134_; 
lean_dec(v___y_4067_);
v_a_4127_ = lean_ctor_get(v___x_4077_, 0);
v_isSharedCheck_4134_ = !lean_is_exclusive(v___x_4077_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4129_ = v___x_4077_;
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
else
{
lean_inc(v_a_4127_);
lean_dec(v___x_4077_);
v___x_4129_ = lean_box(0);
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
v_resetjp_4128_:
{
lean_object* v___x_4132_; 
if (v_isShared_4130_ == 0)
{
v___x_4132_ = v___x_4129_;
goto v_reusejp_4131_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v_a_4127_);
v___x_4132_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4131_;
}
v_reusejp_4131_:
{
return v___x_4132_;
}
}
}
}
else
{
lean_object* v_a_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4142_; 
lean_dec(v___y_4067_);
lean_dec(v_tk_4065_);
lean_dec_ref(v_dec_4055_);
v_a_4135_ = lean_ctor_get(v___x_4076_, 0);
v_isSharedCheck_4142_ = !lean_is_exclusive(v___x_4076_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4137_ = v___x_4076_;
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
else
{
lean_inc(v_a_4135_);
lean_dec(v___x_4076_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
lean_object* v___x_4140_; 
if (v_isShared_4138_ == 0)
{
v___x_4140_ = v___x_4137_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v_a_4135_);
v___x_4140_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
return v___x_4140_;
}
}
}
}
v___jp_4143_:
{
lean_object* v___x_4152_; lean_object* v_env_4153_; lean_object* v___x_4154_; uint8_t v___x_4155_; uint8_t v___x_4156_; 
v___x_4152_ = lean_st_ref_get(v___y_4151_);
v_env_4153_ = lean_ctor_get(v___x_4152_, 0);
lean_inc_ref(v_env_4153_);
lean_dec(v___x_4152_);
v___x_4154_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__8));
v___x_4155_ = 1;
v___x_4156_ = l_Lean_Environment_contains(v_env_4153_, v___x_4154_, v___x_4155_);
if (v___x_4156_ == 0)
{
lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v_a_4159_; lean_object* v___x_4161_; uint8_t v_isShared_4162_; uint8_t v_isSharedCheck_4166_; 
lean_dec(v_as_4144_);
lean_dec_ref(v_dec_4055_);
v___x_4157_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__11, &l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__11_once, _init_l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__11);
v___x_4158_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg(v_tk_4065_, v___x_4157_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_);
lean_dec(v_tk_4065_);
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
v___y_4067_ = v_as_4144_;
v___y_4068_ = v___y_4145_;
v___y_4069_ = v___y_4146_;
v___y_4070_ = v___y_4147_;
v___y_4071_ = v___y_4148_;
v___y_4072_ = v___y_4149_;
v___y_4073_ = v___y_4150_;
v___y_4074_ = v___y_4151_;
goto v___jp_4066_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___boxed(lean_object* v_stx_4189_, lean_object* v_dec_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_){
_start:
{
lean_object* v_res_4199_; 
v_res_4199_ = l_Lean_Elab_Tactic_Do_elabDoAssertion(v_stx_4189_, v_dec_4190_, v_a_4191_, v_a_4192_, v_a_4193_, v_a_4194_, v_a_4195_, v_a_4196_, v_a_4197_);
lean_dec(v_a_4197_);
lean_dec_ref(v_a_4196_);
lean_dec(v_a_4195_);
lean_dec_ref(v_a_4194_);
lean_dec(v_a_4193_);
lean_dec_ref(v_a_4192_);
lean_dec_ref(v_a_4191_);
return v_res_4199_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1(lean_object* v_00_u03b1_4200_, lean_object* v_ref_4201_, lean_object* v_msg_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_){
_start:
{
lean_object* v___x_4211_; 
v___x_4211_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg(v_ref_4201_, v_msg_4202_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_);
return v___x_4211_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___boxed(lean_object* v_00_u03b1_4212_, lean_object* v_ref_4213_, lean_object* v_msg_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_){
_start:
{
lean_object* v_res_4223_; 
v_res_4223_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1(v_00_u03b1_4212_, v_ref_4213_, v_msg_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_);
lean_dec(v___y_4221_);
lean_dec_ref(v___y_4220_);
lean_dec(v___y_4219_);
lean_dec_ref(v___y_4218_);
lean_dec(v___y_4217_);
lean_dec_ref(v___y_4216_);
lean_dec_ref(v___y_4215_);
lean_dec(v_ref_4213_);
return v_res_4223_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2(lean_object* v_00_u03b1_4224_, lean_object* v_msg_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_){
_start:
{
lean_object* v___x_4234_; 
v___x_4234_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2___redArg(v_msg_4225_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_);
return v___x_4234_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2___boxed(lean_object* v_00_u03b1_4235_, lean_object* v_msg_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_){
_start:
{
lean_object* v_res_4245_; 
v_res_4245_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2(v_00_u03b1_4235_, v_msg_4236_, v___y_4237_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_);
lean_dec(v___y_4243_);
lean_dec_ref(v___y_4242_);
lean_dec(v___y_4241_);
lean_dec_ref(v___y_4240_);
lean_dec(v___y_4239_);
lean_dec_ref(v___y_4238_);
lean_dec_ref(v___y_4237_);
return v_res_4245_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2(lean_object* v_ref_4246_, lean_object* v_msgData_4247_, uint8_t v_severity_4248_, uint8_t v_isSilent_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_){
_start:
{
lean_object* v___x_4258_; 
v___x_4258_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg(v_ref_4246_, v_msgData_4247_, v_severity_4248_, v_isSilent_4249_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_);
return v___x_4258_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___boxed(lean_object* v_ref_4259_, lean_object* v_msgData_4260_, lean_object* v_severity_4261_, lean_object* v_isSilent_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_){
_start:
{
uint8_t v_severity_boxed_4271_; uint8_t v_isSilent_boxed_4272_; lean_object* v_res_4273_; 
v_severity_boxed_4271_ = lean_unbox(v_severity_4261_);
v_isSilent_boxed_4272_ = lean_unbox(v_isSilent_4262_);
v_res_4273_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2(v_ref_4259_, v_msgData_4260_, v_severity_boxed_4271_, v_isSilent_boxed_4272_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_);
lean_dec(v___y_4269_);
lean_dec_ref(v___y_4268_);
lean_dec(v___y_4267_);
lean_dec_ref(v___y_4266_);
lean_dec(v___y_4265_);
lean_dec_ref(v___y_4264_);
lean_dec_ref(v___y_4263_);
lean_dec(v_ref_4259_);
return v_res_4273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1(){
_start:
{
lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; 
v___x_4282_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4283_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__13));
v___x_4284_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___closed__1));
v___x_4285_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___boxed), 10, 0);
v___x_4286_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4282_, v___x_4283_, v___x_4284_, v___x_4285_);
return v___x_4286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___boxed(lean_object* v_a_4287_){
_start:
{
lean_object* v_res_4288_; 
v_res_4288_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1();
return v_res_4288_;
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
