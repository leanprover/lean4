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
lean_object* l_Lean_Meta_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Macro_hasDecl(lean_object*, lean_object*, lean_object*);
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
lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; uint8_t v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; uint8_t v___y_873_; lean_object* v___y_874_; lean_object* v___y_875_; lean_object* v_specTac_876_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___y_892_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; size_t v___y_897_; lean_object* v___y_898_; lean_object* v___y_899_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_903_; lean_object* v___y_904_; lean_object* v___y_905_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_914_; uint8_t v___y_915_; lean_object* v___y_916_; lean_object* v___y_917_; lean_object* v_a_918_; lean_object* v_a_919_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1029_; uint8_t v___y_1030_; size_t v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v_post_1036_; lean_object* v___y_1037_; lean_object* v_ref_1038_; lean_object* v___y_1039_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___y_1084_; lean_object* v___y_1085_; lean_object* v___y_1086_; uint8_t v___y_1087_; size_t v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1090_; lean_object* v___y_1091_; lean_object* v___y_1092_; lean_object* v_post_1093_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___x_1097_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; uint8_t v___y_1102_; lean_object* v___y_1103_; lean_object* v___y_1104_; lean_object* v___y_1105_; lean_object* v___y_1106_; lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; lean_object* v___y_1113_; lean_object* v___y_1114_; size_t v___y_1115_; uint8_t v___y_1116_; lean_object* v___y_1117_; lean_object* v___y_1118_; lean_object* v___y_1119_; lean_object* v_pre_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1185_; uint8_t v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1194_; lean_object* v___y_1195_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1199_; uint8_t v___y_1200_; size_t v___y_1201_; lean_object* v___y_1202_; lean_object* v___y_1203_; lean_object* v___y_1204_; lean_object* v___y_1205_; lean_object* v___y_1238_; lean_object* v___y_1239_; uint8_t v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; uint8_t v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v_decl_1269_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v___y_1281_; lean_object* v___y_1282_; lean_object* v___y_1283_; lean_object* v___y_1284_; lean_object* v___y_1303_; lean_object* v___y_1304_; lean_object* v___y_1305_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v___y_1308_; lean_object* v___y_1309_; lean_object* v___y_1310_; lean_object* v___y_1311_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___x_1423_; uint8_t v___x_1424_; 
v___x_1097_ = lean_unsigned_to_nat(1u);
v_decl_1269_ = l_Lean_Syntax_getArg(v_stx_628_, v___x_1097_);
v___x_1423_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__77));
lean_inc(v_decl_1269_);
v___x_1424_ = l_Lean_Syntax_isOfKind(v_decl_1269_, v___x_1423_);
if (v___x_1424_ == 0)
{
lean_object* v___x_1425_; 
v___x_1425_ = l_Lean_Macro_throwUnsupported___redArg(v_a_630_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_a_1426_; 
v_a_1426_ = lean_ctor_get(v___x_1425_, 1);
lean_inc(v_a_1426_);
lean_dec_ref_known(v___x_1425_, 2);
v___y_1406_ = v_a_629_;
v___y_1407_ = v_a_1426_;
goto v___jp_1405_;
}
else
{
lean_object* v_a_1427_; lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1435_; 
lean_dec(v_decl_1269_);
lean_dec(v_stx_628_);
v_a_1427_ = lean_ctor_get(v___x_1425_, 0);
v_a_1428_ = lean_ctor_get(v___x_1425_, 1);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1430_ = v___x_1425_;
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_inc(v_a_1427_);
lean_dec(v___x_1425_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_a_1427_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v_a_1428_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
else
{
v___y_1406_ = v_a_629_;
v___y_1407_ = v_a_630_;
goto v___jp_1405_;
}
v___jp_631_:
{
lean_object* v_quotContext_657_; lean_object* v_currMacroScope_658_; lean_object* v_ref_659_; lean_object* v___x_660_; lean_object* v_a_661_; lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_849_; 
v_quotContext_657_ = lean_ctor_get(v___y_634_, 1);
v_currMacroScope_658_ = lean_ctor_get(v___y_634_, 2);
v_ref_659_ = lean_ctor_get(v___y_634_, 5);
v___x_660_ = l_Lean_Elab_Tactic_Do_expandDefContract___lam__0(v_ref_659_, v___y_634_, v___y_651_);
v_a_661_ = lean_ctor_get(v___x_660_, 0);
v_a_662_ = lean_ctor_get(v___x_660_, 1);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_849_ == 0)
{
v___x_664_ = v___x_660_;
v_isShared_665_ = v_isSharedCheck_849_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_inc(v_a_661_);
lean_dec(v___x_660_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_849_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_666_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__0));
v___x_667_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__0));
lean_inc_ref_n(v___y_653_, 30);
lean_inc_ref_n(v___y_640_, 32);
v___x_668_ = l_Lean_Name_mkStr4(v___y_640_, v___y_653_, v___x_666_, v___x_667_);
v___x_669_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__1));
v___x_670_ = l_Lean_Name_mkStr4(v___y_640_, v___y_653_, v___x_666_, v___x_669_);
lean_inc_n(v_a_661_, 75);
v___x_671_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_671_, 0, v_a_661_);
lean_ctor_set(v___x_671_, 1, v___x_669_);
v___x_672_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__2));
v___x_673_ = l_Lean_Name_mkStr4(v___y_640_, v___y_653_, v___x_666_, v___x_672_);
v___x_674_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__3));
v___x_675_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_675_, 0, v_a_661_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
v___x_676_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_expandDefContract___closed__5, &l_Lean_Elab_Tactic_Do_expandDefContract___closed__5_once, _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__5);
lean_inc_ref(v___y_644_);
lean_inc_ref(v___y_648_);
v___x_677_ = l_Lean_Name_mkStr2(v___y_648_, v___y_644_);
lean_inc_n(v_currMacroScope_658_, 2);
lean_inc(v___x_677_);
lean_inc_n(v_quotContext_657_, 2);
v___x_678_ = l_Lean_addMacroScope(v_quotContext_657_, v___x_677_, v_currMacroScope_658_);
v___x_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_679_, 0, v___x_677_);
v___x_680_ = lean_box(0);
v___x_681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_681_, 0, v___x_679_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
v___x_682_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_682_, 0, v_a_661_);
lean_ctor_set(v___x_682_, 1, v___x_676_);
lean_ctor_set(v___x_682_, 2, v___x_678_);
lean_ctor_set(v___x_682_, 3, v___x_681_);
v___x_683_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_expandDefContract___closed__7, &l_Lean_Elab_Tactic_Do_expandDefContract___closed__7_once, _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__7);
lean_inc_ref(v___y_643_);
v___x_684_ = l_Lean_Name_mkStr2(v___y_640_, v___y_643_);
lean_inc(v___x_684_);
v___x_685_ = l_Lean_addMacroScope(v_quotContext_657_, v___x_684_, v_currMacroScope_658_);
v___x_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_686_, 0, v___x_684_);
v___x_687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
lean_ctor_set(v___x_687_, 1, v___x_680_);
v___x_688_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_688_, 0, v_a_661_);
lean_ctor_set(v___x_688_, 1, v___x_683_);
lean_ctor_set(v___x_688_, 2, v___x_685_);
lean_ctor_set(v___x_688_, 3, v___x_687_);
lean_inc_n(v___y_652_, 17);
v___x_689_ = l_Lean_Syntax_node2(v_a_661_, v___y_652_, v___x_682_, v___x_688_);
v___x_690_ = l_Lean_Syntax_node2(v_a_661_, v___x_673_, v___x_675_, v___x_689_);
v___x_691_ = l_Lean_Syntax_node2(v_a_661_, v___x_670_, v___x_671_, v___x_690_);
v___x_692_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_692_, 0, v_a_661_);
lean_ctor_set(v___x_692_, 1, v___x_667_);
v___x_693_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__8));
v___x_694_ = l_Lean_Name_mkStr4(v___y_640_, v___y_653_, v___x_666_, v___x_693_);
v___x_695_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__9));
v___x_696_ = l_Lean_Name_mkStr4(v___y_640_, v___y_653_, v___x_666_, v___x_695_);
lean_inc_ref(v___y_635_);
v___x_697_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_697_, 0, v_a_661_);
lean_ctor_set(v___x_697_, 1, v___y_652_);
lean_ctor_set(v___x_697_, 2, v___y_635_);
v___x_698_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__10));
lean_inc_ref_n(v___y_637_, 4);
v___x_699_ = l_Lean_Name_mkStr4(v___y_640_, v___y_653_, v___y_637_, v___x_698_);
v___x_700_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__11));
v___x_701_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_701_, 0, v_a_661_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
v___x_702_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__12));
v___x_703_ = l_Lean_Name_mkStr4(v___y_640_, v___y_653_, v___y_637_, v___x_702_);
v___x_704_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__13));
v___x_705_ = l_Lean_Name_mkStr4(v___y_640_, v___y_653_, v___y_637_, v___x_704_);
lean_inc_ref_n(v___x_697_, 24);
v___x_706_ = l_Lean_Syntax_node1(v_a_661_, v___x_705_, v___x_697_);
v___x_707_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__14));
lean_inc_ref_n(v___y_645_, 2);
v___x_708_ = l_Lean_Name_mkStr4(v___y_640_, v___y_653_, v___x_707_, v___y_645_);
v___x_709_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_709_, 0, v_a_661_);
lean_ctor_set(v___x_709_, 1, v___y_645_);
v___x_710_ = l_Lean_Syntax_node2(v_a_661_, v___x_708_, v___x_709_, v___x_697_);
v___x_711_ = l_Lean_Syntax_node2(v_a_661_, v___x_703_, v___x_706_, v___x_710_);
v___x_712_ = l_Lean_Syntax_node1(v_a_661_, v___y_652_, v___x_711_);
v___x_713_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__15));
v___x_714_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_714_, 0, v_a_661_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
lean_inc_ref(v___x_714_);
v___x_715_ = l_Lean_Syntax_node3(v_a_661_, v___x_699_, v___x_701_, v___x_712_, v___x_714_);
v___x_716_ = l_Lean_Syntax_node1(v_a_661_, v___y_652_, v___x_715_);
v___x_717_ = l_Lean_Syntax_node7(v_a_661_, v___x_696_, v___x_697_, v___x_716_, v___x_697_, v___x_697_, v___x_697_, v___x_697_, v___x_697_);
v___x_718_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__16));
v___x_719_ = l_Lean_Name_mkStr4(v___y_640_, v___y_653_, v___x_666_, v___x_718_);
v___x_720_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_720_, 0, v_a_661_);
lean_ctor_set(v___x_720_, 1, v___x_718_);
v___x_721_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__17));
v___x_722_ = l_Lean_Name_mkStr4(v___y_640_, v___y_653_, v___x_666_, v___x_721_);
v___x_723_ = lean_mk_empty_array_with_capacity(v___y_647_);
lean_inc_n(v___y_638_, 2);
v___x_724_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_724_, 0, v___y_638_);
lean_ctor_set(v___x_724_, 1, v___y_652_);
lean_ctor_set(v___x_724_, 2, v___x_723_);
v___x_725_ = lean_array_push(v___y_642_, v___y_654_);
v___x_726_ = lean_array_push(v___x_725_, v___x_724_);
v___x_727_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_727_, 0, v___y_638_);
lean_ctor_set(v___x_727_, 1, v___x_722_);
lean_ctor_set(v___x_727_, 2, v___x_726_);
v___x_728_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__18));
v___x_729_ = l_Lean_Name_mkStr4(v___y_640_, v___y_653_, v___x_666_, v___x_728_);
v___x_730_ = l_Array_append___redArg(v___y_635_, v___y_632_);
lean_dec_ref(v___y_632_);
v___x_731_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_731_, 0, v_a_661_);
lean_ctor_set(v___x_731_, 1, v___y_652_);
lean_ctor_set(v___x_731_, 2, v___x_730_);
v___x_732_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__19));
v___x_733_ = l_Lean_Name_mkStr4(v___y_640_, v___y_653_, v___y_637_, v___x_732_);
v___x_734_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__20));
v___x_735_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_735_, 0, v_a_661_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
v___x_736_ = l_Lean_Syntax_node2(v_a_661_, v___x_733_, v___x_735_, v___y_639_);
v___x_737_ = l_Lean_Syntax_node2(v_a_661_, v___x_729_, v___x_731_, v___x_736_);
v___x_738_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__1));
v___x_739_ = l_Lean_Name_mkStr4(v___y_640_, v___y_653_, v___x_666_, v___x_738_);
v___x_740_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__21));
v___x_741_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_741_, 0, v_a_661_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__22));
v___x_743_ = l_Lean_Name_mkStr4(v___y_640_, v___y_653_, v___y_637_, v___x_742_);
v___x_744_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__23));
v___x_745_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_745_, 0, v_a_661_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v___x_746_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__22));
v___x_747_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__24));
v___x_748_ = l_Lean_Name_mkStr4(v___y_640_, v___y_653_, v___x_746_, v___x_747_);
v___x_749_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__25));
v___x_750_ = l_Lean_Name_mkStr4(v___y_640_, v___y_653_, v___x_746_, v___x_749_);
v___x_751_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__26));
v___x_752_ = l_Lean_Name_mkStr4(v___y_640_, v___y_653_, v___x_746_, v___x_751_);
v___x_753_ = l_Lean_SourceInfo_fromRef(v___y_656_, v___y_650_);
lean_dec(v___y_656_);
v___x_754_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
lean_ctor_set(v___x_754_, 1, v___x_751_);
v___x_755_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__27));
v___x_756_ = l_Lean_Name_mkStr4(v___y_640_, v___y_653_, v___x_746_, v___x_755_);
v___x_757_ = l_Lean_Syntax_node1(v_a_661_, v___x_756_, v___x_697_);
v___x_758_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__28));
v___x_759_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_759_, 0, v_a_661_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
v___x_760_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__29));
v___x_761_ = l_Lean_Name_mkStr4(v___y_640_, v___y_653_, v___x_746_, v___x_760_);
v___x_762_ = l_Lean_Syntax_node3(v_a_661_, v___x_761_, v___x_697_, v___x_697_, v___y_649_);
v___x_763_ = l_Lean_Syntax_node1(v_a_661_, v___y_652_, v___x_762_);
v___x_764_ = l_Lean_Syntax_node3(v_a_661_, v___y_652_, v___x_759_, v___x_763_, v___x_714_);
v___x_765_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__30));
v___x_766_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_766_, 0, v_a_661_);
lean_ctor_set(v___x_766_, 1, v___x_765_);
v___x_767_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__31));
v___x_768_ = l_Lean_Name_mkStr4(v___y_640_, v___y_653_, v___x_746_, v___x_767_);
v___x_769_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__32));
v___x_770_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__12));
v___x_771_ = l_Lean_Name_mkStr5(v___y_640_, v___y_653_, v___x_746_, v___x_769_, v___x_770_);
v___x_772_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__16));
v___x_773_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_773_, 0, v_a_661_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
v___x_774_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__33));
v___x_775_ = l_Lean_Name_mkStr5(v___y_640_, v___y_653_, v___x_746_, v___x_769_, v___x_774_);
v___x_776_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__34));
v___x_777_ = l_Lean_Name_mkStr5(v___y_640_, v___y_653_, v___x_746_, v___x_769_, v___x_776_);
v___x_778_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__35));
v___x_779_ = l_Lean_Name_mkStr5(v___y_640_, v___y_653_, v___x_746_, v___x_769_, v___x_778_);
v___x_780_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__36));
v___x_781_ = l_Lean_Name_mkStr5(v___y_640_, v___y_653_, v___x_746_, v___x_769_, v___x_780_);
v___x_782_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__37));
v___x_783_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_783_, 0, v_a_661_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
v___x_784_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__38));
v___x_785_ = l_Lean_Name_mkStr5(v___y_640_, v___y_653_, v___x_746_, v___x_769_, v___x_784_);
v___x_786_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_786_, 0, v_a_661_);
lean_ctor_set(v___x_786_, 1, v___x_784_);
v___x_787_ = l_Lean_Syntax_node4(v_a_661_, v___x_785_, v___x_786_, v___x_697_, v___x_697_, v___x_697_);
lean_inc(v___x_779_);
v___x_788_ = l_Lean_Syntax_node2(v_a_661_, v___x_779_, v___x_787_, v___x_697_);
v___x_789_ = l_Lean_Syntax_node1(v_a_661_, v___y_652_, v___x_788_);
lean_inc(v___x_777_);
v___x_790_ = l_Lean_Syntax_node1(v_a_661_, v___x_777_, v___x_789_);
lean_inc(v___x_775_);
v___x_791_ = l_Lean_Syntax_node1(v_a_661_, v___x_775_, v___x_790_);
v___x_792_ = l_Lean_Syntax_node2(v_a_661_, v___x_781_, v___x_783_, v___x_791_);
v___x_793_ = l_Lean_Syntax_node2(v_a_661_, v___x_779_, v___x_792_, v___x_697_);
v___x_794_ = l_Lean_Syntax_node1(v_a_661_, v___y_652_, v___x_793_);
v___x_795_ = l_Lean_Syntax_node1(v_a_661_, v___x_777_, v___x_794_);
v___x_796_ = l_Lean_Syntax_node1(v_a_661_, v___x_775_, v___x_795_);
v___x_797_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__42));
v___x_798_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_798_, 0, v_a_661_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
v___x_799_ = l_Lean_Syntax_node3(v_a_661_, v___x_771_, v___x_773_, v___x_796_, v___x_798_);
v___x_800_ = l_Lean_Syntax_node1(v_a_661_, v___x_768_, v___x_799_);
v___x_801_ = l_Lean_Syntax_node2(v_a_661_, v___y_652_, v___x_766_, v___x_800_);
v___x_802_ = l_Lean_Syntax_node8(v_a_661_, v___x_752_, v___x_754_, v___x_757_, v___x_764_, v___x_697_, v___x_697_, v___x_697_, v___x_697_, v___x_801_);
v___x_803_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__39));
v___x_804_ = l_Lean_Name_mkStr4(v___y_640_, v___y_653_, v___x_746_, v___x_803_);
v___x_805_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_805_, 0, v_a_661_);
lean_ctor_set(v___x_805_, 1, v___x_803_);
v___x_806_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__41));
v___x_807_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__42));
v___x_808_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_808_, 0, v_a_661_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v___x_809_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__43));
v___x_810_ = l_Lean_Name_mkStr4(v___y_640_, v___y_653_, v___x_746_, v___x_809_);
v___x_811_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_811_, 0, v_a_661_);
lean_ctor_set(v___x_811_, 1, v___x_809_);
v___x_812_ = l_Lean_Syntax_node1(v_a_661_, v___x_810_, v___x_811_);
v___x_813_ = l_Lean_Syntax_node1(v_a_661_, v___y_652_, v___x_812_);
lean_inc_n(v___x_750_, 2);
v___x_814_ = l_Lean_Syntax_node1(v_a_661_, v___x_750_, v___x_813_);
lean_inc_n(v___x_748_, 2);
v___x_815_ = l_Lean_Syntax_node1(v_a_661_, v___x_748_, v___x_814_);
lean_inc_ref(v___x_808_);
v___x_816_ = l_Lean_Syntax_node2(v_a_661_, v___x_806_, v___x_808_, v___x_815_);
v___x_817_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__44));
v___x_818_ = l_Lean_Name_mkStr4(v___y_640_, v___y_653_, v___x_746_, v___x_817_);
v___x_819_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_819_, 0, v_a_661_);
lean_ctor_set(v___x_819_, 1, v___x_817_);
v___x_820_ = l_Lean_Syntax_node1(v_a_661_, v___y_652_, v___y_641_);
v___x_821_ = l_Lean_Syntax_node2(v_a_661_, v___x_818_, v___x_819_, v___x_820_);
v___x_822_ = l_Lean_Syntax_node1(v_a_661_, v___y_652_, v___x_821_);
v___x_823_ = l_Lean_Syntax_node1(v_a_661_, v___x_750_, v___x_822_);
v___x_824_ = l_Lean_Syntax_node1(v_a_661_, v___x_748_, v___x_823_);
v___x_825_ = l_Lean_Syntax_node2(v_a_661_, v___x_806_, v___x_808_, v___x_824_);
v___x_826_ = l_Lean_Syntax_node2(v_a_661_, v___y_652_, v___x_816_, v___x_825_);
v___x_827_ = l_Lean_Syntax_node2(v_a_661_, v___x_804_, v___x_805_, v___x_826_);
v___x_828_ = l_Lean_Syntax_node5(v_a_661_, v___y_652_, v___x_802_, v___x_697_, v___y_636_, v___x_697_, v___x_827_);
v___x_829_ = l_Lean_Syntax_node1(v_a_661_, v___x_750_, v___x_828_);
v___x_830_ = l_Lean_Syntax_node1(v_a_661_, v___x_748_, v___x_829_);
v___x_831_ = l_Lean_Syntax_node2(v_a_661_, v___x_743_, v___x_745_, v___x_830_);
v___x_832_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__45));
v___x_833_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__46));
v___x_834_ = l_Lean_Name_mkStr4(v___y_640_, v___y_653_, v___x_832_, v___x_833_);
v___x_835_ = l_Lean_Syntax_node2(v_a_661_, v___x_834_, v___x_697_, v___x_697_);
v___x_836_ = l_Lean_Syntax_node4(v_a_661_, v___x_739_, v___x_741_, v___x_831_, v___x_835_, v___x_697_);
v___x_837_ = l_Lean_Syntax_node4(v_a_661_, v___x_719_, v___x_720_, v___x_727_, v___x_737_, v___x_836_);
v___x_838_ = l_Lean_Syntax_node2(v_a_661_, v___x_694_, v___x_717_, v___x_837_);
v___x_839_ = l_Lean_Syntax_node3(v_a_661_, v___x_668_, v___x_691_, v___x_692_, v___x_838_);
v___x_840_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice(v___y_646_);
lean_dec(v___y_646_);
v___x_841_ = lean_mk_empty_array_with_capacity(v___y_633_);
v___x_842_ = lean_array_push(v___x_841_, v___x_840_);
v___x_843_ = lean_array_push(v___x_842_, v___y_655_);
v___x_844_ = lean_array_push(v___x_843_, v___x_839_);
v___x_845_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_845_, 0, v___y_638_);
lean_ctor_set(v___x_845_, 1, v___y_652_);
lean_ctor_set(v___x_845_, 2, v___x_844_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v___x_845_);
v___x_847_ = v___x_664_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_845_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v_a_662_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
v___jp_850_:
{
uint8_t v___x_879_; 
v___x_879_ = l_Lean_Syntax_isNone(v___y_857_);
if (v___x_879_ == 0)
{
lean_object* v___x_880_; lean_object* v___x_881_; 
lean_dec(v___y_875_);
lean_dec(v___y_871_);
lean_dec(v___y_864_);
v___x_880_ = l_Lean_Syntax_getArg(v___y_857_, v___y_856_);
lean_dec(v___y_857_);
v___x_881_ = l_Lean_Syntax_getArg(v___x_880_, v___y_856_);
lean_dec(v___x_880_);
v___y_632_ = v___y_862_;
v___y_633_ = v___y_851_;
v___y_634_ = v___y_877_;
v___y_635_ = v___y_863_;
v___y_636_ = v_specTac_876_;
v___y_637_ = v___y_852_;
v___y_638_ = v___y_865_;
v___y_639_ = v___y_853_;
v___y_640_ = v___y_866_;
v___y_641_ = v___y_867_;
v___y_642_ = v___y_854_;
v___y_643_ = v___y_868_;
v___y_644_ = v___y_870_;
v___y_645_ = v___y_869_;
v___y_646_ = v___y_855_;
v___y_647_ = v___y_856_;
v___y_648_ = v___y_858_;
v___y_649_ = v___y_872_;
v___y_650_ = v___y_873_;
v___y_651_ = v___y_878_;
v___y_652_ = v___y_874_;
v___y_653_ = v___y_859_;
v___y_654_ = v___y_860_;
v___y_655_ = v___y_861_;
v___y_656_ = v___x_881_;
goto v___jp_631_;
}
else
{
uint8_t v___x_882_; 
lean_dec(v___y_857_);
v___x_882_ = l_Lean_Syntax_isNone(v___y_864_);
if (v___x_882_ == 0)
{
lean_object* v___x_883_; lean_object* v___x_884_; 
lean_dec(v___y_875_);
lean_dec(v___y_871_);
v___x_883_ = l_Lean_Syntax_getArg(v___y_864_, v___y_856_);
lean_dec(v___y_864_);
v___x_884_ = l_Lean_Syntax_getArg(v___x_883_, v___y_856_);
lean_dec(v___x_883_);
v___y_632_ = v___y_862_;
v___y_633_ = v___y_851_;
v___y_634_ = v___y_877_;
v___y_635_ = v___y_863_;
v___y_636_ = v_specTac_876_;
v___y_637_ = v___y_852_;
v___y_638_ = v___y_865_;
v___y_639_ = v___y_853_;
v___y_640_ = v___y_866_;
v___y_641_ = v___y_867_;
v___y_642_ = v___y_854_;
v___y_643_ = v___y_868_;
v___y_644_ = v___y_870_;
v___y_645_ = v___y_869_;
v___y_646_ = v___y_855_;
v___y_647_ = v___y_856_;
v___y_648_ = v___y_858_;
v___y_649_ = v___y_872_;
v___y_650_ = v___y_873_;
v___y_651_ = v___y_878_;
v___y_652_ = v___y_874_;
v___y_653_ = v___y_859_;
v___y_654_ = v___y_860_;
v___y_655_ = v___y_861_;
v___y_656_ = v___x_884_;
goto v___jp_631_;
}
else
{
lean_object* v___x_885_; uint8_t v___x_886_; 
lean_dec(v___y_864_);
v___x_885_ = l_Lean_Syntax_getNumArgs(v___y_875_);
v___x_886_ = lean_nat_dec_lt(v___y_856_, v___x_885_);
lean_dec(v___x_885_);
if (v___x_886_ == 0)
{
lean_object* v___x_887_; lean_object* v___x_888_; 
lean_dec(v___y_875_);
v___x_887_ = l_Lean_Syntax_getArg(v___y_871_, v___y_856_);
lean_dec(v___y_871_);
v___x_888_ = l_Lean_Syntax_getArg(v___x_887_, v___y_856_);
lean_dec(v___x_887_);
v___y_632_ = v___y_862_;
v___y_633_ = v___y_851_;
v___y_634_ = v___y_877_;
v___y_635_ = v___y_863_;
v___y_636_ = v_specTac_876_;
v___y_637_ = v___y_852_;
v___y_638_ = v___y_865_;
v___y_639_ = v___y_853_;
v___y_640_ = v___y_866_;
v___y_641_ = v___y_867_;
v___y_642_ = v___y_854_;
v___y_643_ = v___y_868_;
v___y_644_ = v___y_870_;
v___y_645_ = v___y_869_;
v___y_646_ = v___y_855_;
v___y_647_ = v___y_856_;
v___y_648_ = v___y_858_;
v___y_649_ = v___y_872_;
v___y_650_ = v___y_873_;
v___y_651_ = v___y_878_;
v___y_652_ = v___y_874_;
v___y_653_ = v___y_859_;
v___y_654_ = v___y_860_;
v___y_655_ = v___y_861_;
v___y_656_ = v___x_888_;
goto v___jp_631_;
}
else
{
lean_object* v___x_889_; lean_object* v___x_890_; 
lean_dec(v___y_871_);
v___x_889_ = l_Lean_Syntax_getArg(v___y_875_, v___y_856_);
lean_dec(v___y_875_);
v___x_890_ = l_Lean_Syntax_getArg(v___x_889_, v___y_856_);
lean_dec(v___x_889_);
v___y_632_ = v___y_862_;
v___y_633_ = v___y_851_;
v___y_634_ = v___y_877_;
v___y_635_ = v___y_863_;
v___y_636_ = v_specTac_876_;
v___y_637_ = v___y_852_;
v___y_638_ = v___y_865_;
v___y_639_ = v___y_853_;
v___y_640_ = v___y_866_;
v___y_641_ = v___y_867_;
v___y_642_ = v___y_854_;
v___y_643_ = v___y_868_;
v___y_644_ = v___y_870_;
v___y_645_ = v___y_869_;
v___y_646_ = v___y_855_;
v___y_647_ = v___y_856_;
v___y_648_ = v___y_858_;
v___y_649_ = v___y_872_;
v___y_650_ = v___y_873_;
v___y_651_ = v___y_878_;
v___y_652_ = v___y_874_;
v___y_653_ = v___y_859_;
v___y_654_ = v___y_860_;
v___y_655_ = v___y_861_;
v___y_656_ = v___x_890_;
goto v___jp_631_;
}
}
}
}
v___jp_891_:
{
lean_object* v___x_920_; lean_object* v_a_921_; lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_1013_; 
v___x_920_ = l_Lean_Elab_Tactic_Do_expandDefContract___lam__0(v___y_911_, v___y_917_, v_a_919_);
v_a_921_ = lean_ctor_get(v___x_920_, 0);
v_a_922_ = lean_ctor_get(v___x_920_, 1);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_924_ = v___x_920_;
v_isShared_925_ = v_isSharedCheck_1013_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_inc(v_a_921_);
lean_dec(v___x_920_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_1013_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_940_; 
v___x_926_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1));
v___x_927_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__2));
v___x_928_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__47));
lean_inc_ref(v___y_904_);
v___x_929_ = l_Lean_Name_mkStr4(v___y_904_, v___x_926_, v___x_927_, v___x_928_);
v___x_930_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_expandDefContract___closed__49, &l_Lean_Elab_Tactic_Do_expandDefContract___closed__49_once, _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__49);
v___x_931_ = lean_mk_empty_array_with_capacity(v___y_910_);
lean_inc_ref(v___x_931_);
v___x_932_ = lean_array_push(v___x_931_, v___x_930_);
v___x_933_ = lean_array_push(v___x_932_, v_a_918_);
v___x_934_ = lean_box(2);
v___x_935_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
lean_ctor_set(v___x_935_, 1, v___x_929_);
lean_ctor_set(v___x_935_, 2, v___x_933_);
v___x_936_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__50));
lean_inc_ref(v___y_908_);
lean_inc_ref(v___y_896_);
v___x_937_ = l_Lean_Name_mkStr3(v___y_896_, v___y_908_, v___x_936_);
v___x_938_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__51));
lean_inc(v_a_921_);
if (v_isShared_925_ == 0)
{
lean_ctor_set_tag(v___x_924_, 2);
lean_ctor_set(v___x_924_, 1, v___x_938_);
v___x_940_ = v___x_924_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_921_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v___x_938_);
v___x_940_ = v_reuseFailAlloc_1012_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; size_t v_sz_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_941_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__52));
lean_inc_n(v_a_921_, 5);
v___x_942_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_942_, 0, v_a_921_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
v___x_943_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__2));
v___x_944_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_expandDefContract___closed__53, &l_Lean_Elab_Tactic_Do_expandDefContract___closed__53_once, _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__53);
v___x_945_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_945_, 0, v_a_921_);
lean_ctor_set(v___x_945_, 1, v___x_943_);
lean_ctor_set(v___x_945_, 2, v___x_944_);
v___x_946_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__6));
lean_inc_ref(v___y_904_);
v___x_947_ = l_Lean_Name_mkStr4(v___y_904_, v___x_926_, v___x_927_, v___x_946_);
v_sz_948_ = lean_array_size(v___y_898_);
v___x_949_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__1(v_sz_948_, v___y_897_, v___y_898_);
v___x_950_ = l_Array_append___redArg(v___x_944_, v___x_949_);
lean_dec_ref(v___x_949_);
v___x_951_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_951_, 0, v_a_921_);
lean_ctor_set(v___x_951_, 1, v___x_943_);
lean_ctor_set(v___x_951_, 2, v___x_950_);
lean_inc(v___y_913_);
v___x_952_ = l_Lean_Syntax_node2(v_a_921_, v___x_947_, v___y_913_, v___x_951_);
v___x_953_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__54));
v___x_954_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_954_, 0, v_a_921_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = lean_unsigned_to_nat(10u);
v___x_956_ = lean_mk_empty_array_with_capacity(v___x_955_);
lean_inc_ref(v___x_940_);
v___x_957_ = lean_array_push(v___x_956_, v___x_940_);
v___x_958_ = lean_array_push(v___x_957_, v___y_902_);
lean_inc_ref(v___x_942_);
v___x_959_ = lean_array_push(v___x_958_, v___x_942_);
v___x_960_ = lean_array_push(v___x_959_, v___x_945_);
v___x_961_ = lean_array_push(v___x_960_, v___x_952_);
v___x_962_ = lean_array_push(v___x_961_, v___x_940_);
v___x_963_ = lean_array_push(v___x_962_, v___y_905_);
v___x_964_ = lean_array_push(v___x_963_, v___x_954_);
v___x_965_ = lean_array_push(v___x_964_, v___x_935_);
v___x_966_ = lean_array_push(v___x_965_, v___x_942_);
v___x_967_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_967_, 0, v_a_921_);
lean_ctor_set(v___x_967_, 1, v___x_937_);
lean_ctor_set(v___x_967_, 2, v___x_966_);
if (lean_obj_tag(v___y_906_) == 0)
{
lean_object* v___x_968_; lean_object* v_a_969_; lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_987_; 
v___x_968_ = l_Lean_Elab_Tactic_Do_expandDefContract___lam__0(v___y_911_, v___y_917_, v_a_922_);
v_a_969_ = lean_ctor_get(v___x_968_, 0);
v_a_970_ = lean_ctor_get(v___x_968_, 1);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_987_ == 0)
{
v___x_972_ = v___x_968_;
v_isShared_973_ = v_isSharedCheck_987_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_inc(v_a_969_);
lean_dec(v___x_968_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_987_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_984_; 
v___x_974_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__55));
v___x_975_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_914_, v___y_915_);
v___x_976_ = lean_string_append(v___x_974_, v___x_975_);
lean_dec_ref(v___x_975_);
v___x_977_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__56));
v___x_978_ = lean_string_append(v___x_976_, v___x_977_);
v___x_979_ = l_Lean_Syntax_mkStrLit(v___x_978_, v___x_934_);
v___x_980_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__22));
v___x_981_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__57));
lean_inc_ref(v___y_904_);
v___x_982_ = l_Lean_Name_mkStr4(v___y_904_, v___x_926_, v___x_980_, v___x_981_);
lean_inc(v_a_969_);
if (v_isShared_973_ == 0)
{
lean_ctor_set_tag(v___x_972_, 2);
lean_ctor_set(v___x_972_, 1, v___x_981_);
v___x_984_ = v___x_972_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_969_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v___x_981_);
v___x_984_ = v_reuseFailAlloc_986_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
lean_object* v___x_985_; 
v___x_985_ = l_Lean_Syntax_node1(v_a_969_, v___x_982_, v___x_984_);
v___y_851_ = v___y_892_;
v___y_852_ = v___x_927_;
v___y_853_ = v___x_967_;
v___y_854_ = v___x_931_;
v___y_855_ = v___y_893_;
v___y_856_ = v___y_895_;
v___y_857_ = v___y_894_;
v___y_858_ = v___y_896_;
v___y_859_ = v___x_926_;
v___y_860_ = v___y_899_;
v___y_861_ = v___y_900_;
v___y_862_ = v___y_901_;
v___y_863_ = v___x_944_;
v___y_864_ = v___y_903_;
v___y_865_ = v___x_934_;
v___y_866_ = v___y_904_;
v___y_867_ = v___x_979_;
v___y_868_ = v___y_907_;
v___y_869_ = v___y_909_;
v___y_870_ = v___y_908_;
v___y_871_ = v___y_912_;
v___y_872_ = v___y_913_;
v___y_873_ = v___y_915_;
v___y_874_ = v___x_943_;
v___y_875_ = v___y_916_;
v_specTac_876_ = v___x_985_;
v___y_877_ = v___y_917_;
v___y_878_ = v_a_970_;
goto v___jp_850_;
}
}
}
else
{
lean_object* v_val_988_; lean_object* v___x_989_; lean_object* v_a_990_; lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1011_; 
v_val_988_ = lean_ctor_get(v___y_906_, 0);
lean_inc(v_val_988_);
lean_dec_ref_known(v___y_906_, 1);
v___x_989_ = l_Lean_Elab_Tactic_Do_expandDefContract___lam__0(v___y_911_, v___y_917_, v_a_922_);
v_a_990_ = lean_ctor_get(v___x_989_, 0);
v_a_991_ = lean_ctor_get(v___x_989_, 1);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_993_ = v___x_989_;
v_isShared_994_ = v_isSharedCheck_1011_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_inc(v_a_990_);
lean_dec(v___x_989_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1011_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1006_; 
v___x_995_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__55));
v___x_996_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_914_, v___y_915_);
v___x_997_ = lean_string_append(v___x_995_, v___x_996_);
lean_dec_ref(v___x_996_);
v___x_998_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__58));
v___x_999_ = lean_string_append(v___x_997_, v___x_998_);
v___x_1000_ = l_Lean_Syntax_mkStrLit(v___x_999_, v___x_934_);
v___x_1001_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__22));
v___x_1002_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__12));
lean_inc_ref(v___y_904_);
v___x_1003_ = l_Lean_Name_mkStr4(v___y_904_, v___x_926_, v___x_1001_, v___x_1002_);
v___x_1004_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__16));
lean_inc(v_a_990_);
if (v_isShared_994_ == 0)
{
lean_ctor_set_tag(v___x_993_, 2);
lean_ctor_set(v___x_993_, 1, v___x_1004_);
v___x_1006_ = v___x_993_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_a_990_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v___x_1004_);
v___x_1006_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1007_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__42));
lean_inc(v_a_990_);
v___x_1008_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1008_, 0, v_a_990_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
v___x_1009_ = l_Lean_Syntax_node3(v_a_990_, v___x_1003_, v___x_1006_, v_val_988_, v___x_1008_);
v___y_851_ = v___y_892_;
v___y_852_ = v___x_927_;
v___y_853_ = v___x_967_;
v___y_854_ = v___x_931_;
v___y_855_ = v___y_893_;
v___y_856_ = v___y_895_;
v___y_857_ = v___y_894_;
v___y_858_ = v___y_896_;
v___y_859_ = v___x_926_;
v___y_860_ = v___y_899_;
v___y_861_ = v___y_900_;
v___y_862_ = v___y_901_;
v___y_863_ = v___x_944_;
v___y_864_ = v___y_903_;
v___y_865_ = v___x_934_;
v___y_866_ = v___y_904_;
v___y_867_ = v___x_1000_;
v___y_868_ = v___y_907_;
v___y_869_ = v___y_909_;
v___y_870_ = v___y_908_;
v___y_871_ = v___y_912_;
v___y_872_ = v___y_913_;
v___y_873_ = v___y_915_;
v___y_874_ = v___x_943_;
v___y_875_ = v___y_916_;
v_specTac_876_ = v___x_1009_;
v___y_877_ = v___y_917_;
v___y_878_ = v_a_991_;
goto v___jp_850_;
}
}
}
}
}
}
v___jp_1014_:
{
lean_object* v___x_1040_; lean_object* v_a_1041_; lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1070_; 
v___x_1040_ = l_Lean_Elab_Tactic_Do_expandDefContract___lam__0(v_ref_1038_, v___y_1037_, v___y_1039_);
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
v_a_1042_ = lean_ctor_get(v___x_1040_, 1);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1044_ = v___x_1040_;
v_isShared_1045_ = v_isSharedCheck_1070_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_inc(v_a_1041_);
lean_dec(v___x_1040_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1070_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1051_; 
v___x_1046_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0));
v___x_1047_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__26));
v___x_1048_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__60));
v___x_1049_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__61));
lean_inc(v_a_1041_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set_tag(v___x_1044_, 2);
lean_ctor_set(v___x_1044_, 1, v___x_1049_);
v___x_1051_ = v___x_1044_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1041_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v___x_1049_);
v___x_1051_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; uint8_t v___x_1055_; 
v___x_1052_ = l_Lean_Syntax_node1(v_a_1041_, v___x_1048_, v___x_1051_);
v___x_1053_ = l_Lean_Syntax_getArgs(v___y_1033_);
v___x_1054_ = lean_array_get_size(v___x_1053_);
v___x_1055_ = lean_nat_dec_lt(v___y_1025_, v___x_1054_);
if (v___x_1055_ == 0)
{
lean_dec_ref(v___x_1053_);
v___y_892_ = v___y_1016_;
v___y_893_ = v___y_1023_;
v___y_894_ = v___y_1024_;
v___y_895_ = v___y_1025_;
v___y_896_ = v___y_1026_;
v___y_897_ = v___y_1031_;
v___y_898_ = v___y_1032_;
v___y_899_ = v___y_1034_;
v___y_900_ = v___y_1035_;
v___y_901_ = v___y_1015_;
v___y_902_ = v___y_1017_;
v___y_903_ = v___y_1018_;
v___y_904_ = v___x_1046_;
v___y_905_ = v_post_1036_;
v___y_906_ = v___y_1019_;
v___y_907_ = v___x_1047_;
v___y_908_ = v___y_1021_;
v___y_909_ = v___y_1020_;
v___y_910_ = v___y_1022_;
v___y_911_ = v_ref_1038_;
v___y_912_ = v___y_1027_;
v___y_913_ = v___y_1028_;
v___y_914_ = v___y_1029_;
v___y_915_ = v___y_1030_;
v___y_916_ = v___y_1033_;
v___y_917_ = v___y_1037_;
v_a_918_ = v___x_1052_;
v_a_919_ = v_a_1042_;
goto v___jp_891_;
}
else
{
size_t v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = lean_usize_of_nat(v___x_1054_);
v___x_1057_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2(v___x_1053_, v___x_1056_, v___y_1031_, v___x_1052_, v___y_1037_, v_a_1042_);
lean_dec_ref(v___x_1053_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v_a_1058_; lean_object* v_a_1059_; 
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_a_1058_);
v_a_1059_ = lean_ctor_get(v___x_1057_, 1);
lean_inc(v_a_1059_);
lean_dec_ref_known(v___x_1057_, 2);
v___y_892_ = v___y_1016_;
v___y_893_ = v___y_1023_;
v___y_894_ = v___y_1024_;
v___y_895_ = v___y_1025_;
v___y_896_ = v___y_1026_;
v___y_897_ = v___y_1031_;
v___y_898_ = v___y_1032_;
v___y_899_ = v___y_1034_;
v___y_900_ = v___y_1035_;
v___y_901_ = v___y_1015_;
v___y_902_ = v___y_1017_;
v___y_903_ = v___y_1018_;
v___y_904_ = v___x_1046_;
v___y_905_ = v_post_1036_;
v___y_906_ = v___y_1019_;
v___y_907_ = v___x_1047_;
v___y_908_ = v___y_1021_;
v___y_909_ = v___y_1020_;
v___y_910_ = v___y_1022_;
v___y_911_ = v_ref_1038_;
v___y_912_ = v___y_1027_;
v___y_913_ = v___y_1028_;
v___y_914_ = v___y_1029_;
v___y_915_ = v___y_1030_;
v___y_916_ = v___y_1033_;
v___y_917_ = v___y_1037_;
v_a_918_ = v_a_1058_;
v_a_919_ = v_a_1059_;
goto v___jp_891_;
}
else
{
lean_object* v_a_1060_; lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
lean_dec(v_post_1036_);
lean_dec(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec(v___y_1024_);
lean_dec(v___y_1023_);
lean_dec(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1015_);
v_a_1060_ = lean_ctor_get(v___x_1057_, 0);
v_a_1061_ = lean_ctor_get(v___x_1057_, 1);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_1057_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_inc(v_a_1060_);
lean_dec(v___x_1057_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1060_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v_a_1061_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
}
}
}
v___jp_1071_:
{
lean_object* v_ref_1096_; 
v_ref_1096_ = lean_ctor_get(v___y_1094_, 5);
v___y_1015_ = v___y_1072_;
v___y_1016_ = v___y_1073_;
v___y_1017_ = v___y_1074_;
v___y_1018_ = v___y_1075_;
v___y_1019_ = v___y_1076_;
v___y_1020_ = v___y_1077_;
v___y_1021_ = v___y_1078_;
v___y_1022_ = v___y_1079_;
v___y_1023_ = v___y_1080_;
v___y_1024_ = v___y_1081_;
v___y_1025_ = v___y_1082_;
v___y_1026_ = v___y_1083_;
v___y_1027_ = v___y_1084_;
v___y_1028_ = v___y_1085_;
v___y_1029_ = v___y_1086_;
v___y_1030_ = v___y_1087_;
v___y_1031_ = v___y_1088_;
v___y_1032_ = v___y_1089_;
v___y_1033_ = v___y_1090_;
v___y_1034_ = v___y_1091_;
v___y_1035_ = v___y_1092_;
v_post_1036_ = v_post_1093_;
v___y_1037_ = v___y_1094_;
v_ref_1038_ = v_ref_1096_;
v___y_1039_ = v___y_1095_;
goto v___jp_1014_;
}
v___jp_1098_:
{
uint8_t v___x_1123_; 
v___x_1123_ = l_Lean_Syntax_isNone(v___y_1101_);
if (v___x_1123_ == 0)
{
lean_object* v___x_1124_; lean_object* v___x_1125_; uint8_t v___x_1126_; 
v___x_1124_ = l_Lean_Syntax_getArg(v___y_1101_, v___y_1109_);
v___x_1125_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__63));
lean_inc(v___x_1124_);
v___x_1126_ = l_Lean_Syntax_isOfKind(v___x_1124_, v___x_1125_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1127_; 
lean_dec(v___x_1124_);
v___x_1127_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1122_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; lean_object* v_a_1129_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_a_1128_);
v_a_1129_ = lean_ctor_get(v___x_1127_, 1);
lean_inc(v_a_1129_);
lean_dec_ref_known(v___x_1127_, 2);
v___y_1072_ = v___y_1099_;
v___y_1073_ = v___y_1100_;
v___y_1074_ = v_pre_1120_;
v___y_1075_ = v___y_1101_;
v___y_1076_ = v___y_1103_;
v___y_1077_ = v___y_1104_;
v___y_1078_ = v___y_1105_;
v___y_1079_ = v___y_1106_;
v___y_1080_ = v___y_1107_;
v___y_1081_ = v___y_1108_;
v___y_1082_ = v___y_1109_;
v___y_1083_ = v___y_1110_;
v___y_1084_ = v___y_1111_;
v___y_1085_ = v___y_1112_;
v___y_1086_ = v___y_1113_;
v___y_1087_ = v___y_1116_;
v___y_1088_ = v___y_1115_;
v___y_1089_ = v___y_1114_;
v___y_1090_ = v___y_1117_;
v___y_1091_ = v___y_1118_;
v___y_1092_ = v___y_1119_;
v_post_1093_ = v_a_1128_;
v___y_1094_ = v___y_1121_;
v___y_1095_ = v_a_1129_;
goto v___jp_1071_;
}
else
{
lean_object* v_a_1130_; lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
lean_dec(v_pre_1120_);
lean_dec(v___y_1119_);
lean_dec(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec(v___y_1112_);
lean_dec(v___y_1111_);
lean_dec(v___y_1108_);
lean_dec(v___y_1107_);
lean_dec(v___y_1103_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1099_);
v_a_1130_ = lean_ctor_get(v___x_1127_, 0);
v_a_1131_ = lean_ctor_get(v___x_1127_, 1);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1127_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_inc(v_a_1130_);
lean_dec(v___x_1127_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1130_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v_a_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
else
{
lean_object* v___x_1139_; lean_object* v___x_1140_; uint8_t v___x_1141_; 
v___x_1139_ = l_Lean_Syntax_getArg(v___x_1124_, v___x_1097_);
lean_dec(v___x_1124_);
v___x_1140_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__3));
lean_inc(v___x_1139_);
v___x_1141_ = l_Lean_Syntax_isOfKind(v___x_1139_, v___x_1140_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; 
lean_dec(v___x_1139_);
v___x_1142_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1122_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; lean_object* v_a_1144_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
lean_inc(v_a_1143_);
v_a_1144_ = lean_ctor_get(v___x_1142_, 1);
lean_inc(v_a_1144_);
lean_dec_ref_known(v___x_1142_, 2);
v___y_1072_ = v___y_1099_;
v___y_1073_ = v___y_1100_;
v___y_1074_ = v_pre_1120_;
v___y_1075_ = v___y_1101_;
v___y_1076_ = v___y_1103_;
v___y_1077_ = v___y_1104_;
v___y_1078_ = v___y_1105_;
v___y_1079_ = v___y_1106_;
v___y_1080_ = v___y_1107_;
v___y_1081_ = v___y_1108_;
v___y_1082_ = v___y_1109_;
v___y_1083_ = v___y_1110_;
v___y_1084_ = v___y_1111_;
v___y_1085_ = v___y_1112_;
v___y_1086_ = v___y_1113_;
v___y_1087_ = v___y_1116_;
v___y_1088_ = v___y_1115_;
v___y_1089_ = v___y_1114_;
v___y_1090_ = v___y_1117_;
v___y_1091_ = v___y_1118_;
v___y_1092_ = v___y_1119_;
v_post_1093_ = v_a_1143_;
v___y_1094_ = v___y_1121_;
v___y_1095_ = v_a_1144_;
goto v___jp_1071_;
}
else
{
lean_object* v_a_1145_; lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
lean_dec(v_pre_1120_);
lean_dec(v___y_1119_);
lean_dec(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec(v___y_1112_);
lean_dec(v___y_1111_);
lean_dec(v___y_1108_);
lean_dec(v___y_1107_);
lean_dec(v___y_1103_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1099_);
v_a_1145_ = lean_ctor_get(v___x_1142_, 0);
v_a_1146_ = lean_ctor_get(v___x_1142_, 1);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1148_ = v___x_1142_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_inc(v_a_1145_);
lean_dec(v___x_1142_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1145_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v_a_1146_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
else
{
lean_object* v_ref_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v_ref_1154_ = lean_ctor_get(v___y_1121_, 5);
v___x_1155_ = l_Lean_SourceInfo_fromRef(v_ref_1154_, v___x_1123_);
v___x_1156_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__40));
v___x_1157_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__41));
lean_inc(v___x_1155_);
v___x_1158_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1155_);
lean_ctor_set(v___x_1158_, 1, v___x_1156_);
v___x_1159_ = l_Lean_Syntax_node2(v___x_1155_, v___x_1157_, v___x_1158_, v___x_1139_);
v___y_1015_ = v___y_1099_;
v___y_1016_ = v___y_1100_;
v___y_1017_ = v_pre_1120_;
v___y_1018_ = v___y_1101_;
v___y_1019_ = v___y_1103_;
v___y_1020_ = v___y_1104_;
v___y_1021_ = v___y_1105_;
v___y_1022_ = v___y_1106_;
v___y_1023_ = v___y_1107_;
v___y_1024_ = v___y_1108_;
v___y_1025_ = v___y_1109_;
v___y_1026_ = v___y_1110_;
v___y_1027_ = v___y_1111_;
v___y_1028_ = v___y_1112_;
v___y_1029_ = v___y_1113_;
v___y_1030_ = v___y_1116_;
v___y_1031_ = v___y_1115_;
v___y_1032_ = v___y_1114_;
v___y_1033_ = v___y_1117_;
v___y_1034_ = v___y_1118_;
v___y_1035_ = v___y_1119_;
v_post_1036_ = v___x_1159_;
v___y_1037_ = v___y_1121_;
v_ref_1038_ = v_ref_1154_;
v___y_1039_ = v___y_1122_;
goto v___jp_1014_;
}
}
}
else
{
lean_object* v_ref_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v_ref_1160_ = lean_ctor_get(v___y_1121_, 5);
v___x_1161_ = l_Lean_SourceInfo_fromRef(v_ref_1160_, v___y_1102_);
v___x_1162_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__40));
v___x_1163_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__41));
lean_inc_n(v___x_1161_, 9);
v___x_1164_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1161_);
lean_ctor_set(v___x_1164_, 1, v___x_1162_);
v___x_1165_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__3));
v___x_1166_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__2));
v___x_1167_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__65));
v___x_1168_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__66));
v___x_1169_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1161_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
v___x_1170_ = l_Lean_Syntax_node1(v___x_1161_, v___x_1167_, v___x_1169_);
v___x_1171_ = l_Lean_Syntax_node1(v___x_1161_, v___x_1166_, v___x_1170_);
v___x_1172_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_expandDefContract___closed__53, &l_Lean_Elab_Tactic_Do_expandDefContract___closed__53_once, _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__53);
v___x_1173_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1161_);
lean_ctor_set(v___x_1173_, 1, v___x_1166_);
lean_ctor_set(v___x_1173_, 2, v___x_1172_);
v___x_1174_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__67));
v___x_1175_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1161_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
v___x_1176_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__69));
v___x_1177_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__70));
v___x_1178_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1161_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
v___x_1179_ = l_Lean_Syntax_node1(v___x_1161_, v___x_1176_, v___x_1178_);
v___x_1180_ = l_Lean_Syntax_node4(v___x_1161_, v___x_1165_, v___x_1171_, v___x_1173_, v___x_1175_, v___x_1179_);
v___x_1181_ = l_Lean_Syntax_node2(v___x_1161_, v___x_1163_, v___x_1164_, v___x_1180_);
v___y_1015_ = v___y_1099_;
v___y_1016_ = v___y_1100_;
v___y_1017_ = v_pre_1120_;
v___y_1018_ = v___y_1101_;
v___y_1019_ = v___y_1103_;
v___y_1020_ = v___y_1104_;
v___y_1021_ = v___y_1105_;
v___y_1022_ = v___y_1106_;
v___y_1023_ = v___y_1107_;
v___y_1024_ = v___y_1108_;
v___y_1025_ = v___y_1109_;
v___y_1026_ = v___y_1110_;
v___y_1027_ = v___y_1111_;
v___y_1028_ = v___y_1112_;
v___y_1029_ = v___y_1113_;
v___y_1030_ = v___y_1116_;
v___y_1031_ = v___y_1115_;
v___y_1032_ = v___y_1114_;
v___y_1033_ = v___y_1117_;
v___y_1034_ = v___y_1118_;
v___y_1035_ = v___y_1119_;
v_post_1036_ = v___x_1181_;
v___y_1037_ = v___y_1121_;
v_ref_1038_ = v_ref_1160_;
v___y_1039_ = v___y_1122_;
goto v___jp_1014_;
}
}
v___jp_1182_:
{
uint8_t v___x_1206_; 
v___x_1206_ = l_Lean_Syntax_isNone(v___y_1193_);
if (v___x_1206_ == 0)
{
lean_object* v___x_1207_; lean_object* v___x_1208_; uint8_t v___x_1209_; 
v___x_1207_ = l_Lean_Syntax_getArg(v___y_1193_, v___y_1194_);
v___x_1208_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__72));
lean_inc(v___x_1207_);
v___x_1209_ = l_Lean_Syntax_isOfKind(v___x_1207_, v___x_1208_);
if (v___x_1209_ == 0)
{
lean_object* v___x_1210_; 
lean_dec(v___x_1207_);
v___x_1210_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1199_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_a_1211_; lean_object* v_a_1212_; 
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_a_1211_);
v_a_1212_ = lean_ctor_get(v___x_1210_, 1);
lean_inc(v_a_1212_);
lean_dec_ref_known(v___x_1210_, 2);
v___y_1099_ = v___y_1183_;
v___y_1100_ = v___y_1184_;
v___y_1101_ = v___y_1185_;
v___y_1102_ = v___y_1186_;
v___y_1103_ = v___y_1188_;
v___y_1104_ = v___y_1189_;
v___y_1105_ = v___y_1190_;
v___y_1106_ = v___y_1191_;
v___y_1107_ = v___y_1192_;
v___y_1108_ = v___y_1193_;
v___y_1109_ = v___y_1194_;
v___y_1110_ = v___y_1195_;
v___y_1111_ = v___y_1196_;
v___y_1112_ = v___y_1197_;
v___y_1113_ = v___y_1198_;
v___y_1114_ = v___y_1205_;
v___y_1115_ = v___y_1201_;
v___y_1116_ = v___y_1200_;
v___y_1117_ = v___y_1202_;
v___y_1118_ = v___y_1203_;
v___y_1119_ = v___y_1204_;
v_pre_1120_ = v_a_1211_;
v___y_1121_ = v___y_1187_;
v___y_1122_ = v_a_1212_;
goto v___jp_1098_;
}
else
{
lean_object* v_a_1213_; lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec(v___y_1198_);
lean_dec(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec(v___y_1188_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1183_);
v_a_1213_ = lean_ctor_get(v___x_1210_, 0);
v_a_1214_ = lean_ctor_get(v___x_1210_, 1);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1216_ = v___x_1210_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_inc(v_a_1213_);
lean_dec(v___x_1210_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1213_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v_a_1214_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
else
{
lean_object* v___x_1222_; lean_object* v___x_1223_; uint8_t v___x_1224_; 
v___x_1222_ = l_Lean_Syntax_getArg(v___x_1207_, v___x_1097_);
lean_dec(v___x_1207_);
v___x_1223_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__3));
lean_inc(v___x_1222_);
v___x_1224_ = l_Lean_Syntax_isOfKind(v___x_1222_, v___x_1223_);
if (v___x_1224_ == 0)
{
v___y_1099_ = v___y_1183_;
v___y_1100_ = v___y_1184_;
v___y_1101_ = v___y_1185_;
v___y_1102_ = v___y_1186_;
v___y_1103_ = v___y_1188_;
v___y_1104_ = v___y_1189_;
v___y_1105_ = v___y_1190_;
v___y_1106_ = v___y_1191_;
v___y_1107_ = v___y_1192_;
v___y_1108_ = v___y_1193_;
v___y_1109_ = v___y_1194_;
v___y_1110_ = v___y_1195_;
v___y_1111_ = v___y_1196_;
v___y_1112_ = v___y_1197_;
v___y_1113_ = v___y_1198_;
v___y_1114_ = v___y_1205_;
v___y_1115_ = v___y_1201_;
v___y_1116_ = v___y_1200_;
v___y_1117_ = v___y_1202_;
v___y_1118_ = v___y_1203_;
v___y_1119_ = v___y_1204_;
v_pre_1120_ = v___x_1222_;
v___y_1121_ = v___y_1187_;
v___y_1122_ = v___y_1199_;
goto v___jp_1098_;
}
else
{
lean_object* v_ref_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v_ref_1225_ = lean_ctor_get(v___y_1187_, 5);
v___x_1226_ = l_Lean_SourceInfo_fromRef(v_ref_1225_, v___x_1206_);
v___x_1227_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__40));
v___x_1228_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__41));
lean_inc(v___x_1226_);
v___x_1229_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1226_);
lean_ctor_set(v___x_1229_, 1, v___x_1227_);
v___x_1230_ = l_Lean_Syntax_node2(v___x_1226_, v___x_1228_, v___x_1229_, v___x_1222_);
v___y_1099_ = v___y_1183_;
v___y_1100_ = v___y_1184_;
v___y_1101_ = v___y_1185_;
v___y_1102_ = v___y_1186_;
v___y_1103_ = v___y_1188_;
v___y_1104_ = v___y_1189_;
v___y_1105_ = v___y_1190_;
v___y_1106_ = v___y_1191_;
v___y_1107_ = v___y_1192_;
v___y_1108_ = v___y_1193_;
v___y_1109_ = v___y_1194_;
v___y_1110_ = v___y_1195_;
v___y_1111_ = v___y_1196_;
v___y_1112_ = v___y_1197_;
v___y_1113_ = v___y_1198_;
v___y_1114_ = v___y_1205_;
v___y_1115_ = v___y_1201_;
v___y_1116_ = v___y_1200_;
v___y_1117_ = v___y_1202_;
v___y_1118_ = v___y_1203_;
v___y_1119_ = v___y_1204_;
v_pre_1120_ = v___x_1230_;
v___y_1121_ = v___y_1187_;
v___y_1122_ = v___y_1199_;
goto v___jp_1098_;
}
}
}
else
{
lean_object* v_ref_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v_ref_1231_ = lean_ctor_get(v___y_1187_, 5);
v___x_1232_ = l_Lean_SourceInfo_fromRef(v_ref_1231_, v___y_1186_);
v___x_1233_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__69));
v___x_1234_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__70));
lean_inc(v___x_1232_);
v___x_1235_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1232_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
v___x_1236_ = l_Lean_Syntax_node1(v___x_1232_, v___x_1233_, v___x_1235_);
v___y_1099_ = v___y_1183_;
v___y_1100_ = v___y_1184_;
v___y_1101_ = v___y_1185_;
v___y_1102_ = v___y_1186_;
v___y_1103_ = v___y_1188_;
v___y_1104_ = v___y_1189_;
v___y_1105_ = v___y_1190_;
v___y_1106_ = v___y_1191_;
v___y_1107_ = v___y_1192_;
v___y_1108_ = v___y_1193_;
v___y_1109_ = v___y_1194_;
v___y_1110_ = v___y_1195_;
v___y_1111_ = v___y_1196_;
v___y_1112_ = v___y_1197_;
v___y_1113_ = v___y_1198_;
v___y_1114_ = v___y_1205_;
v___y_1115_ = v___y_1201_;
v___y_1116_ = v___y_1200_;
v___y_1117_ = v___y_1202_;
v___y_1118_ = v___y_1203_;
v___y_1119_ = v___y_1204_;
v_pre_1120_ = v___x_1236_;
v___y_1121_ = v___y_1187_;
v___y_1122_ = v___y_1199_;
goto v___jp_1098_;
}
}
v___jp_1237_:
{
lean_object* v___x_1260_; size_t v_sz_1261_; size_t v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; 
lean_inc_ref(v___y_1251_);
v___x_1260_ = l_Array_append___redArg(v___y_1251_, v___y_1259_);
lean_dec_ref(v___y_1259_);
v_sz_1261_ = lean_array_size(v___x_1260_);
v___x_1262_ = ((size_t)0ULL);
v___x_1263_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__0(v_sz_1261_, v___x_1262_, v___x_1260_);
v___x_1264_ = lean_mk_empty_array_with_capacity(v___y_1248_);
v___x_1265_ = lean_array_get_size(v___y_1251_);
v___x_1266_ = lean_nat_dec_lt(v___y_1248_, v___x_1265_);
if (v___x_1266_ == 0)
{
lean_dec_ref(v___y_1251_);
v___y_1183_ = v___x_1263_;
v___y_1184_ = v___y_1238_;
v___y_1185_ = v___y_1239_;
v___y_1186_ = v___y_1240_;
v___y_1187_ = v___y_1241_;
v___y_1188_ = v___y_1242_;
v___y_1189_ = v___y_1243_;
v___y_1190_ = v___y_1244_;
v___y_1191_ = v___y_1245_;
v___y_1192_ = v___y_1246_;
v___y_1193_ = v___y_1247_;
v___y_1194_ = v___y_1248_;
v___y_1195_ = v___y_1249_;
v___y_1196_ = v___y_1250_;
v___y_1197_ = v___y_1252_;
v___y_1198_ = v___y_1253_;
v___y_1199_ = v___y_1255_;
v___y_1200_ = v___y_1254_;
v___y_1201_ = v___x_1262_;
v___y_1202_ = v___y_1256_;
v___y_1203_ = v___y_1257_;
v___y_1204_ = v___y_1258_;
v___y_1205_ = v___x_1264_;
goto v___jp_1182_;
}
else
{
size_t v___x_1267_; lean_object* v___x_1268_; 
v___x_1267_ = lean_usize_of_nat(v___x_1265_);
v___x_1268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__3(v___y_1251_, v___x_1262_, v___x_1267_, v___x_1264_);
lean_dec_ref(v___y_1251_);
v___y_1183_ = v___x_1263_;
v___y_1184_ = v___y_1238_;
v___y_1185_ = v___y_1239_;
v___y_1186_ = v___y_1240_;
v___y_1187_ = v___y_1241_;
v___y_1188_ = v___y_1242_;
v___y_1189_ = v___y_1243_;
v___y_1190_ = v___y_1244_;
v___y_1191_ = v___y_1245_;
v___y_1192_ = v___y_1246_;
v___y_1193_ = v___y_1247_;
v___y_1194_ = v___y_1248_;
v___y_1195_ = v___y_1249_;
v___y_1196_ = v___y_1250_;
v___y_1197_ = v___y_1252_;
v___y_1198_ = v___y_1253_;
v___y_1199_ = v___y_1255_;
v___y_1200_ = v___y_1254_;
v___y_1201_ = v___x_1262_;
v___y_1202_ = v___y_1256_;
v___y_1203_ = v___y_1257_;
v___y_1204_ = v___y_1258_;
v___y_1205_ = v___x_1268_;
goto v___jp_1182_;
}
}
v___jp_1270_:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; uint8_t v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; uint8_t v___x_1296_; uint8_t v___x_1297_; 
v___x_1285_ = l_Lean_Syntax_getArg(v_decl_1269_, v___y_1272_);
v___x_1286_ = l_Lean_Syntax_getArg(v_decl_1269_, v___x_1097_);
lean_dec(v_decl_1269_);
v___x_1287_ = l_Lean_Syntax_getArg(v___x_1286_, v___y_1276_);
lean_dec(v___x_1286_);
v___x_1288_ = l_Lean_TSyntax_getId(v___x_1287_);
v___x_1289_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0___closed__0));
v___x_1290_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0___closed__1));
lean_inc(v___x_1288_);
v___x_1291_ = l_Lean_Name_append(v___x_1288_, v___x_1290_);
v___x_1292_ = 0;
v___x_1293_ = l_Lean_mkIdentFrom(v___x_1287_, v___x_1291_, v___x_1292_);
v___x_1294_ = l_Lean_Syntax_getArg(v___x_1285_, v___y_1276_);
lean_dec(v___x_1285_);
v___x_1295_ = l_Lean_Syntax_getArgs(v___x_1294_);
lean_dec(v___x_1294_);
v___x_1296_ = l_Lean_Syntax_isNone(v___y_1279_);
v___x_1297_ = 1;
if (v___x_1296_ == 0)
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1298_ = l_Lean_Syntax_getArg(v___y_1279_, v___y_1276_);
v___x_1299_ = l_Lean_Syntax_getArg(v___x_1298_, v___x_1097_);
lean_dec(v___x_1298_);
v___x_1300_ = l_Lean_Syntax_getArgs(v___x_1299_);
lean_dec(v___x_1299_);
v___y_1238_ = v___y_1274_;
v___y_1239_ = v___y_1278_;
v___y_1240_ = v___x_1292_;
v___y_1241_ = v___y_1283_;
v___y_1242_ = v___y_1281_;
v___y_1243_ = v___x_1289_;
v___y_1244_ = v___y_1271_;
v___y_1245_ = v___y_1272_;
v___y_1246_ = v___y_1273_;
v___y_1247_ = v___y_1275_;
v___y_1248_ = v___y_1276_;
v___y_1249_ = v___y_1277_;
v___y_1250_ = v___y_1279_;
v___y_1251_ = v___x_1295_;
v___y_1252_ = v___x_1287_;
v___y_1253_ = v___x_1288_;
v___y_1254_ = v___x_1297_;
v___y_1255_ = v___y_1284_;
v___y_1256_ = v___y_1280_;
v___y_1257_ = v___x_1293_;
v___y_1258_ = v___y_1282_;
v___y_1259_ = v___x_1300_;
goto v___jp_1237_;
}
else
{
lean_object* v___x_1301_; 
v___x_1301_ = lean_mk_empty_array_with_capacity(v___y_1276_);
v___y_1238_ = v___y_1274_;
v___y_1239_ = v___y_1278_;
v___y_1240_ = v___x_1292_;
v___y_1241_ = v___y_1283_;
v___y_1242_ = v___y_1281_;
v___y_1243_ = v___x_1289_;
v___y_1244_ = v___y_1271_;
v___y_1245_ = v___y_1272_;
v___y_1246_ = v___y_1273_;
v___y_1247_ = v___y_1275_;
v___y_1248_ = v___y_1276_;
v___y_1249_ = v___y_1277_;
v___y_1250_ = v___y_1279_;
v___y_1251_ = v___x_1295_;
v___y_1252_ = v___x_1287_;
v___y_1253_ = v___x_1288_;
v___y_1254_ = v___x_1297_;
v___y_1255_ = v___y_1284_;
v___y_1256_ = v___y_1280_;
v___y_1257_ = v___x_1293_;
v___y_1258_ = v___y_1282_;
v___y_1259_ = v___x_1301_;
goto v___jp_1237_;
}
}
v___jp_1302_:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__73));
v___x_1319_ = l_Lean_Macro_throwErrorAt___redArg(v___y_1317_, v___x_1318_, v___y_1313_, v___y_1305_);
lean_dec(v___y_1317_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v_a_1320_; 
v_a_1320_ = lean_ctor_get(v___x_1319_, 1);
lean_inc(v_a_1320_);
lean_dec_ref_known(v___x_1319_, 2);
v___y_1271_ = v___y_1307_;
v___y_1272_ = v___y_1308_;
v___y_1273_ = v___y_1309_;
v___y_1274_ = v___y_1303_;
v___y_1275_ = v___y_1310_;
v___y_1276_ = v___y_1311_;
v___y_1277_ = v___y_1312_;
v___y_1278_ = v___y_1304_;
v___y_1279_ = v___y_1314_;
v___y_1280_ = v___y_1315_;
v___y_1281_ = v___y_1306_;
v___y_1282_ = v___y_1316_;
v___y_1283_ = v___y_1313_;
v___y_1284_ = v_a_1320_;
goto v___jp_1270_;
}
else
{
lean_object* v_a_1321_; lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1329_; 
lean_dec(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec(v___y_1306_);
lean_dec(v___y_1304_);
lean_dec(v_decl_1269_);
v_a_1321_ = lean_ctor_get(v___x_1319_, 0);
v_a_1322_ = lean_ctor_get(v___x_1319_, 1);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1324_ = v___x_1319_;
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_inc(v_a_1321_);
lean_dec(v___x_1319_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; 
if (v_isShared_1325_ == 0)
{
v___x_1327_ = v___x_1324_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1321_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v_a_1322_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
}
v___jp_1330_:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1341_ = lean_unsigned_to_nat(4u);
v___x_1342_ = l_Lean_Syntax_getArg(v___y_1333_, v___x_1341_);
v___x_1343_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection(v___x_1342_, v___y_1339_, v___y_1340_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v_a_1344_; lean_object* v_a_1345_; lean_object* v_fst_1346_; lean_object* v_snd_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_a_1344_);
v_a_1345_ = lean_ctor_get(v___x_1343_, 1);
lean_inc(v_a_1345_);
lean_dec_ref_known(v___x_1343_, 2);
v_fst_1346_ = lean_ctor_get(v_a_1344_, 0);
lean_inc(v_fst_1346_);
v_snd_1347_ = lean_ctor_get(v_a_1344_, 1);
lean_inc(v_snd_1347_);
lean_dec(v_a_1344_);
v___x_1348_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__4));
v___x_1349_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__5));
v___x_1350_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__75));
v___x_1351_ = l_Lean_Macro_hasDecl(v___x_1350_, v___y_1339_, v_a_1345_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; lean_object* v_a_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; uint8_t v___x_1356_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_a_1352_);
v_a_1353_ = lean_ctor_get(v___x_1351_, 1);
lean_inc(v_a_1353_);
lean_dec_ref_known(v___x_1351_, 2);
lean_inc(v_decl_1269_);
v___x_1354_ = l_Lean_Syntax_setArg(v_decl_1269_, v___y_1332_, v_snd_1347_);
v___x_1355_ = l_Lean_Syntax_setArg(v_stx_628_, v___x_1097_, v___x_1354_);
v___x_1356_ = lean_unbox(v_a_1352_);
lean_dec(v_a_1352_);
if (v___x_1356_ == 0)
{
uint8_t v___x_1357_; 
v___x_1357_ = l_Lean_Syntax_isNone(v___y_1337_);
if (v___x_1357_ == 0)
{
lean_inc(v___y_1337_);
v___y_1303_ = v___y_1332_;
v___y_1304_ = v___y_1336_;
v___y_1305_ = v_a_1353_;
v___y_1306_ = v_fst_1346_;
v___y_1307_ = v___x_1349_;
v___y_1308_ = v___y_1331_;
v___y_1309_ = v___y_1333_;
v___y_1310_ = v___y_1335_;
v___y_1311_ = v___y_1334_;
v___y_1312_ = v___x_1348_;
v___y_1313_ = v___y_1339_;
v___y_1314_ = v___y_1337_;
v___y_1315_ = v___y_1338_;
v___y_1316_ = v___x_1355_;
v___y_1317_ = v___y_1337_;
goto v___jp_1302_;
}
else
{
uint8_t v___x_1358_; 
v___x_1358_ = l_Lean_Syntax_isNone(v___y_1335_);
if (v___x_1358_ == 0)
{
lean_inc(v___y_1335_);
v___y_1303_ = v___y_1332_;
v___y_1304_ = v___y_1336_;
v___y_1305_ = v_a_1353_;
v___y_1306_ = v_fst_1346_;
v___y_1307_ = v___x_1349_;
v___y_1308_ = v___y_1331_;
v___y_1309_ = v___y_1333_;
v___y_1310_ = v___y_1335_;
v___y_1311_ = v___y_1334_;
v___y_1312_ = v___x_1348_;
v___y_1313_ = v___y_1339_;
v___y_1314_ = v___y_1337_;
v___y_1315_ = v___y_1338_;
v___y_1316_ = v___x_1355_;
v___y_1317_ = v___y_1335_;
goto v___jp_1302_;
}
else
{
uint8_t v___x_1359_; 
v___x_1359_ = l_Lean_Syntax_isNone(v___y_1336_);
if (v___x_1359_ == 0)
{
lean_inc(v___y_1336_);
v___y_1303_ = v___y_1332_;
v___y_1304_ = v___y_1336_;
v___y_1305_ = v_a_1353_;
v___y_1306_ = v_fst_1346_;
v___y_1307_ = v___x_1349_;
v___y_1308_ = v___y_1331_;
v___y_1309_ = v___y_1333_;
v___y_1310_ = v___y_1335_;
v___y_1311_ = v___y_1334_;
v___y_1312_ = v___x_1348_;
v___y_1313_ = v___y_1339_;
v___y_1314_ = v___y_1337_;
v___y_1315_ = v___y_1338_;
v___y_1316_ = v___x_1355_;
v___y_1317_ = v___y_1336_;
goto v___jp_1302_;
}
else
{
lean_inc(v___y_1338_);
v___y_1303_ = v___y_1332_;
v___y_1304_ = v___y_1336_;
v___y_1305_ = v_a_1353_;
v___y_1306_ = v_fst_1346_;
v___y_1307_ = v___x_1349_;
v___y_1308_ = v___y_1331_;
v___y_1309_ = v___y_1333_;
v___y_1310_ = v___y_1335_;
v___y_1311_ = v___y_1334_;
v___y_1312_ = v___x_1348_;
v___y_1313_ = v___y_1339_;
v___y_1314_ = v___y_1337_;
v___y_1315_ = v___y_1338_;
v___y_1316_ = v___x_1355_;
v___y_1317_ = v___y_1338_;
goto v___jp_1302_;
}
}
}
}
else
{
v___y_1271_ = v___x_1349_;
v___y_1272_ = v___y_1331_;
v___y_1273_ = v___y_1333_;
v___y_1274_ = v___y_1332_;
v___y_1275_ = v___y_1335_;
v___y_1276_ = v___y_1334_;
v___y_1277_ = v___x_1348_;
v___y_1278_ = v___y_1336_;
v___y_1279_ = v___y_1337_;
v___y_1280_ = v___y_1338_;
v___y_1281_ = v_fst_1346_;
v___y_1282_ = v___x_1355_;
v___y_1283_ = v___y_1339_;
v___y_1284_ = v_a_1353_;
goto v___jp_1270_;
}
}
else
{
lean_object* v_a_1360_; lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
lean_dec(v_snd_1347_);
lean_dec(v_fst_1346_);
lean_dec(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec(v___y_1333_);
lean_dec(v_decl_1269_);
lean_dec(v_stx_628_);
v_a_1360_ = lean_ctor_get(v___x_1351_, 0);
v_a_1361_ = lean_ctor_get(v___x_1351_, 1);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1351_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_inc(v_a_1360_);
lean_dec(v___x_1351_);
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
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1360_);
lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_a_1361_);
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
else
{
lean_object* v_a_1369_; lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec(v___y_1333_);
lean_dec(v_decl_1269_);
lean_dec(v_stx_628_);
v_a_1369_ = lean_ctor_get(v___x_1343_, 0);
v_a_1370_ = lean_ctor_get(v___x_1343_, 1);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1343_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_inc(v_a_1369_);
lean_dec(v___x_1343_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1369_);
lean_ctor_set(v_reuseFailAlloc_1376_, 1, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
v___jp_1378_:
{
lean_object* v___x_1383_; lean_object* v_givenStx_1384_; lean_object* v_requiresStx_1385_; lean_object* v___x_1386_; lean_object* v_ensuresStx_1387_; lean_object* v_throwsStx_1388_; uint8_t v___x_1389_; 
v___x_1383_ = lean_unsigned_to_nat(0u);
v_givenStx_1384_ = l_Lean_Syntax_getArg(v___y_1380_, v___x_1383_);
v_requiresStx_1385_ = l_Lean_Syntax_getArg(v___y_1380_, v___x_1097_);
v___x_1386_ = lean_unsigned_to_nat(2u);
v_ensuresStx_1387_ = l_Lean_Syntax_getArg(v___y_1380_, v___x_1386_);
v_throwsStx_1388_ = l_Lean_Syntax_getArg(v___y_1380_, v___y_1379_);
v___x_1389_ = l_Lean_Syntax_isNone(v_givenStx_1384_);
if (v___x_1389_ == 0)
{
v___y_1331_ = v___x_1386_;
v___y_1332_ = v___y_1379_;
v___y_1333_ = v___y_1380_;
v___y_1334_ = v___x_1383_;
v___y_1335_ = v_requiresStx_1385_;
v___y_1336_ = v_ensuresStx_1387_;
v___y_1337_ = v_givenStx_1384_;
v___y_1338_ = v_throwsStx_1388_;
v___y_1339_ = v___y_1381_;
v___y_1340_ = v___y_1382_;
goto v___jp_1330_;
}
else
{
uint8_t v___x_1390_; 
v___x_1390_ = l_Lean_Syntax_isNone(v_requiresStx_1385_);
if (v___x_1390_ == 0)
{
v___y_1331_ = v___x_1386_;
v___y_1332_ = v___y_1379_;
v___y_1333_ = v___y_1380_;
v___y_1334_ = v___x_1383_;
v___y_1335_ = v_requiresStx_1385_;
v___y_1336_ = v_ensuresStx_1387_;
v___y_1337_ = v_givenStx_1384_;
v___y_1338_ = v_throwsStx_1388_;
v___y_1339_ = v___y_1381_;
v___y_1340_ = v___y_1382_;
goto v___jp_1330_;
}
else
{
uint8_t v___x_1391_; 
v___x_1391_ = l_Lean_Syntax_isNone(v_ensuresStx_1387_);
if (v___x_1391_ == 0)
{
v___y_1331_ = v___x_1386_;
v___y_1332_ = v___y_1379_;
v___y_1333_ = v___y_1380_;
v___y_1334_ = v___x_1383_;
v___y_1335_ = v_requiresStx_1385_;
v___y_1336_ = v_ensuresStx_1387_;
v___y_1337_ = v_givenStx_1384_;
v___y_1338_ = v_throwsStx_1388_;
v___y_1339_ = v___y_1381_;
v___y_1340_ = v___y_1382_;
goto v___jp_1330_;
}
else
{
lean_object* v___x_1392_; uint8_t v___x_1393_; 
v___x_1392_ = l_Lean_Syntax_getNumArgs(v_throwsStx_1388_);
v___x_1393_ = lean_nat_dec_eq(v___x_1392_, v___x_1383_);
lean_dec(v___x_1392_);
if (v___x_1393_ == 0)
{
v___y_1331_ = v___x_1386_;
v___y_1332_ = v___y_1379_;
v___y_1333_ = v___y_1380_;
v___y_1334_ = v___x_1383_;
v___y_1335_ = v_requiresStx_1385_;
v___y_1336_ = v_ensuresStx_1387_;
v___y_1337_ = v_givenStx_1384_;
v___y_1338_ = v_throwsStx_1388_;
v___y_1339_ = v___y_1381_;
v___y_1340_ = v___y_1382_;
goto v___jp_1330_;
}
else
{
lean_object* v___x_1394_; 
v___x_1394_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1382_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_a_1395_; 
v_a_1395_ = lean_ctor_get(v___x_1394_, 1);
lean_inc(v_a_1395_);
lean_dec_ref_known(v___x_1394_, 2);
v___y_1331_ = v___x_1386_;
v___y_1332_ = v___y_1379_;
v___y_1333_ = v___y_1380_;
v___y_1334_ = v___x_1383_;
v___y_1335_ = v_requiresStx_1385_;
v___y_1336_ = v_ensuresStx_1387_;
v___y_1337_ = v_givenStx_1384_;
v___y_1338_ = v_throwsStx_1388_;
v___y_1339_ = v___y_1381_;
v___y_1340_ = v_a_1395_;
goto v___jp_1330_;
}
else
{
lean_object* v_a_1396_; lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
lean_dec(v_throwsStx_1388_);
lean_dec(v_ensuresStx_1387_);
lean_dec(v_requiresStx_1385_);
lean_dec(v_givenStx_1384_);
lean_dec(v___y_1380_);
lean_dec(v_decl_1269_);
lean_dec(v_stx_628_);
v_a_1396_ = lean_ctor_get(v___x_1394_, 0);
v_a_1397_ = lean_ctor_get(v___x_1394_, 1);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1399_ = v___x_1394_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_inc(v_a_1396_);
lean_dec(v___x_1394_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1396_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v_a_1397_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
}
}
}
}
v___jp_1405_:
{
lean_object* v___x_1408_; lean_object* v_val_1409_; lean_object* v___x_1410_; uint8_t v___x_1411_; 
v___x_1408_ = lean_unsigned_to_nat(3u);
v_val_1409_ = l_Lean_Syntax_getArg(v_decl_1269_, v___x_1408_);
v___x_1410_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__1));
lean_inc(v_val_1409_);
v___x_1411_ = l_Lean_Syntax_isOfKind(v_val_1409_, v___x_1410_);
if (v___x_1411_ == 0)
{
lean_object* v___x_1412_; 
v___x_1412_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1407_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_a_1413_; 
v_a_1413_ = lean_ctor_get(v___x_1412_, 1);
lean_inc(v_a_1413_);
lean_dec_ref_known(v___x_1412_, 2);
v___y_1379_ = v___x_1408_;
v___y_1380_ = v_val_1409_;
v___y_1381_ = v___y_1406_;
v___y_1382_ = v_a_1413_;
goto v___jp_1378_;
}
else
{
lean_object* v_a_1414_; lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
lean_dec(v_val_1409_);
lean_dec(v_decl_1269_);
lean_dec(v_stx_628_);
v_a_1414_ = lean_ctor_get(v___x_1412_, 0);
v_a_1415_ = lean_ctor_get(v___x_1412_, 1);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1417_ = v___x_1412_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_inc(v_a_1414_);
lean_dec(v___x_1412_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
if (v_isShared_1418_ == 0)
{
v___x_1420_ = v___x_1417_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1414_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v_a_1415_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
else
{
v___y_1379_ = v___x_1408_;
v___y_1380_ = v_val_1409_;
v___y_1381_ = v___y_1406_;
v___y_1382_ = v___y_1407_;
goto v___jp_1378_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___boxed(lean_object* v_stx_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_Lean_Elab_Tactic_Do_expandDefContract(v_stx_1436_, v_a_1437_, v_a_1438_);
lean_dec_ref(v_a_1437_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1(){
_start:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1453_ = l_Lean_Elab_macroAttribute;
v___x_1454_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__0));
v___x_1455_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__2));
v___x_1456_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_expandDefContract___boxed), 3, 0);
v___x_1457_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1453_, v___x_1454_, v___x_1455_, v___x_1456_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___boxed(lean_object* v_a_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1();
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3(){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1462_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__2));
v___x_1463_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3___closed__0));
v___x_1464_ = l_Lean_addBuiltinDocString(v___x_1462_, v___x_1463_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3___boxed(lean_object* v_a_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3();
return v_res_1466_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1467_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1468_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0);
v___x_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg(){
_start:
{
lean_object* v___x_1471_; 
v___x_1471_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__1);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___boxed(lean_object* v___dummy_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg();
return v_res_1473_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1474_; 
v___x_1474_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg();
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0(lean_object* v_00_u03b2_1475_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___closed__0);
return v___x_1476_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0);
v___x_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1477_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___redArg(){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___redArg___closed__0);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___redArg___boxed(lean_object* v___dummy_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___redArg();
return v_res_1482_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1483_; 
v___x_1483_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___redArg();
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1(lean_object* v_00_u03b2_1484_){
_start:
{
lean_object* v___x_1485_; 
v___x_1485_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___closed__0);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__2___redArg(lean_object* v_as_1486_, size_t v_sz_1487_, size_t v_i_1488_, lean_object* v_b_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
uint8_t v___x_1495_; 
v___x_1495_ = lean_usize_dec_lt(v_i_1488_, v_sz_1487_);
if (v___x_1495_ == 0)
{
lean_object* v___x_1496_; 
v___x_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1496_, 0, v_b_1489_);
return v___x_1496_;
}
else
{
lean_object* v_a_1497_; uint8_t v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v_a_1497_ = lean_array_uget_borrowed(v_as_1486_, v_i_1488_);
v___x_1498_ = 0;
v___x_1499_ = lean_unsigned_to_nat(1000u);
lean_inc(v_a_1497_);
v___x_1500_ = l_Lean_Meta_SimpTheorems_addConst(v_b_1489_, v_a_1497_, v___x_1495_, v___x_1498_, v___x_1499_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1501_; size_t v___x_1502_; size_t v___x_1503_; 
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_a_1501_);
lean_dec_ref_known(v___x_1500_, 1);
v___x_1502_ = ((size_t)1ULL);
v___x_1503_ = lean_usize_add(v_i_1488_, v___x_1502_);
v_i_1488_ = v___x_1503_;
v_b_1489_ = v_a_1501_;
goto _start;
}
else
{
return v___x_1500_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__2___redArg___boxed(lean_object* v_as_1505_, lean_object* v_sz_1506_, lean_object* v_i_1507_, lean_object* v_b_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
size_t v_sz_boxed_1514_; size_t v_i_boxed_1515_; lean_object* v_res_1516_; 
v_sz_boxed_1514_ = lean_unbox_usize(v_sz_1506_);
lean_dec(v_sz_1506_);
v_i_boxed_1515_ = lean_unbox_usize(v_i_1507_);
lean_dec(v_i_1507_);
v_res_1516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__2___redArg(v_as_1505_, v_sz_boxed_1514_, v_i_boxed_1515_, v_b_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec_ref(v_as_1505_);
return v_res_1516_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__0(void){
_start:
{
lean_object* v___x_1517_; 
v___x_1517_ = l_Lean_Meta_DiscrTree_empty___redArg();
return v___x_1517_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__1(void){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = l_Lean_ImportedConsts_empty___redArg();
return v___x_1518_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3(void){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0);
v___x_1522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1521_);
return v___x_1522_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__4(void){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1523_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3);
v___x_1524_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__2));
v___x_1525_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__1, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__1);
v___x_1526_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
lean_ctor_set(v___x_1526_, 1, v___x_1524_);
lean_ctor_set(v___x_1526_, 2, v___x_1524_);
lean_ctor_set(v___x_1526_, 3, v___x_1523_);
return v___x_1526_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__5(void){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1527_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3);
v___x_1528_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___closed__0);
v___x_1529_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__4, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__4_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__4);
v___x_1530_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
lean_ctor_set(v___x_1530_, 1, v___x_1528_);
lean_ctor_set(v___x_1530_, 2, v___x_1527_);
return v___x_1530_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__6(void){
_start:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v_thms_1536_; 
v___x_1531_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3);
v___x_1532_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___closed__0);
v___x_1533_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___closed__0);
v___x_1534_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__5, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__5);
v___x_1535_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__0, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__0);
v_thms_1536_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_thms_1536_, 0, v___x_1535_);
lean_ctor_set(v_thms_1536_, 1, v___x_1535_);
lean_ctor_set(v_thms_1536_, 2, v___x_1534_);
lean_ctor_set(v_thms_1536_, 3, v___x_1533_);
lean_ctor_set(v_thms_1536_, 4, v___x_1532_);
lean_ctor_set(v_thms_1536_, 5, v___x_1531_);
return v_thms_1536_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__8(void){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1544_ = lean_unsigned_to_nat(0u);
v___x_1545_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3);
v___x_1546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1545_);
lean_ctor_set(v___x_1546_, 1, v___x_1544_);
return v___x_1546_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__9(void){
_start:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1547_ = lean_unsigned_to_nat(32u);
v___x_1548_ = lean_mk_empty_array_with_capacity(v___x_1547_);
v___x_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1548_);
return v___x_1549_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__10(void){
_start:
{
size_t v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1550_ = ((size_t)5ULL);
v___x_1551_ = lean_unsigned_to_nat(0u);
v___x_1552_ = lean_unsigned_to_nat(32u);
v___x_1553_ = lean_mk_empty_array_with_capacity(v___x_1552_);
v___x_1554_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__9, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__9);
v___x_1555_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1555_, 0, v___x_1554_);
lean_ctor_set(v___x_1555_, 1, v___x_1553_);
lean_ctor_set(v___x_1555_, 2, v___x_1551_);
lean_ctor_set(v___x_1555_, 3, v___x_1551_);
lean_ctor_set_usize(v___x_1555_, 4, v___x_1550_);
return v___x_1555_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__11(void){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1556_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__10, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__10_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__10);
v___x_1557_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3);
v___x_1558_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1557_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
lean_ctor_set(v___x_1558_, 2, v___x_1557_);
lean_ctor_set(v___x_1558_, 3, v___x_1556_);
return v___x_1558_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__12(void){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1559_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__11, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__11_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__11);
v___x_1560_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__8, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__8_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__8);
v___x_1561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1560_);
lean_ctor_set(v___x_1561_, 1, v___x_1559_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith(lean_object* v_names_1562_, lean_object* v_e_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_){
_start:
{
lean_object* v___x_1571_; lean_object* v_thms_1572_; size_t v_sz_1573_; size_t v___x_1574_; lean_object* v___x_1575_; 
v___x_1571_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__2));
v_thms_1572_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__6, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__6);
v_sz_1573_ = lean_array_size(v_names_1562_);
v___x_1574_ = ((size_t)0ULL);
v___x_1575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__2___redArg(v_names_1562_, v_sz_1573_, v___x_1574_, v_thms_1572_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; lean_object* v___x_1577_; 
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_a_1576_);
lean_dec_ref_known(v___x_1575_, 1);
v___x_1577_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_1569_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; uint8_t v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1578_);
lean_dec_ref_known(v___x_1577_, 1);
v___x_1579_ = 0;
v___x_1580_ = lean_box(0);
v___x_1581_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__7));
v___x_1582_ = lean_unsigned_to_nat(1u);
v___x_1583_ = lean_mk_empty_array_with_capacity(v___x_1582_);
v___x_1584_ = lean_array_push(v___x_1583_, v_a_1576_);
v___x_1585_ = l_Lean_Options_empty;
v___x_1586_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1581_, v___x_1584_, v_a_1578_, v___x_1585_, v_a_1566_, v_a_1568_, v_a_1569_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1587_);
lean_dec_ref_known(v___x_1586_, 1);
v___x_1588_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__12, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__12_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__12);
v___x_1589_ = l_Lean_Meta_simp(v_e_1563_, v_a_1587_, v___x_1571_, v___x_1580_, v___x_1588_, v___x_1579_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1599_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1592_ = v___x_1589_;
v_isShared_1593_ = v_isSharedCheck_1599_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1589_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1599_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v_fst_1594_; lean_object* v_expr_1595_; lean_object* v___x_1597_; 
v_fst_1594_ = lean_ctor_get(v_a_1590_, 0);
lean_inc(v_fst_1594_);
lean_dec(v_a_1590_);
v_expr_1595_ = lean_ctor_get(v_fst_1594_, 0);
lean_inc_ref(v_expr_1595_);
lean_dec(v_fst_1594_);
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 0, v_expr_1595_);
v___x_1597_ = v___x_1592_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_expr_1595_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
v_a_1600_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1589_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1589_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
else
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1615_; 
lean_dec_ref(v_e_1563_);
v_a_1608_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1610_ = v___x_1586_;
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1586_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1613_; 
if (v_isShared_1611_ == 0)
{
v___x_1613_ = v___x_1610_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_a_1608_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
else
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
lean_dec(v_a_1576_);
lean_dec_ref(v_e_1563_);
v_a_1616_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1618_ = v___x_1577_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1577_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1616_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
else
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
lean_dec_ref(v_e_1563_);
v_a_1624_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1626_ = v___x_1575_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1575_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1624_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___boxed(lean_object* v_names_1632_, lean_object* v_e_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith(v_names_1632_, v_e_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_);
lean_dec(v_a_1639_);
lean_dec_ref(v_a_1638_);
lean_dec(v_a_1637_);
lean_dec_ref(v_a_1636_);
lean_dec(v_a_1635_);
lean_dec_ref(v_a_1634_);
lean_dec_ref(v_names_1632_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__2(lean_object* v_as_1642_, size_t v_sz_1643_, size_t v_i_1644_, lean_object* v_b_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__2___redArg(v_as_1642_, v_sz_1643_, v_i_1644_, v_b_1645_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__2___boxed(lean_object* v_as_1654_, lean_object* v_sz_1655_, lean_object* v_i_1656_, lean_object* v_b_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
size_t v_sz_boxed_1665_; size_t v_i_boxed_1666_; lean_object* v_res_1667_; 
v_sz_boxed_1665_ = lean_unbox_usize(v_sz_1655_);
lean_dec(v_sz_1655_);
v_i_boxed_1666_ = lean_unbox_usize(v_i_1656_);
lean_dec(v_i_1656_);
v_res_1667_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__2(v_as_1654_, v_sz_boxed_1665_, v_i_boxed_1666_, v_b_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
lean_dec_ref(v_as_1654_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0___redArg(lean_object* v_e_1668_, lean_object* v___y_1669_){
_start:
{
uint8_t v___x_1671_; 
v___x_1671_ = l_Lean_Expr_hasMVar(v_e_1668_);
if (v___x_1671_ == 0)
{
lean_object* v___x_1672_; 
v___x_1672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1672_, 0, v_e_1668_);
return v___x_1672_;
}
else
{
lean_object* v___x_1673_; lean_object* v_mctx_1674_; lean_object* v___x_1675_; lean_object* v_fst_1676_; lean_object* v_snd_1677_; lean_object* v___x_1678_; lean_object* v_cache_1679_; lean_object* v_zetaDeltaFVarIds_1680_; lean_object* v_postponed_1681_; lean_object* v_diag_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1691_; 
v___x_1673_ = lean_st_ref_get(v___y_1669_);
v_mctx_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc_ref(v_mctx_1674_);
lean_dec(v___x_1673_);
v___x_1675_ = l_Lean_instantiateMVarsCore(v_mctx_1674_, v_e_1668_);
v_fst_1676_ = lean_ctor_get(v___x_1675_, 0);
lean_inc(v_fst_1676_);
v_snd_1677_ = lean_ctor_get(v___x_1675_, 1);
lean_inc(v_snd_1677_);
lean_dec_ref(v___x_1675_);
v___x_1678_ = lean_st_ref_take(v___y_1669_);
v_cache_1679_ = lean_ctor_get(v___x_1678_, 1);
v_zetaDeltaFVarIds_1680_ = lean_ctor_get(v___x_1678_, 2);
v_postponed_1681_ = lean_ctor_get(v___x_1678_, 3);
v_diag_1682_ = lean_ctor_get(v___x_1678_, 4);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1691_ == 0)
{
lean_object* v_unused_1692_; 
v_unused_1692_ = lean_ctor_get(v___x_1678_, 0);
lean_dec(v_unused_1692_);
v___x_1684_ = v___x_1678_;
v_isShared_1685_ = v_isSharedCheck_1691_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_diag_1682_);
lean_inc(v_postponed_1681_);
lean_inc(v_zetaDeltaFVarIds_1680_);
lean_inc(v_cache_1679_);
lean_dec(v___x_1678_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1691_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 0, v_snd_1677_);
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_snd_1677_);
lean_ctor_set(v_reuseFailAlloc_1690_, 1, v_cache_1679_);
lean_ctor_set(v_reuseFailAlloc_1690_, 2, v_zetaDeltaFVarIds_1680_);
lean_ctor_set(v_reuseFailAlloc_1690_, 3, v_postponed_1681_);
lean_ctor_set(v_reuseFailAlloc_1690_, 4, v_diag_1682_);
v___x_1687_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1688_ = lean_st_ref_put(v___y_1669_, v___x_1687_);
v___x_1689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1689_, 0, v_fst_1676_);
return v___x_1689_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0___redArg___boxed(lean_object* v_e_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0___redArg(v_e_1693_, v___y_1694_);
lean_dec(v___y_1694_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0(lean_object* v_e_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0___redArg(v_e_1697_, v___y_1701_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0___boxed(lean_object* v_e_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0(v_e_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__0(lean_object* v_e_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v___x_1728_; uint8_t v___x_1729_; 
v___x_1728_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__10));
v___x_1729_ = l_Lean_Expr_isAppOf(v_e_1717_, v___x_1728_);
if (v___x_1729_ == 0)
{
lean_dec_ref(v_e_1717_);
goto v___jp_1725_;
}
else
{
lean_object* v___x_1730_; 
v___x_1730_ = l_Lean_Meta_unfoldProjInst_x3f(v_e_1717_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1746_; 
v_a_1731_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1733_ = v___x_1730_;
v_isShared_1734_ = v_isSharedCheck_1746_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1730_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1746_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
if (lean_obj_tag(v_a_1731_) == 1)
{
lean_object* v_val_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1745_; 
v_val_1735_ = lean_ctor_get(v_a_1731_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v_a_1731_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1737_ = v_a_1731_;
v_isShared_1738_ = v_isSharedCheck_1745_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_val_1735_);
lean_dec(v_a_1731_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1745_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1740_; 
if (v_isShared_1738_ == 0)
{
v___x_1740_ = v___x_1737_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_val_1735_);
v___x_1740_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
lean_object* v___x_1742_; 
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 0, v___x_1740_);
v___x_1742_ = v___x_1733_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1740_);
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
lean_del_object(v___x_1733_);
lean_dec(v_a_1731_);
goto v___jp_1725_;
}
}
}
else
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
v_a_1747_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___x_1730_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1730_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1747_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
v___jp_1725_:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1726_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__0___closed__0));
v___x_1727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1726_);
return v___x_1727_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__0___boxed(lean_object* v_e_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__0(v_e_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__1(lean_object* v_x_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1772_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__0___closed__0));
v___x_1773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1772_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__1___boxed(lean_object* v_x_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__1(v_x_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec_ref(v_x_1774_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___lam__0(lean_object* v_00_u03b1_1783_, lean_object* v_x_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1792_ = lean_apply_1(v_x_1784_, lean_box(0));
v___x_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1792_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___lam__0___boxed(lean_object* v_00_u03b1_1794_, lean_object* v_x_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___lam__0(v_00_u03b1_1794_, v_x_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
return v_res_1803_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__3(void){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = l_Lean_maxRecDepthErrorMessage;
v___x_1810_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1809_);
return v___x_1810_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__4(void){
_start:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1811_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__3);
v___x_1812_ = l_Lean_MessageData_ofFormat(v___x_1811_);
return v___x_1812_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__5(void){
_start:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1813_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__4);
v___x_1814_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__2));
v___x_1815_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1814_);
lean_ctor_set(v___x_1815_, 1, v___x_1813_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg(lean_object* v_ref_1816_){
_start:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1818_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__5);
v___x_1819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1819_, 0, v_ref_1816_);
lean_ctor_set(v___x_1819_, 1, v___x_1818_);
v___x_1820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1819_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___boxed(lean_object* v_ref_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_1821_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10___redArg(lean_object* v_x_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v___y_1834_; lean_object* v_toCold_1843_; lean_object* v_currRecDepth_1844_; lean_object* v_ref_1845_; uint16_t v_optionFlags_1846_; uint8_t v_suppressElabErrors_1847_; uint8_t v_checkDeprecated_1848_; uint8_t v_isRecordingDeps_1849_; lean_object* v_maxRecDepth_1855_; lean_object* v___x_1856_; uint8_t v___x_1857_; 
v_toCold_1843_ = lean_ctor_get(v___y_1830_, 0);
v_currRecDepth_1844_ = lean_ctor_get(v___y_1830_, 1);
v_ref_1845_ = lean_ctor_get(v___y_1830_, 2);
v_optionFlags_1846_ = lean_ctor_get_uint16(v___y_1830_, sizeof(void*)*3);
v_suppressElabErrors_1847_ = lean_ctor_get_uint8(v___y_1830_, sizeof(void*)*3 + 2);
v_checkDeprecated_1848_ = lean_ctor_get_uint8(v___y_1830_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1849_ = lean_ctor_get_uint8(v___y_1830_, sizeof(void*)*3 + 4);
v_maxRecDepth_1855_ = lean_ctor_get(v_toCold_1843_, 3);
v___x_1856_ = lean_unsigned_to_nat(0u);
v___x_1857_ = lean_nat_dec_eq(v_maxRecDepth_1855_, v___x_1856_);
if (v___x_1857_ == 0)
{
uint8_t v___x_1858_; 
v___x_1858_ = lean_nat_dec_eq(v_currRecDepth_1844_, v_maxRecDepth_1855_);
if (v___x_1858_ == 0)
{
goto v___jp_1850_;
}
else
{
lean_object* v___x_1859_; 
lean_dec_ref(v_x_1824_);
lean_inc(v_ref_1845_);
v___x_1859_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_1845_);
v___y_1834_ = v___x_1859_;
goto v___jp_1833_;
}
}
else
{
goto v___jp_1850_;
}
v___jp_1833_:
{
if (lean_obj_tag(v___y_1834_) == 0)
{
return v___y_1834_;
}
else
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1842_; 
v_a_1835_ = lean_ctor_get(v___y_1834_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___y_1834_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1837_ = v___y_1834_;
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___y_1834_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1840_; 
if (v_isShared_1838_ == 0)
{
v___x_1840_ = v___x_1837_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_a_1835_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
}
v___jp_1850_:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1851_ = lean_unsigned_to_nat(1u);
v___x_1852_ = lean_nat_add(v_currRecDepth_1844_, v___x_1851_);
lean_inc(v_ref_1845_);
lean_inc_ref(v_toCold_1843_);
v___x_1853_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1853_, 0, v_toCold_1843_);
lean_ctor_set(v___x_1853_, 1, v___x_1852_);
lean_ctor_set(v___x_1853_, 2, v_ref_1845_);
lean_ctor_set_uint16(v___x_1853_, sizeof(void*)*3, v_optionFlags_1846_);
lean_ctor_set_uint8(v___x_1853_, sizeof(void*)*3 + 2, v_suppressElabErrors_1847_);
lean_ctor_set_uint8(v___x_1853_, sizeof(void*)*3 + 3, v_checkDeprecated_1848_);
lean_ctor_set_uint8(v___x_1853_, sizeof(void*)*3 + 4, v_isRecordingDeps_1849_);
lean_inc(v___y_1831_);
lean_inc(v___y_1829_);
lean_inc_ref(v___y_1828_);
lean_inc(v___y_1827_);
lean_inc_ref(v___y_1826_);
lean_inc(v___y_1825_);
v___x_1854_ = lean_apply_8(v_x_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___x_1853_, v___y_1831_, lean_box(0));
v___y_1834_ = v___x_1854_;
goto v___jp_1833_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10___redArg___boxed(lean_object* v_x_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10___redArg(v_x_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__2(lean_object* v___x_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1870_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__2___boxed(lean_object* v___x_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__2(v___x_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
lean_dec(v___y_1885_);
lean_dec_ref(v___y_1884_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(lean_object* v_k_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v_b_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v___x_1898_; 
lean_inc(v___y_1896_);
lean_inc_ref(v___y_1895_);
lean_inc(v___y_1894_);
lean_inc_ref(v___y_1893_);
lean_inc(v___y_1891_);
lean_inc_ref(v___y_1890_);
lean_inc(v___y_1889_);
v___x_1898_ = lean_apply_9(v_k_1888_, v_b_1892_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, lean_box(0));
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed(lean_object* v_k_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v_b_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(v_k_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v_b_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v___y_1900_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg(lean_object* v_name_1910_, uint8_t v_bi_1911_, lean_object* v_type_1912_, lean_object* v_k_1913_, uint8_t v_kind_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v___f_1923_; lean_object* v___x_1924_; 
lean_inc(v___y_1917_);
lean_inc_ref(v___y_1916_);
lean_inc(v___y_1915_);
v___f_1923_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1923_, 0, v_k_1913_);
lean_closure_set(v___f_1923_, 1, v___y_1915_);
lean_closure_set(v___f_1923_, 2, v___y_1916_);
lean_closure_set(v___f_1923_, 3, v___y_1917_);
v___x_1924_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1910_, v_bi_1911_, v_type_1912_, v___f_1923_, v_kind_1914_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
if (lean_obj_tag(v___x_1924_) == 0)
{
return v___x_1924_;
}
else
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1932_; 
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1927_ = v___x_1924_;
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1924_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1930_; 
if (v_isShared_1928_ == 0)
{
v___x_1930_ = v___x_1927_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_a_1925_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg___boxed(lean_object* v_name_1933_, lean_object* v_bi_1934_, lean_object* v_type_1935_, lean_object* v_k_1936_, lean_object* v_kind_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_){
_start:
{
uint8_t v_bi_boxed_1946_; uint8_t v_kind_boxed_1947_; lean_object* v_res_1948_; 
v_bi_boxed_1946_ = lean_unbox(v_bi_1934_);
v_kind_boxed_1947_ = lean_unbox(v_kind_1937_);
v_res_1948_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg(v_name_1933_, v_bi_boxed_1946_, v_type_1935_, v_k_1936_, v_kind_boxed_1947_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
lean_dec(v___y_1938_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11___redArg(lean_object* v_name_1949_, lean_object* v_type_1950_, lean_object* v_val_1951_, lean_object* v_k_1952_, uint8_t v_nondep_1953_, uint8_t v_kind_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v___f_1963_; lean_object* v___x_1964_; 
lean_inc(v___y_1957_);
lean_inc_ref(v___y_1956_);
lean_inc(v___y_1955_);
v___f_1963_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1963_, 0, v_k_1952_);
lean_closure_set(v___f_1963_, 1, v___y_1955_);
lean_closure_set(v___f_1963_, 2, v___y_1956_);
lean_closure_set(v___f_1963_, 3, v___y_1957_);
v___x_1964_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1949_, v_type_1950_, v_val_1951_, v___f_1963_, v_nondep_1953_, v_kind_1954_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
if (lean_obj_tag(v___x_1964_) == 0)
{
return v___x_1964_;
}
else
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1972_; 
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1967_ = v___x_1964_;
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1964_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1970_; 
if (v_isShared_1968_ == 0)
{
v___x_1970_ = v___x_1967_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_a_1965_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11___redArg___boxed(lean_object* v_name_1973_, lean_object* v_type_1974_, lean_object* v_val_1975_, lean_object* v_k_1976_, lean_object* v_nondep_1977_, lean_object* v_kind_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
uint8_t v_nondep_boxed_1987_; uint8_t v_kind_boxed_1988_; lean_object* v_res_1989_; 
v_nondep_boxed_1987_ = lean_unbox(v_nondep_1977_);
v_kind_boxed_1988_ = lean_unbox(v_kind_1978_);
v_res_1989_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11___redArg(v_name_1973_, v_type_1974_, v_val_1975_, v_k_1976_, v_nondep_boxed_1987_, v_kind_boxed_1988_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec(v___y_1979_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5_spec__6___redArg(lean_object* v_a_1990_, lean_object* v_x_1991_){
_start:
{
if (lean_obj_tag(v_x_1991_) == 0)
{
lean_object* v___x_1992_; 
v___x_1992_ = lean_box(0);
return v___x_1992_;
}
else
{
lean_object* v_key_1993_; lean_object* v_value_1994_; lean_object* v_tail_1995_; uint8_t v___x_1996_; 
v_key_1993_ = lean_ctor_get(v_x_1991_, 0);
v_value_1994_ = lean_ctor_get(v_x_1991_, 1);
v_tail_1995_ = lean_ctor_get(v_x_1991_, 2);
v___x_1996_ = l_Lean_ExprStructEq_beq(v_key_1993_, v_a_1990_);
if (v___x_1996_ == 0)
{
v_x_1991_ = v_tail_1995_;
goto _start;
}
else
{
lean_object* v___x_1998_; 
lean_inc(v_value_1994_);
v___x_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1998_, 0, v_value_1994_);
return v___x_1998_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object* v_a_1999_, lean_object* v_x_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5_spec__6___redArg(v_a_1999_, v_x_2000_);
lean_dec(v_x_2000_);
lean_dec_ref(v_a_1999_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5___redArg(lean_object* v_m_2002_, lean_object* v_a_2003_){
_start:
{
lean_object* v_buckets_2004_; lean_object* v___x_2005_; uint64_t v___x_2006_; uint64_t v___x_2007_; uint64_t v___x_2008_; uint64_t v_fold_2009_; uint64_t v___x_2010_; uint64_t v___x_2011_; uint64_t v___x_2012_; size_t v___x_2013_; size_t v___x_2014_; size_t v___x_2015_; size_t v___x_2016_; size_t v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v_buckets_2004_ = lean_ctor_get(v_m_2002_, 1);
v___x_2005_ = lean_array_get_size(v_buckets_2004_);
v___x_2006_ = l_Lean_ExprStructEq_hash(v_a_2003_);
v___x_2007_ = 32ULL;
v___x_2008_ = lean_uint64_shift_right(v___x_2006_, v___x_2007_);
v_fold_2009_ = lean_uint64_xor(v___x_2006_, v___x_2008_);
v___x_2010_ = 16ULL;
v___x_2011_ = lean_uint64_shift_right(v_fold_2009_, v___x_2010_);
v___x_2012_ = lean_uint64_xor(v_fold_2009_, v___x_2011_);
v___x_2013_ = lean_uint64_to_usize(v___x_2012_);
v___x_2014_ = lean_usize_of_nat(v___x_2005_);
v___x_2015_ = ((size_t)1ULL);
v___x_2016_ = lean_usize_sub(v___x_2014_, v___x_2015_);
v___x_2017_ = lean_usize_land(v___x_2013_, v___x_2016_);
v___x_2018_ = lean_array_uget_borrowed(v_buckets_2004_, v___x_2017_);
v___x_2019_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5_spec__6___redArg(v_a_2003_, v___x_2018_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5___redArg___boxed(lean_object* v_m_2020_, lean_object* v_a_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5___redArg(v_m_2020_, v_a_2021_);
lean_dec_ref(v_a_2021_);
lean_dec_ref(v_m_2020_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_2023_, lean_object* v_x_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2032_ = lean_apply_1(v_x_2024_, lean_box(0));
v___x_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2032_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2034_, lean_object* v_x_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__0(v_00_u03b1_2034_, v_x_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__18___redArg(lean_object* v_a_2044_, lean_object* v_b_2045_, lean_object* v_x_2046_){
_start:
{
if (lean_obj_tag(v_x_2046_) == 0)
{
lean_dec(v_b_2045_);
lean_dec_ref(v_a_2044_);
return v_x_2046_;
}
else
{
lean_object* v_key_2047_; lean_object* v_value_2048_; lean_object* v_tail_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2061_; 
v_key_2047_ = lean_ctor_get(v_x_2046_, 0);
v_value_2048_ = lean_ctor_get(v_x_2046_, 1);
v_tail_2049_ = lean_ctor_get(v_x_2046_, 2);
v_isSharedCheck_2061_ = !lean_is_exclusive(v_x_2046_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2051_ = v_x_2046_;
v_isShared_2052_ = v_isSharedCheck_2061_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_tail_2049_);
lean_inc(v_value_2048_);
lean_inc(v_key_2047_);
lean_dec(v_x_2046_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2061_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
uint8_t v___x_2053_; 
v___x_2053_ = l_Lean_ExprStructEq_beq(v_key_2047_, v_a_2044_);
if (v___x_2053_ == 0)
{
lean_object* v___x_2054_; lean_object* v___x_2056_; 
v___x_2054_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__18___redArg(v_a_2044_, v_b_2045_, v_tail_2049_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 2, v___x_2054_);
v___x_2056_ = v___x_2051_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_key_2047_);
lean_ctor_set(v_reuseFailAlloc_2057_, 1, v_value_2048_);
lean_ctor_set(v_reuseFailAlloc_2057_, 2, v___x_2054_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
else
{
lean_object* v___x_2059_; 
lean_dec(v_value_2048_);
lean_dec(v_key_2047_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 1, v_b_2045_);
lean_ctor_set(v___x_2051_, 0, v_a_2044_);
v___x_2059_ = v___x_2051_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_a_2044_);
lean_ctor_set(v_reuseFailAlloc_2060_, 1, v_b_2045_);
lean_ctor_set(v_reuseFailAlloc_2060_, 2, v_tail_2049_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16___redArg(lean_object* v_a_2062_, lean_object* v_x_2063_){
_start:
{
if (lean_obj_tag(v_x_2063_) == 0)
{
uint8_t v___x_2064_; 
v___x_2064_ = 0;
return v___x_2064_;
}
else
{
lean_object* v_key_2065_; lean_object* v_tail_2066_; uint8_t v___x_2067_; 
v_key_2065_ = lean_ctor_get(v_x_2063_, 0);
v_tail_2066_ = lean_ctor_get(v_x_2063_, 2);
v___x_2067_ = l_Lean_ExprStructEq_beq(v_key_2065_, v_a_2062_);
if (v___x_2067_ == 0)
{
v_x_2063_ = v_tail_2066_;
goto _start;
}
else
{
return v___x_2067_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16___redArg___boxed(lean_object* v_a_2069_, lean_object* v_x_2070_){
_start:
{
uint8_t v_res_2071_; lean_object* v_r_2072_; 
v_res_2071_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2069_, v_x_2070_);
lean_dec(v_x_2070_);
lean_dec_ref(v_a_2069_);
v_r_2072_ = lean_box(v_res_2071_);
return v_r_2072_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(lean_object* v_x_2073_, lean_object* v_x_2074_){
_start:
{
if (lean_obj_tag(v_x_2074_) == 0)
{
return v_x_2073_;
}
else
{
lean_object* v_key_2075_; lean_object* v_value_2076_; lean_object* v_tail_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2100_; 
v_key_2075_ = lean_ctor_get(v_x_2074_, 0);
v_value_2076_ = lean_ctor_get(v_x_2074_, 1);
v_tail_2077_ = lean_ctor_get(v_x_2074_, 2);
v_isSharedCheck_2100_ = !lean_is_exclusive(v_x_2074_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2079_ = v_x_2074_;
v_isShared_2080_ = v_isSharedCheck_2100_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_tail_2077_);
lean_inc(v_value_2076_);
lean_inc(v_key_2075_);
lean_dec(v_x_2074_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2100_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2081_; uint64_t v___x_2082_; uint64_t v___x_2083_; uint64_t v___x_2084_; uint64_t v_fold_2085_; uint64_t v___x_2086_; uint64_t v___x_2087_; uint64_t v___x_2088_; size_t v___x_2089_; size_t v___x_2090_; size_t v___x_2091_; size_t v___x_2092_; size_t v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2096_; 
v___x_2081_ = lean_array_get_size(v_x_2073_);
v___x_2082_ = l_Lean_ExprStructEq_hash(v_key_2075_);
v___x_2083_ = 32ULL;
v___x_2084_ = lean_uint64_shift_right(v___x_2082_, v___x_2083_);
v_fold_2085_ = lean_uint64_xor(v___x_2082_, v___x_2084_);
v___x_2086_ = 16ULL;
v___x_2087_ = lean_uint64_shift_right(v_fold_2085_, v___x_2086_);
v___x_2088_ = lean_uint64_xor(v_fold_2085_, v___x_2087_);
v___x_2089_ = lean_uint64_to_usize(v___x_2088_);
v___x_2090_ = lean_usize_of_nat(v___x_2081_);
v___x_2091_ = ((size_t)1ULL);
v___x_2092_ = lean_usize_sub(v___x_2090_, v___x_2091_);
v___x_2093_ = lean_usize_land(v___x_2089_, v___x_2092_);
v___x_2094_ = lean_array_uget_borrowed(v_x_2073_, v___x_2093_);
lean_inc(v___x_2094_);
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 2, v___x_2094_);
v___x_2096_ = v___x_2079_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_key_2075_);
lean_ctor_set(v_reuseFailAlloc_2099_, 1, v_value_2076_);
lean_ctor_set(v_reuseFailAlloc_2099_, 2, v___x_2094_);
v___x_2096_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
lean_object* v___x_2097_; 
v___x_2097_ = lean_array_uset(v_x_2073_, v___x_2093_, v___x_2096_);
v_x_2073_ = v___x_2097_;
v_x_2074_ = v_tail_2077_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(lean_object* v_i_2101_, lean_object* v_source_2102_, lean_object* v_target_2103_){
_start:
{
lean_object* v___x_2104_; uint8_t v___x_2105_; 
v___x_2104_ = lean_array_get_size(v_source_2102_);
v___x_2105_ = lean_nat_dec_lt(v_i_2101_, v___x_2104_);
if (v___x_2105_ == 0)
{
lean_dec_ref(v_source_2102_);
lean_dec(v_i_2101_);
return v_target_2103_;
}
else
{
lean_object* v_es_2106_; lean_object* v___x_2107_; lean_object* v_source_2108_; lean_object* v_target_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v_es_2106_ = lean_array_fget(v_source_2102_, v_i_2101_);
v___x_2107_ = lean_box(0);
v_source_2108_ = lean_array_fset(v_source_2102_, v_i_2101_, v___x_2107_);
v_target_2109_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_target_2103_, v_es_2106_);
v___x_2110_ = lean_unsigned_to_nat(1u);
v___x_2111_ = lean_nat_add(v_i_2101_, v___x_2110_);
lean_dec(v_i_2101_);
v_i_2101_ = v___x_2111_;
v_source_2102_ = v_source_2108_;
v_target_2103_ = v_target_2109_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17___redArg(lean_object* v_data_2113_){
_start:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v_nbuckets_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2114_ = lean_array_get_size(v_data_2113_);
v___x_2115_ = lean_unsigned_to_nat(2u);
v_nbuckets_2116_ = lean_nat_mul(v___x_2114_, v___x_2115_);
v___x_2117_ = lean_unsigned_to_nat(0u);
v___x_2118_ = lean_box(0);
v___x_2119_ = lean_mk_array(v_nbuckets_2116_, v___x_2118_);
v___x_2120_ = lean_array_propagate_mark(v_data_2113_, v___x_2119_);
v___x_2121_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v___x_2117_, v_data_2113_, v___x_2120_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11___redArg(lean_object* v_m_2122_, lean_object* v_a_2123_, lean_object* v_b_2124_){
_start:
{
lean_object* v_size_2125_; lean_object* v_buckets_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2169_; 
v_size_2125_ = lean_ctor_get(v_m_2122_, 0);
v_buckets_2126_ = lean_ctor_get(v_m_2122_, 1);
v_isSharedCheck_2169_ = !lean_is_exclusive(v_m_2122_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2128_ = v_m_2122_;
v_isShared_2129_ = v_isSharedCheck_2169_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_buckets_2126_);
lean_inc(v_size_2125_);
lean_dec(v_m_2122_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2169_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2130_; uint64_t v___x_2131_; uint64_t v___x_2132_; uint64_t v___x_2133_; uint64_t v_fold_2134_; uint64_t v___x_2135_; uint64_t v___x_2136_; uint64_t v___x_2137_; size_t v___x_2138_; size_t v___x_2139_; size_t v___x_2140_; size_t v___x_2141_; size_t v___x_2142_; lean_object* v_bkt_2143_; uint8_t v___x_2144_; 
v___x_2130_ = lean_array_get_size(v_buckets_2126_);
v___x_2131_ = l_Lean_ExprStructEq_hash(v_a_2123_);
v___x_2132_ = 32ULL;
v___x_2133_ = lean_uint64_shift_right(v___x_2131_, v___x_2132_);
v_fold_2134_ = lean_uint64_xor(v___x_2131_, v___x_2133_);
v___x_2135_ = 16ULL;
v___x_2136_ = lean_uint64_shift_right(v_fold_2134_, v___x_2135_);
v___x_2137_ = lean_uint64_xor(v_fold_2134_, v___x_2136_);
v___x_2138_ = lean_uint64_to_usize(v___x_2137_);
v___x_2139_ = lean_usize_of_nat(v___x_2130_);
v___x_2140_ = ((size_t)1ULL);
v___x_2141_ = lean_usize_sub(v___x_2139_, v___x_2140_);
v___x_2142_ = lean_usize_land(v___x_2138_, v___x_2141_);
v_bkt_2143_ = lean_array_uget_borrowed(v_buckets_2126_, v___x_2142_);
v___x_2144_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2123_, v_bkt_2143_);
if (v___x_2144_ == 0)
{
lean_object* v___x_2145_; lean_object* v_size_x27_2146_; lean_object* v___x_2147_; lean_object* v_buckets_x27_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; uint8_t v___x_2154_; 
v___x_2145_ = lean_unsigned_to_nat(1u);
v_size_x27_2146_ = lean_nat_add(v_size_2125_, v___x_2145_);
lean_dec(v_size_2125_);
lean_inc(v_bkt_2143_);
v___x_2147_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2147_, 0, v_a_2123_);
lean_ctor_set(v___x_2147_, 1, v_b_2124_);
lean_ctor_set(v___x_2147_, 2, v_bkt_2143_);
v_buckets_x27_2148_ = lean_array_uset(v_buckets_2126_, v___x_2142_, v___x_2147_);
v___x_2149_ = lean_unsigned_to_nat(4u);
v___x_2150_ = lean_nat_mul(v_size_x27_2146_, v___x_2149_);
v___x_2151_ = lean_unsigned_to_nat(3u);
v___x_2152_ = lean_nat_div(v___x_2150_, v___x_2151_);
lean_dec(v___x_2150_);
v___x_2153_ = lean_array_get_size(v_buckets_x27_2148_);
v___x_2154_ = lean_nat_dec_le(v___x_2152_, v___x_2153_);
lean_dec(v___x_2152_);
if (v___x_2154_ == 0)
{
lean_object* v_val_2155_; lean_object* v___x_2157_; 
v_val_2155_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17___redArg(v_buckets_x27_2148_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 1, v_val_2155_);
lean_ctor_set(v___x_2128_, 0, v_size_x27_2146_);
v___x_2157_ = v___x_2128_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_size_x27_2146_);
lean_ctor_set(v_reuseFailAlloc_2158_, 1, v_val_2155_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
else
{
lean_object* v___x_2160_; 
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 1, v_buckets_x27_2148_);
lean_ctor_set(v___x_2128_, 0, v_size_x27_2146_);
v___x_2160_ = v___x_2128_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_size_x27_2146_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v_buckets_x27_2148_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
else
{
lean_object* v___x_2162_; lean_object* v_buckets_x27_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2167_; 
lean_inc(v_bkt_2143_);
v___x_2162_ = lean_box(0);
v_buckets_x27_2163_ = lean_array_uset(v_buckets_2126_, v___x_2142_, v___x_2162_);
v___x_2164_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__18___redArg(v_a_2123_, v_b_2124_, v_bkt_2143_);
v___x_2165_ = lean_array_uset(v_buckets_x27_2163_, v___x_2142_, v___x_2164_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 1, v___x_2165_);
v___x_2167_ = v___x_2128_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_size_2125_);
lean_ctor_set(v_reuseFailAlloc_2168_, 1, v___x_2165_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__2(lean_object* v_a_2170_, lean_object* v_e_2171_, lean_object* v_a_2172_){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2174_ = lean_st_ref_take(v_a_2170_);
v___x_2175_ = lean_box(0);
v___x_2176_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11___redArg(v___x_2174_, v_e_2171_, v_a_2172_);
v___x_2177_ = lean_st_ref_put(v_a_2170_, v___x_2176_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__2___boxed(lean_object* v_a_2178_, lean_object* v_e_2179_, lean_object* v_a_2180_, lean_object* v___y_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__2(v_a_2178_, v_e_2179_, v_a_2180_);
lean_dec(v_a_2178_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6___lam__0___boxed(lean_object* v_fvars_2183_, lean_object* v_pre_2184_, lean_object* v_post_2185_, lean_object* v_usedLetOnly_2186_, lean_object* v_skipConstInApp_2187_, lean_object* v_skipInstances_2188_, lean_object* v_body_2189_, lean_object* v_x_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
uint8_t v_usedLetOnly_boxed_2199_; uint8_t v_skipConstInApp_boxed_2200_; uint8_t v_skipInstances_boxed_2201_; lean_object* v_res_2202_; 
v_usedLetOnly_boxed_2199_ = lean_unbox(v_usedLetOnly_2186_);
v_skipConstInApp_boxed_2200_ = lean_unbox(v_skipConstInApp_2187_);
v_skipInstances_boxed_2201_ = lean_unbox(v_skipInstances_2188_);
v_res_2202_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6___lam__0(v_fvars_2183_, v_pre_2184_, v_post_2185_, v_usedLetOnly_boxed_2199_, v_skipConstInApp_boxed_2200_, v_skipInstances_boxed_2201_, v_body_2189_, v_x_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec(v___y_2191_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7___lam__0(lean_object* v_fvars_2206_, lean_object* v_pre_2207_, lean_object* v_post_2208_, uint8_t v_usedLetOnly_2209_, uint8_t v_skipConstInApp_2210_, uint8_t v_skipInstances_2211_, lean_object* v_body_2212_, lean_object* v_x_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2222_ = lean_array_push(v_fvars_2206_, v_x_2213_);
v___x_2223_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7(v_pre_2207_, v_post_2208_, v_usedLetOnly_2209_, v_skipConstInApp_2210_, v_skipInstances_2211_, v___x_2222_, v_body_2212_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7___lam__0___boxed(lean_object* v_fvars_2224_, lean_object* v_pre_2225_, lean_object* v_post_2226_, lean_object* v_usedLetOnly_2227_, lean_object* v_skipConstInApp_2228_, lean_object* v_skipInstances_2229_, lean_object* v_body_2230_, lean_object* v_x_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
uint8_t v_usedLetOnly_boxed_2240_; uint8_t v_skipConstInApp_boxed_2241_; uint8_t v_skipInstances_boxed_2242_; lean_object* v_res_2243_; 
v_usedLetOnly_boxed_2240_ = lean_unbox(v_usedLetOnly_2227_);
v_skipConstInApp_boxed_2241_ = lean_unbox(v_skipConstInApp_2228_);
v_skipInstances_boxed_2242_ = lean_unbox(v_skipInstances_2229_);
v_res_2243_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7___lam__0(v_fvars_2224_, v_pre_2225_, v_post_2226_, v_usedLetOnly_boxed_2240_, v_skipConstInApp_boxed_2241_, v_skipInstances_boxed_2242_, v_body_2230_, v_x_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v___y_2232_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(lean_object* v_pre_2244_, lean_object* v_post_2245_, uint8_t v_usedLetOnly_2246_, uint8_t v_skipConstInApp_2247_, uint8_t v_skipInstances_2248_, lean_object* v_e_2249_, lean_object* v_a_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
lean_object* v___x_2258_; 
lean_inc_ref(v_post_2245_);
lean_inc(v___y_2256_);
lean_inc_ref(v___y_2255_);
lean_inc(v___y_2254_);
lean_inc_ref(v___y_2253_);
lean_inc(v___y_2252_);
lean_inc_ref(v___y_2251_);
lean_inc_ref(v_e_2249_);
v___x_2258_ = lean_apply_8(v_post_2245_, v_e_2249_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, lean_box(0));
if (lean_obj_tag(v___x_2258_) == 0)
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2277_; 
v_a_2259_ = lean_ctor_get(v___x_2258_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2261_ = v___x_2258_;
v_isShared_2262_ = v_isSharedCheck_2277_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2258_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2277_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
switch(lean_obj_tag(v_a_2259_))
{
case 0:
{
lean_object* v_e_2263_; lean_object* v___x_2265_; 
lean_dec_ref(v_e_2249_);
lean_dec_ref(v_post_2245_);
lean_dec_ref(v_pre_2244_);
v_e_2263_ = lean_ctor_get(v_a_2259_, 0);
lean_inc_ref(v_e_2263_);
lean_dec_ref_known(v_a_2259_, 1);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 0, v_e_2263_);
v___x_2265_ = v___x_2261_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_e_2263_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
case 1:
{
lean_object* v_e_2267_; lean_object* v___x_2268_; 
lean_del_object(v___x_2261_);
lean_dec_ref(v_e_2249_);
v_e_2267_ = lean_ctor_get(v_a_2259_, 0);
lean_inc_ref(v_e_2267_);
lean_dec_ref_known(v_a_2259_, 1);
v___x_2268_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2244_, v_post_2245_, v_usedLetOnly_2246_, v_skipConstInApp_2247_, v_skipInstances_2248_, v_e_2267_, v_a_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
return v___x_2268_;
}
default: 
{
lean_object* v_e_x3f_2269_; 
lean_dec_ref(v_post_2245_);
lean_dec_ref(v_pre_2244_);
v_e_x3f_2269_ = lean_ctor_get(v_a_2259_, 0);
lean_inc(v_e_x3f_2269_);
lean_dec_ref_known(v_a_2259_, 1);
if (lean_obj_tag(v_e_x3f_2269_) == 0)
{
lean_object* v___x_2271_; 
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 0, v_e_2249_);
v___x_2271_ = v___x_2261_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_e_2249_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
else
{
lean_object* v_val_2273_; lean_object* v___x_2275_; 
lean_dec_ref(v_e_2249_);
v_val_2273_ = lean_ctor_get(v_e_x3f_2269_, 0);
lean_inc(v_val_2273_);
lean_dec_ref_known(v_e_x3f_2269_, 1);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 0, v_val_2273_);
v___x_2275_ = v___x_2261_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_val_2273_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
}
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
lean_dec_ref(v_e_2249_);
lean_dec_ref(v_post_2245_);
lean_dec_ref(v_pre_2244_);
v_a_2278_ = lean_ctor_get(v___x_2258_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___x_2258_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2258_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2278_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7(lean_object* v_pre_2286_, lean_object* v_post_2287_, uint8_t v_usedLetOnly_2288_, uint8_t v_skipConstInApp_2289_, uint8_t v_skipInstances_2290_, lean_object* v_fvars_2291_, lean_object* v_e_2292_, lean_object* v_a_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
if (lean_obj_tag(v_e_2292_) == 6)
{
lean_object* v_binderName_2301_; lean_object* v_binderType_2302_; lean_object* v_body_2303_; uint8_t v_binderInfo_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___f_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v_binderName_2301_ = lean_ctor_get(v_e_2292_, 0);
lean_inc(v_binderName_2301_);
v_binderType_2302_ = lean_ctor_get(v_e_2292_, 1);
lean_inc_ref(v_binderType_2302_);
v_body_2303_ = lean_ctor_get(v_e_2292_, 2);
lean_inc_ref(v_body_2303_);
v_binderInfo_2304_ = lean_ctor_get_uint8(v_e_2292_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2292_, 3);
v___x_2305_ = lean_box(v_usedLetOnly_2288_);
v___x_2306_ = lean_box(v_skipConstInApp_2289_);
v___x_2307_ = lean_box(v_skipInstances_2290_);
lean_inc_ref(v_post_2287_);
lean_inc_ref(v_pre_2286_);
lean_inc_ref(v_fvars_2291_);
v___f_2308_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7___lam__0___boxed), 16, 7);
lean_closure_set(v___f_2308_, 0, v_fvars_2291_);
lean_closure_set(v___f_2308_, 1, v_pre_2286_);
lean_closure_set(v___f_2308_, 2, v_post_2287_);
lean_closure_set(v___f_2308_, 3, v___x_2305_);
lean_closure_set(v___f_2308_, 4, v___x_2306_);
lean_closure_set(v___f_2308_, 5, v___x_2307_);
lean_closure_set(v___f_2308_, 6, v_body_2303_);
v___x_2309_ = lean_expr_instantiate_rev(v_binderType_2302_, v_fvars_2291_);
lean_dec_ref(v_fvars_2291_);
lean_dec_ref(v_binderType_2302_);
v___x_2310_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2286_, v_post_2287_, v_usedLetOnly_2288_, v_skipConstInApp_2289_, v_skipInstances_2290_, v___x_2309_, v_a_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v_a_2311_; uint8_t v___x_2312_; lean_object* v___x_2313_; 
v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_a_2311_);
lean_dec_ref_known(v___x_2310_, 1);
v___x_2312_ = 0;
v___x_2313_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_2301_, v_binderInfo_2304_, v_a_2311_, v___f_2308_, v___x_2312_, v_a_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
return v___x_2313_;
}
else
{
lean_dec_ref(v___f_2308_);
lean_dec(v_binderName_2301_);
return v___x_2310_;
}
}
else
{
lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2314_ = lean_expr_instantiate_rev(v_e_2292_, v_fvars_2291_);
lean_dec_ref(v_e_2292_);
lean_inc_ref(v_post_2287_);
lean_inc_ref(v_pre_2286_);
v___x_2315_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2286_, v_post_2287_, v_usedLetOnly_2288_, v_skipConstInApp_2289_, v_skipInstances_2290_, v___x_2314_, v_a_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; uint8_t v___x_2317_; uint8_t v___x_2318_; uint8_t v___x_2319_; lean_object* v___x_2320_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2316_);
lean_dec_ref_known(v___x_2315_, 1);
v___x_2317_ = 0;
v___x_2318_ = 1;
v___x_2319_ = 1;
v___x_2320_ = l_Lean_Meta_mkLambdaFVars(v_fvars_2291_, v_a_2316_, v___x_2317_, v_usedLetOnly_2288_, v___x_2317_, v___x_2318_, v___x_2319_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
lean_dec_ref(v_fvars_2291_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_a_2321_; lean_object* v___x_2322_; 
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2321_);
lean_dec_ref_known(v___x_2320_, 1);
v___x_2322_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2286_, v_post_2287_, v_usedLetOnly_2288_, v_skipConstInApp_2289_, v_skipInstances_2290_, v_a_2321_, v_a_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
return v___x_2322_;
}
else
{
lean_dec_ref(v_post_2287_);
lean_dec_ref(v_pre_2286_);
return v___x_2320_;
}
}
else
{
lean_dec_ref(v_fvars_2291_);
lean_dec_ref(v_post_2287_);
lean_dec_ref(v_pre_2286_);
return v___x_2315_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8___lam__0(lean_object* v_fvars_2323_, lean_object* v_pre_2324_, lean_object* v_post_2325_, uint8_t v_usedLetOnly_2326_, uint8_t v_skipConstInApp_2327_, uint8_t v_skipInstances_2328_, lean_object* v_body_2329_, lean_object* v_x_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2339_ = lean_array_push(v_fvars_2323_, v_x_2330_);
v___x_2340_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8(v_pre_2324_, v_post_2325_, v_usedLetOnly_2326_, v_skipConstInApp_2327_, v_skipInstances_2328_, v___x_2339_, v_body_2329_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
return v___x_2340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8___lam__0___boxed(lean_object* v_fvars_2341_, lean_object* v_pre_2342_, lean_object* v_post_2343_, lean_object* v_usedLetOnly_2344_, lean_object* v_skipConstInApp_2345_, lean_object* v_skipInstances_2346_, lean_object* v_body_2347_, lean_object* v_x_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
uint8_t v_usedLetOnly_boxed_2357_; uint8_t v_skipConstInApp_boxed_2358_; uint8_t v_skipInstances_boxed_2359_; lean_object* v_res_2360_; 
v_usedLetOnly_boxed_2357_ = lean_unbox(v_usedLetOnly_2344_);
v_skipConstInApp_boxed_2358_ = lean_unbox(v_skipConstInApp_2345_);
v_skipInstances_boxed_2359_ = lean_unbox(v_skipInstances_2346_);
v_res_2360_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8___lam__0(v_fvars_2341_, v_pre_2342_, v_post_2343_, v_usedLetOnly_boxed_2357_, v_skipConstInApp_boxed_2358_, v_skipInstances_boxed_2359_, v_body_2347_, v_x_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v___y_2349_);
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8(lean_object* v_pre_2361_, lean_object* v_post_2362_, uint8_t v_usedLetOnly_2363_, uint8_t v_skipConstInApp_2364_, uint8_t v_skipInstances_2365_, lean_object* v_fvars_2366_, lean_object* v_e_2367_, lean_object* v_a_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_){
_start:
{
if (lean_obj_tag(v_e_2367_) == 8)
{
lean_object* v_declName_2376_; lean_object* v_type_2377_; lean_object* v_value_2378_; lean_object* v_body_2379_; uint8_t v_nondep_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___f_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v_declName_2376_ = lean_ctor_get(v_e_2367_, 0);
lean_inc(v_declName_2376_);
v_type_2377_ = lean_ctor_get(v_e_2367_, 1);
lean_inc_ref(v_type_2377_);
v_value_2378_ = lean_ctor_get(v_e_2367_, 2);
lean_inc_ref(v_value_2378_);
v_body_2379_ = lean_ctor_get(v_e_2367_, 3);
lean_inc_ref(v_body_2379_);
v_nondep_2380_ = lean_ctor_get_uint8(v_e_2367_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2367_, 4);
v___x_2381_ = lean_box(v_usedLetOnly_2363_);
v___x_2382_ = lean_box(v_skipConstInApp_2364_);
v___x_2383_ = lean_box(v_skipInstances_2365_);
lean_inc_ref_n(v_post_2362_, 2);
lean_inc_ref_n(v_pre_2361_, 2);
lean_inc_ref(v_fvars_2366_);
v___f_2384_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8___lam__0___boxed), 16, 7);
lean_closure_set(v___f_2384_, 0, v_fvars_2366_);
lean_closure_set(v___f_2384_, 1, v_pre_2361_);
lean_closure_set(v___f_2384_, 2, v_post_2362_);
lean_closure_set(v___f_2384_, 3, v___x_2381_);
lean_closure_set(v___f_2384_, 4, v___x_2382_);
lean_closure_set(v___f_2384_, 5, v___x_2383_);
lean_closure_set(v___f_2384_, 6, v_body_2379_);
v___x_2385_ = lean_expr_instantiate_rev(v_type_2377_, v_fvars_2366_);
lean_dec_ref(v_type_2377_);
v___x_2386_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2361_, v_post_2362_, v_usedLetOnly_2363_, v_skipConstInApp_2364_, v_skipInstances_2365_, v___x_2385_, v_a_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v_a_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
lean_inc(v_a_2387_);
lean_dec_ref_known(v___x_2386_, 1);
v___x_2388_ = lean_expr_instantiate_rev(v_value_2378_, v_fvars_2366_);
lean_dec_ref(v_fvars_2366_);
lean_dec_ref(v_value_2378_);
v___x_2389_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2361_, v_post_2362_, v_usedLetOnly_2363_, v_skipConstInApp_2364_, v_skipInstances_2365_, v___x_2388_, v_a_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
if (lean_obj_tag(v___x_2389_) == 0)
{
lean_object* v_a_2390_; uint8_t v___x_2391_; lean_object* v___x_2392_; 
v_a_2390_ = lean_ctor_get(v___x_2389_, 0);
lean_inc(v_a_2390_);
lean_dec_ref_known(v___x_2389_, 1);
v___x_2391_ = 0;
v___x_2392_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11___redArg(v_declName_2376_, v_a_2387_, v_a_2390_, v___f_2384_, v_nondep_2380_, v___x_2391_, v_a_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
return v___x_2392_;
}
else
{
lean_dec(v_a_2387_);
lean_dec_ref(v___f_2384_);
lean_dec(v_declName_2376_);
return v___x_2389_;
}
}
else
{
lean_dec_ref(v___f_2384_);
lean_dec_ref(v_value_2378_);
lean_dec(v_declName_2376_);
lean_dec_ref(v_fvars_2366_);
lean_dec_ref(v_post_2362_);
lean_dec_ref(v_pre_2361_);
return v___x_2386_;
}
}
else
{
lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2393_ = lean_expr_instantiate_rev(v_e_2367_, v_fvars_2366_);
lean_dec_ref(v_e_2367_);
lean_inc_ref(v_post_2362_);
lean_inc_ref(v_pre_2361_);
v___x_2394_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2361_, v_post_2362_, v_usedLetOnly_2363_, v_skipConstInApp_2364_, v_skipInstances_2365_, v___x_2393_, v_a_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v_a_2395_; uint8_t v___x_2396_; uint8_t v___x_2397_; lean_object* v___x_2398_; 
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
lean_inc(v_a_2395_);
lean_dec_ref_known(v___x_2394_, 1);
v___x_2396_ = 0;
v___x_2397_ = 1;
v___x_2398_ = l_Lean_Meta_mkLetFVars(v_fvars_2366_, v_a_2395_, v_usedLetOnly_2363_, v___x_2396_, v___x_2397_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
lean_dec_ref(v_fvars_2366_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_object* v_a_2399_; lean_object* v___x_2400_; 
v_a_2399_ = lean_ctor_get(v___x_2398_, 0);
lean_inc(v_a_2399_);
lean_dec_ref_known(v___x_2398_, 1);
v___x_2400_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2361_, v_post_2362_, v_usedLetOnly_2363_, v_skipConstInApp_2364_, v_skipInstances_2365_, v_a_2399_, v_a_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
return v___x_2400_;
}
else
{
lean_dec_ref(v_post_2362_);
lean_dec_ref(v_pre_2361_);
return v___x_2398_;
}
}
else
{
lean_dec_ref(v_fvars_2366_);
lean_dec_ref(v_post_2362_);
lean_dec_ref(v_pre_2361_);
return v___x_2394_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2401_; lean_object* v_dummy_2402_; 
v___x_2401_ = lean_box(0);
v_dummy_2402_ = l_Lean_Expr_sort___override(v___x_2401_);
return v_dummy_2402_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__2(lean_object* v_pre_2403_, lean_object* v_post_2404_, uint8_t v_usedLetOnly_2405_, uint8_t v_skipConstInApp_2406_, uint8_t v_skipInstances_2407_, size_t v_sz_2408_, size_t v_i_2409_, lean_object* v_bs_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
uint8_t v___x_2419_; 
v___x_2419_ = lean_usize_dec_lt(v_i_2409_, v_sz_2408_);
if (v___x_2419_ == 0)
{
lean_object* v___x_2420_; 
lean_dec_ref(v_post_2404_);
lean_dec_ref(v_pre_2403_);
v___x_2420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2420_, 0, v_bs_2410_);
return v___x_2420_;
}
else
{
lean_object* v_v_2421_; lean_object* v___x_2422_; lean_object* v_bs_x27_2423_; lean_object* v___x_2424_; 
v_v_2421_ = lean_array_uget(v_bs_2410_, v_i_2409_);
v___x_2422_ = lean_unsigned_to_nat(0u);
v_bs_x27_2423_ = lean_array_uset(v_bs_2410_, v_i_2409_, v___x_2422_);
lean_inc_ref(v_post_2404_);
lean_inc_ref(v_pre_2403_);
v___x_2424_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2403_, v_post_2404_, v_usedLetOnly_2405_, v_skipConstInApp_2406_, v_skipInstances_2407_, v_v_2421_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_object* v_a_2425_; size_t v___x_2426_; size_t v___x_2427_; lean_object* v___x_2428_; 
v_a_2425_ = lean_ctor_get(v___x_2424_, 0);
lean_inc(v_a_2425_);
lean_dec_ref_known(v___x_2424_, 1);
v___x_2426_ = ((size_t)1ULL);
v___x_2427_ = lean_usize_add(v_i_2409_, v___x_2426_);
v___x_2428_ = lean_array_uset(v_bs_x27_2423_, v_i_2409_, v_a_2425_);
v_i_2409_ = v___x_2427_;
v_bs_2410_ = v___x_2428_;
goto _start;
}
else
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2437_; 
lean_dec_ref(v_bs_x27_2423_);
lean_dec_ref(v_post_2404_);
lean_dec_ref(v_pre_2403_);
v_a_2430_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2432_ = v___x_2424_;
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2424_);
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
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__0(lean_object* v_pre_2438_, lean_object* v_post_2439_, uint8_t v_usedLetOnly_2440_, uint8_t v_skipConstInApp_2441_, uint8_t v_skipInstances_2442_, lean_object* v___x_2443_, lean_object* v___y_2444_, lean_object* v_b_2445_, lean_object* v_a_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_){
_start:
{
lean_object* v___x_2454_; 
v___x_2454_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2438_, v_post_2439_, v_usedLetOnly_2440_, v_skipConstInApp_2441_, v_skipInstances_2442_, v___x_2443_, v___y_2444_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2464_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2457_ = v___x_2454_;
v_isShared_2458_ = v_isSharedCheck_2464_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2454_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2464_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2462_; 
v___x_2459_ = lean_array_fset(v_b_2445_, v_a_2446_, v_a_2455_);
v___x_2460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2459_);
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 0, v___x_2460_);
v___x_2462_ = v___x_2457_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v___x_2460_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
else
{
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2472_; 
lean_dec_ref(v_b_2445_);
v_a_2465_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2467_ = v___x_2454_;
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___x_2454_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2470_; 
if (v_isShared_2468_ == 0)
{
v___x_2470_ = v___x_2467_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_a_2465_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__0___boxed(lean_object* v_pre_2473_, lean_object* v_post_2474_, lean_object* v_usedLetOnly_2475_, lean_object* v_skipConstInApp_2476_, lean_object* v_skipInstances_2477_, lean_object* v___x_2478_, lean_object* v___y_2479_, lean_object* v_b_2480_, lean_object* v_a_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_){
_start:
{
uint8_t v_usedLetOnly_boxed_2489_; uint8_t v_skipConstInApp_boxed_2490_; uint8_t v_skipInstances_boxed_2491_; lean_object* v_res_2492_; 
v_usedLetOnly_boxed_2489_ = lean_unbox(v_usedLetOnly_2475_);
v_skipConstInApp_boxed_2490_ = lean_unbox(v_skipConstInApp_2476_);
v_skipInstances_boxed_2491_ = lean_unbox(v_skipInstances_2477_);
v_res_2492_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__0(v_pre_2473_, v_post_2474_, v_usedLetOnly_boxed_2489_, v_skipConstInApp_boxed_2490_, v_skipInstances_boxed_2491_, v___x_2478_, v___y_2479_, v_b_2480_, v_a_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec(v_a_2481_);
lean_dec(v___y_2479_);
return v_res_2492_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg(lean_object* v_upperBound_2493_, lean_object* v___x_2494_, lean_object* v_pre_2495_, lean_object* v_post_2496_, uint8_t v_usedLetOnly_2497_, uint8_t v_skipConstInApp_2498_, uint8_t v_skipInstances_2499_, lean_object* v_a_2500_, lean_object* v_b_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
lean_object* v___y_2511_; uint8_t v___x_2534_; 
v___x_2534_ = lean_nat_dec_lt(v_a_2500_, v_upperBound_2493_);
if (v___x_2534_ == 0)
{
lean_object* v___x_2535_; 
lean_dec(v_a_2500_);
lean_dec_ref(v_post_2496_);
lean_dec_ref(v_pre_2495_);
v___x_2535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2535_, 0, v_b_2501_);
return v___x_2535_;
}
else
{
lean_object* v___x_2536_; lean_object* v___x_2537_; uint8_t v___x_2538_; 
v___x_2536_ = lean_array_fget_borrowed(v_b_2501_, v_a_2500_);
v___x_2537_ = lean_array_get_size(v___x_2494_);
v___x_2538_ = lean_nat_dec_lt(v_a_2500_, v___x_2537_);
if (v___x_2538_ == 0)
{
lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___f_2542_; 
lean_inc(v___x_2536_);
v___x_2539_ = lean_box(v_usedLetOnly_2497_);
v___x_2540_ = lean_box(v_skipConstInApp_2498_);
v___x_2541_ = lean_box(v_skipInstances_2499_);
lean_inc(v_a_2500_);
lean_inc(v___y_2502_);
lean_inc_ref(v_post_2496_);
lean_inc_ref(v_pre_2495_);
v___f_2542_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 16, 9);
lean_closure_set(v___f_2542_, 0, v_pre_2495_);
lean_closure_set(v___f_2542_, 1, v_post_2496_);
lean_closure_set(v___f_2542_, 2, v___x_2539_);
lean_closure_set(v___f_2542_, 3, v___x_2540_);
lean_closure_set(v___f_2542_, 4, v___x_2541_);
lean_closure_set(v___f_2542_, 5, v___x_2536_);
lean_closure_set(v___f_2542_, 6, v___y_2502_);
lean_closure_set(v___f_2542_, 7, v_b_2501_);
lean_closure_set(v___f_2542_, 8, v_a_2500_);
v___y_2511_ = v___f_2542_;
goto v___jp_2510_;
}
else
{
lean_object* v___x_2543_; uint8_t v_isInstance_2544_; 
v___x_2543_ = lean_array_fget_borrowed(v___x_2494_, v_a_2500_);
v_isInstance_2544_ = lean_ctor_get_uint8(v___x_2543_, sizeof(void*)*1 + 4);
if (v_isInstance_2544_ == 0)
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___f_2548_; 
lean_inc(v___x_2536_);
v___x_2545_ = lean_box(v_usedLetOnly_2497_);
v___x_2546_ = lean_box(v_skipConstInApp_2498_);
v___x_2547_ = lean_box(v_skipInstances_2499_);
lean_inc(v_a_2500_);
lean_inc(v___y_2502_);
lean_inc_ref(v_post_2496_);
lean_inc_ref(v_pre_2495_);
v___f_2548_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 16, 9);
lean_closure_set(v___f_2548_, 0, v_pre_2495_);
lean_closure_set(v___f_2548_, 1, v_post_2496_);
lean_closure_set(v___f_2548_, 2, v___x_2545_);
lean_closure_set(v___f_2548_, 3, v___x_2546_);
lean_closure_set(v___f_2548_, 4, v___x_2547_);
lean_closure_set(v___f_2548_, 5, v___x_2536_);
lean_closure_set(v___f_2548_, 6, v___y_2502_);
lean_closure_set(v___f_2548_, 7, v_b_2501_);
lean_closure_set(v___f_2548_, 8, v_a_2500_);
v___y_2511_ = v___f_2548_;
goto v___jp_2510_;
}
else
{
lean_object* v___x_2549_; lean_object* v___f_2550_; 
v___x_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2549_, 0, v_b_2501_);
v___f_2550_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__2___boxed), 8, 1);
lean_closure_set(v___f_2550_, 0, v___x_2549_);
v___y_2511_ = v___f_2550_;
goto v___jp_2510_;
}
}
}
v___jp_2510_:
{
lean_object* v___x_2512_; 
lean_inc(v___y_2508_);
lean_inc_ref(v___y_2507_);
lean_inc(v___y_2506_);
lean_inc_ref(v___y_2505_);
lean_inc(v___y_2504_);
lean_inc_ref(v___y_2503_);
v___x_2512_ = lean_apply_7(v___y_2511_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, lean_box(0));
if (lean_obj_tag(v___x_2512_) == 0)
{
lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2525_; 
v_a_2513_ = lean_ctor_get(v___x_2512_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2515_ = v___x_2512_;
v_isShared_2516_ = v_isSharedCheck_2525_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2512_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2525_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
if (lean_obj_tag(v_a_2513_) == 0)
{
lean_object* v_a_2517_; lean_object* v___x_2519_; 
lean_dec(v_a_2500_);
lean_dec_ref(v_post_2496_);
lean_dec_ref(v_pre_2495_);
v_a_2517_ = lean_ctor_get(v_a_2513_, 0);
lean_inc(v_a_2517_);
lean_dec_ref_known(v_a_2513_, 1);
if (v_isShared_2516_ == 0)
{
lean_ctor_set(v___x_2515_, 0, v_a_2517_);
v___x_2519_ = v___x_2515_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_a_2517_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
else
{
lean_object* v_a_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
lean_del_object(v___x_2515_);
v_a_2521_ = lean_ctor_get(v_a_2513_, 0);
lean_inc(v_a_2521_);
lean_dec_ref_known(v_a_2513_, 1);
v___x_2522_ = lean_unsigned_to_nat(1u);
v___x_2523_ = lean_nat_add(v_a_2500_, v___x_2522_);
lean_dec(v_a_2500_);
v_a_2500_ = v___x_2523_;
v_b_2501_ = v_a_2521_;
goto _start;
}
}
}
else
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
lean_dec(v_a_2500_);
lean_dec_ref(v_post_2496_);
lean_dec_ref(v_pre_2495_);
v_a_2526_ = lean_ctor_get(v___x_2512_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2528_ = v___x_2512_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2512_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2526_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__9(uint8_t v_skipInstances_2551_, lean_object* v_pre_2552_, lean_object* v_post_2553_, uint8_t v_usedLetOnly_2554_, uint8_t v_skipConstInApp_2555_, lean_object* v_x_2556_, lean_object* v_x_2557_, lean_object* v_x_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v_f_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; 
if (lean_obj_tag(v_x_2556_) == 5)
{
lean_object* v_fn_2618_; lean_object* v_arg_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; 
v_fn_2618_ = lean_ctor_get(v_x_2556_, 0);
lean_inc_ref(v_fn_2618_);
v_arg_2619_ = lean_ctor_get(v_x_2556_, 1);
lean_inc_ref(v_arg_2619_);
lean_dec_ref_known(v_x_2556_, 2);
v___x_2620_ = lean_array_set(v_x_2557_, v_x_2558_, v_arg_2619_);
v___x_2621_ = lean_unsigned_to_nat(1u);
v___x_2622_ = lean_nat_sub(v_x_2558_, v___x_2621_);
lean_dec(v_x_2558_);
v_x_2556_ = v_fn_2618_;
v_x_2557_ = v___x_2620_;
v_x_2558_ = v___x_2622_;
goto _start;
}
else
{
lean_dec(v_x_2558_);
if (v_skipConstInApp_2555_ == 0)
{
goto v___jp_2615_;
}
else
{
uint8_t v___x_2624_; 
v___x_2624_ = l_Lean_Expr_isConst(v_x_2556_);
if (v___x_2624_ == 0)
{
goto v___jp_2615_;
}
else
{
v_f_2568_ = v_x_2556_;
v___y_2569_ = v___y_2559_;
v___y_2570_ = v___y_2560_;
v___y_2571_ = v___y_2561_;
v___y_2572_ = v___y_2562_;
v___y_2573_ = v___y_2563_;
v___y_2574_ = v___y_2564_;
v___y_2575_ = v___y_2565_;
goto v___jp_2567_;
}
}
}
v___jp_2567_:
{
if (v_skipInstances_2551_ == 0)
{
size_t v_sz_2576_; size_t v___x_2577_; lean_object* v___x_2578_; 
v_sz_2576_ = lean_array_size(v_x_2557_);
v___x_2577_ = ((size_t)0ULL);
lean_inc_ref(v_post_2553_);
lean_inc_ref(v_pre_2552_);
v___x_2578_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__2(v_pre_2552_, v_post_2553_, v_usedLetOnly_2554_, v_skipConstInApp_2555_, v_skipInstances_2551_, v_sz_2576_, v___x_2577_, v_x_2557_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
if (lean_obj_tag(v___x_2578_) == 0)
{
lean_object* v_a_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
v_a_2579_ = lean_ctor_get(v___x_2578_, 0);
lean_inc(v_a_2579_);
lean_dec_ref_known(v___x_2578_, 1);
v___x_2580_ = l_Lean_mkAppN(v_f_2568_, v_a_2579_);
lean_dec(v_a_2579_);
v___x_2581_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2552_, v_post_2553_, v_usedLetOnly_2554_, v_skipConstInApp_2555_, v_skipInstances_2551_, v___x_2580_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
return v___x_2581_;
}
else
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2589_; 
lean_dec_ref(v_f_2568_);
lean_dec_ref(v_post_2553_);
lean_dec_ref(v_pre_2552_);
v_a_2582_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2584_ = v___x_2578_;
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___x_2578_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2587_; 
if (v_isShared_2585_ == 0)
{
v___x_2587_ = v___x_2584_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_a_2582_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
}
else
{
lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2590_ = lean_array_get_size(v_x_2557_);
lean_inc_ref(v_f_2568_);
v___x_2591_ = l_Lean_Meta_getFunInfoNArgs(v_f_2568_, v___x_2590_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; lean_object* v_paramInfo_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc(v_a_2592_);
lean_dec_ref_known(v___x_2591_, 1);
v_paramInfo_2593_ = lean_ctor_get(v_a_2592_, 0);
lean_inc_ref(v_paramInfo_2593_);
lean_dec(v_a_2592_);
v___x_2594_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_2553_);
lean_inc_ref(v_pre_2552_);
v___x_2595_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg(v___x_2590_, v_paramInfo_2593_, v_pre_2552_, v_post_2553_, v_usedLetOnly_2554_, v_skipConstInApp_2555_, v_skipInstances_2551_, v___x_2594_, v_x_2557_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
lean_dec_ref(v_paramInfo_2593_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
lean_inc(v_a_2596_);
lean_dec_ref_known(v___x_2595_, 1);
v___x_2597_ = l_Lean_mkAppN(v_f_2568_, v_a_2596_);
lean_dec(v_a_2596_);
v___x_2598_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2552_, v_post_2553_, v_usedLetOnly_2554_, v_skipConstInApp_2555_, v_skipInstances_2551_, v___x_2597_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
return v___x_2598_;
}
else
{
lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2606_; 
lean_dec_ref(v_f_2568_);
lean_dec_ref(v_post_2553_);
lean_dec_ref(v_pre_2552_);
v_a_2599_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2601_ = v___x_2595_;
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_a_2599_);
lean_dec(v___x_2595_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2604_; 
if (v_isShared_2602_ == 0)
{
v___x_2604_ = v___x_2601_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_a_2599_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
}
}
else
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
lean_dec_ref(v_f_2568_);
lean_dec_ref(v_x_2557_);
lean_dec_ref(v_post_2553_);
lean_dec_ref(v_pre_2552_);
v_a_2607_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2609_ = v___x_2591_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2591_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2612_; 
if (v_isShared_2610_ == 0)
{
v___x_2612_ = v___x_2609_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2607_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
}
}
v___jp_2615_:
{
lean_object* v___x_2616_; 
lean_inc_ref(v_post_2553_);
lean_inc_ref(v_pre_2552_);
v___x_2616_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2552_, v_post_2553_, v_usedLetOnly_2554_, v_skipConstInApp_2555_, v_skipInstances_2551_, v_x_2556_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v_a_2617_; 
v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_a_2617_);
lean_dec_ref_known(v___x_2616_, 1);
v_f_2568_ = v_a_2617_;
v___y_2569_ = v___y_2559_;
v___y_2570_ = v___y_2560_;
v___y_2571_ = v___y_2561_;
v___y_2572_ = v___y_2562_;
v___y_2573_ = v___y_2563_;
v___y_2574_ = v___y_2564_;
v___y_2575_ = v___y_2565_;
goto v___jp_2567_;
}
else
{
lean_dec_ref(v_x_2557_);
lean_dec_ref(v_post_2553_);
lean_dec_ref(v_pre_2552_);
return v___x_2616_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1(lean_object* v___x_2625_, lean_object* v_pre_2626_, lean_object* v_e_2627_, lean_object* v_post_2628_, uint8_t v_usedLetOnly_2629_, uint8_t v_skipConstInApp_2630_, uint8_t v_skipInstances_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_){
_start:
{
lean_object* v___x_2640_; 
v___x_2640_ = l_Lean_Core_checkSystem(v___x_2625_, v___y_2637_, v___y_2638_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v___x_2641_; 
lean_dec_ref_known(v___x_2640_, 1);
lean_inc_ref(v_pre_2626_);
lean_inc(v___y_2638_);
lean_inc_ref(v___y_2637_);
lean_inc(v___y_2636_);
lean_inc_ref(v___y_2635_);
lean_inc(v___y_2634_);
lean_inc_ref(v___y_2633_);
lean_inc_ref(v_e_2627_);
v___x_2641_ = lean_apply_8(v_pre_2626_, v_e_2627_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, lean_box(0));
if (lean_obj_tag(v___x_2641_) == 0)
{
lean_object* v_a_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2690_; 
v_a_2642_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2644_ = v___x_2641_;
v_isShared_2645_ = v_isSharedCheck_2690_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_a_2642_);
lean_dec(v___x_2641_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2690_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
lean_object* v___y_2647_; 
switch(lean_obj_tag(v_a_2642_))
{
case 0:
{
lean_object* v_e_2682_; lean_object* v___x_2684_; 
lean_dec_ref(v_post_2628_);
lean_dec_ref(v_e_2627_);
lean_dec_ref(v_pre_2626_);
v_e_2682_ = lean_ctor_get(v_a_2642_, 0);
lean_inc_ref(v_e_2682_);
lean_dec_ref_known(v_a_2642_, 1);
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 0, v_e_2682_);
v___x_2684_ = v___x_2644_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_e_2682_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
case 1:
{
lean_object* v_e_2686_; lean_object* v___x_2687_; 
lean_del_object(v___x_2644_);
lean_dec_ref(v_e_2627_);
v_e_2686_ = lean_ctor_get(v_a_2642_, 0);
lean_inc_ref(v_e_2686_);
lean_dec_ref_known(v_a_2642_, 1);
v___x_2687_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2626_, v_post_2628_, v_usedLetOnly_2629_, v_skipConstInApp_2630_, v_skipInstances_2631_, v_e_2686_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
return v___x_2687_;
}
default: 
{
lean_object* v_e_x3f_2688_; 
lean_del_object(v___x_2644_);
v_e_x3f_2688_ = lean_ctor_get(v_a_2642_, 0);
lean_inc(v_e_x3f_2688_);
lean_dec_ref_known(v_a_2642_, 1);
if (lean_obj_tag(v_e_x3f_2688_) == 0)
{
v___y_2647_ = v_e_2627_;
goto v___jp_2646_;
}
else
{
lean_object* v_val_2689_; 
lean_dec_ref(v_e_2627_);
v_val_2689_ = lean_ctor_get(v_e_x3f_2688_, 0);
lean_inc(v_val_2689_);
lean_dec_ref_known(v_e_x3f_2688_, 1);
v___y_2647_ = v_val_2689_;
goto v___jp_2646_;
}
}
}
v___jp_2646_:
{
switch(lean_obj_tag(v___y_2647_))
{
case 7:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2648_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___closed__0));
v___x_2649_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6(v_pre_2626_, v_post_2628_, v_usedLetOnly_2629_, v_skipConstInApp_2630_, v_skipInstances_2631_, v___x_2648_, v___y_2647_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
return v___x_2649_;
}
case 6:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2650_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___closed__0));
v___x_2651_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7(v_pre_2626_, v_post_2628_, v_usedLetOnly_2629_, v_skipConstInApp_2630_, v_skipInstances_2631_, v___x_2650_, v___y_2647_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
return v___x_2651_;
}
case 8:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; 
v___x_2652_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___closed__0));
v___x_2653_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8(v_pre_2626_, v_post_2628_, v_usedLetOnly_2629_, v_skipConstInApp_2630_, v_skipInstances_2631_, v___x_2652_, v___y_2647_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
return v___x_2653_;
}
case 5:
{
lean_object* v_dummy_2654_; lean_object* v_nargs_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v_dummy_2654_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___closed__1);
v_nargs_2655_ = l_Lean_Expr_getAppNumArgs(v___y_2647_);
lean_inc(v_nargs_2655_);
v___x_2656_ = lean_mk_array(v_nargs_2655_, v_dummy_2654_);
v___x_2657_ = lean_unsigned_to_nat(1u);
v___x_2658_ = lean_nat_sub(v_nargs_2655_, v___x_2657_);
lean_dec(v_nargs_2655_);
v___x_2659_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__9(v_skipInstances_2631_, v_pre_2626_, v_post_2628_, v_usedLetOnly_2629_, v_skipConstInApp_2630_, v___y_2647_, v___x_2656_, v___x_2658_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
return v___x_2659_;
}
case 10:
{
lean_object* v_data_2660_; lean_object* v_expr_2661_; lean_object* v___x_2662_; 
v_data_2660_ = lean_ctor_get(v___y_2647_, 0);
v_expr_2661_ = lean_ctor_get(v___y_2647_, 1);
lean_inc_ref(v_expr_2661_);
lean_inc_ref(v_post_2628_);
lean_inc_ref(v_pre_2626_);
v___x_2662_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2626_, v_post_2628_, v_usedLetOnly_2629_, v_skipConstInApp_2630_, v_skipInstances_2631_, v_expr_2661_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v_a_2663_; size_t v___x_2664_; size_t v___x_2665_; uint8_t v___x_2666_; 
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
lean_inc(v_a_2663_);
lean_dec_ref_known(v___x_2662_, 1);
v___x_2664_ = lean_ptr_addr(v_expr_2661_);
v___x_2665_ = lean_ptr_addr(v_a_2663_);
v___x_2666_ = lean_usize_dec_eq(v___x_2664_, v___x_2665_);
if (v___x_2666_ == 0)
{
lean_object* v___x_2667_; lean_object* v___x_2668_; 
lean_inc(v_data_2660_);
lean_dec_ref_known(v___y_2647_, 2);
v___x_2667_ = l_Lean_Expr_mdata___override(v_data_2660_, v_a_2663_);
v___x_2668_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2626_, v_post_2628_, v_usedLetOnly_2629_, v_skipConstInApp_2630_, v_skipInstances_2631_, v___x_2667_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
return v___x_2668_;
}
else
{
lean_object* v___x_2669_; 
lean_dec(v_a_2663_);
v___x_2669_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2626_, v_post_2628_, v_usedLetOnly_2629_, v_skipConstInApp_2630_, v_skipInstances_2631_, v___y_2647_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
return v___x_2669_;
}
}
else
{
lean_dec_ref_known(v___y_2647_, 2);
lean_dec_ref(v_post_2628_);
lean_dec_ref(v_pre_2626_);
return v___x_2662_;
}
}
case 11:
{
lean_object* v_typeName_2670_; lean_object* v_idx_2671_; lean_object* v_struct_2672_; lean_object* v___x_2673_; 
v_typeName_2670_ = lean_ctor_get(v___y_2647_, 0);
v_idx_2671_ = lean_ctor_get(v___y_2647_, 1);
v_struct_2672_ = lean_ctor_get(v___y_2647_, 2);
lean_inc_ref(v_struct_2672_);
lean_inc_ref(v_post_2628_);
lean_inc_ref(v_pre_2626_);
v___x_2673_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2626_, v_post_2628_, v_usedLetOnly_2629_, v_skipConstInApp_2630_, v_skipInstances_2631_, v_struct_2672_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_object* v_a_2674_; size_t v___x_2675_; size_t v___x_2676_; uint8_t v___x_2677_; 
v_a_2674_ = lean_ctor_get(v___x_2673_, 0);
lean_inc(v_a_2674_);
lean_dec_ref_known(v___x_2673_, 1);
v___x_2675_ = lean_ptr_addr(v_struct_2672_);
v___x_2676_ = lean_ptr_addr(v_a_2674_);
v___x_2677_ = lean_usize_dec_eq(v___x_2675_, v___x_2676_);
if (v___x_2677_ == 0)
{
lean_object* v___x_2678_; lean_object* v___x_2679_; 
lean_inc(v_idx_2671_);
lean_inc(v_typeName_2670_);
lean_dec_ref_known(v___y_2647_, 3);
v___x_2678_ = l_Lean_Expr_proj___override(v_typeName_2670_, v_idx_2671_, v_a_2674_);
v___x_2679_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2626_, v_post_2628_, v_usedLetOnly_2629_, v_skipConstInApp_2630_, v_skipInstances_2631_, v___x_2678_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
return v___x_2679_;
}
else
{
lean_object* v___x_2680_; 
lean_dec(v_a_2674_);
v___x_2680_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2626_, v_post_2628_, v_usedLetOnly_2629_, v_skipConstInApp_2630_, v_skipInstances_2631_, v___y_2647_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
return v___x_2680_;
}
}
else
{
lean_dec_ref_known(v___y_2647_, 3);
lean_dec_ref(v_post_2628_);
lean_dec_ref(v_pre_2626_);
return v___x_2673_;
}
}
default: 
{
lean_object* v___x_2681_; 
v___x_2681_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2626_, v_post_2628_, v_usedLetOnly_2629_, v_skipConstInApp_2630_, v_skipInstances_2631_, v___y_2647_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
return v___x_2681_;
}
}
}
}
}
else
{
lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2698_; 
lean_dec_ref(v_post_2628_);
lean_dec_ref(v_e_2627_);
lean_dec_ref(v_pre_2626_);
v_a_2691_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2693_ = v___x_2641_;
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_dec(v___x_2641_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2696_; 
if (v_isShared_2694_ == 0)
{
v___x_2696_ = v___x_2693_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_a_2691_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
}
else
{
lean_object* v_a_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2706_; 
lean_dec_ref(v_post_2628_);
lean_dec_ref(v_e_2627_);
lean_dec_ref(v_pre_2626_);
v_a_2699_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2701_ = v___x_2640_;
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_a_2699_);
lean_dec(v___x_2640_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v___x_2704_; 
if (v_isShared_2702_ == 0)
{
v___x_2704_ = v___x_2701_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_a_2699_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___boxed(lean_object* v___x_2707_, lean_object* v_pre_2708_, lean_object* v_e_2709_, lean_object* v_post_2710_, lean_object* v_usedLetOnly_2711_, lean_object* v_skipConstInApp_2712_, lean_object* v_skipInstances_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_){
_start:
{
uint8_t v_usedLetOnly_boxed_2722_; uint8_t v_skipConstInApp_boxed_2723_; uint8_t v_skipInstances_boxed_2724_; lean_object* v_res_2725_; 
v_usedLetOnly_boxed_2722_ = lean_unbox(v_usedLetOnly_2711_);
v_skipConstInApp_boxed_2723_ = lean_unbox(v_skipConstInApp_2712_);
v_skipInstances_boxed_2724_ = lean_unbox(v_skipInstances_2713_);
v_res_2725_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1(v___x_2707_, v_pre_2708_, v_e_2709_, v_post_2710_, v_usedLetOnly_boxed_2722_, v_skipConstInApp_boxed_2723_, v_skipInstances_boxed_2724_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec(v___y_2716_);
lean_dec_ref(v___y_2715_);
lean_dec(v___y_2714_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(lean_object* v_pre_2726_, lean_object* v_post_2727_, uint8_t v_usedLetOnly_2728_, uint8_t v_skipConstInApp_2729_, uint8_t v_skipInstances_2730_, lean_object* v_e_2731_, lean_object* v_a_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
lean_object* v___x_2740_; lean_object* v___x_2741_; 
lean_inc(v_a_2732_);
v___x_2740_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2740_, 0, lean_box(0));
lean_closure_set(v___x_2740_, 1, lean_box(0));
lean_closure_set(v___x_2740_, 2, v_a_2732_);
v___x_2741_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__0(lean_box(0), v___x_2740_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_object* v_a_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2776_; 
v_a_2742_ = lean_ctor_get(v___x_2741_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2744_ = v___x_2741_;
v_isShared_2745_ = v_isSharedCheck_2776_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_a_2742_);
lean_dec(v___x_2741_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2776_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v___x_2746_; 
v___x_2746_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5___redArg(v_a_2742_, v_e_2731_);
lean_dec(v_a_2742_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___f_2751_; lean_object* v___x_2752_; 
lean_del_object(v___x_2744_);
v___x_2747_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___closed__0));
v___x_2748_ = lean_box(v_usedLetOnly_2728_);
v___x_2749_ = lean_box(v_skipConstInApp_2729_);
v___x_2750_ = lean_box(v_skipInstances_2730_);
lean_inc_ref(v_e_2731_);
v___f_2751_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___boxed), 15, 7);
lean_closure_set(v___f_2751_, 0, v___x_2747_);
lean_closure_set(v___f_2751_, 1, v_pre_2726_);
lean_closure_set(v___f_2751_, 2, v_e_2731_);
lean_closure_set(v___f_2751_, 3, v_post_2727_);
lean_closure_set(v___f_2751_, 4, v___x_2748_);
lean_closure_set(v___f_2751_, 5, v___x_2749_);
lean_closure_set(v___f_2751_, 6, v___x_2750_);
v___x_2752_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10___redArg(v___f_2751_, v_a_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
if (lean_obj_tag(v___x_2752_) == 0)
{
lean_object* v_a_2753_; lean_object* v___f_2754_; lean_object* v___x_2755_; 
v_a_2753_ = lean_ctor_get(v___x_2752_, 0);
lean_inc_n(v_a_2753_, 2);
lean_dec_ref_known(v___x_2752_, 1);
lean_inc(v_a_2732_);
v___f_2754_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2754_, 0, v_a_2732_);
lean_closure_set(v___f_2754_, 1, v_e_2731_);
lean_closure_set(v___f_2754_, 2, v_a_2753_);
v___x_2755_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__0(lean_box(0), v___f_2754_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
if (lean_obj_tag(v___x_2755_) == 0)
{
lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2762_ == 0)
{
lean_object* v_unused_2763_; 
v_unused_2763_ = lean_ctor_get(v___x_2755_, 0);
lean_dec(v_unused_2763_);
v___x_2757_ = v___x_2755_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_dec(v___x_2755_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
lean_ctor_set(v___x_2757_, 0, v_a_2753_);
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2753_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
else
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2771_; 
lean_dec(v_a_2753_);
v_a_2764_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2766_ = v___x_2755_;
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2755_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2769_; 
if (v_isShared_2767_ == 0)
{
v___x_2769_ = v___x_2766_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2764_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
}
}
else
{
lean_dec_ref(v_e_2731_);
return v___x_2752_;
}
}
else
{
lean_object* v_val_2772_; lean_object* v___x_2774_; 
lean_dec_ref(v_e_2731_);
lean_dec_ref(v_post_2727_);
lean_dec_ref(v_pre_2726_);
v_val_2772_ = lean_ctor_get(v___x_2746_, 0);
lean_inc(v_val_2772_);
lean_dec_ref_known(v___x_2746_, 1);
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 0, v_val_2772_);
v___x_2774_ = v___x_2744_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_val_2772_);
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
lean_dec_ref(v_e_2731_);
lean_dec_ref(v_post_2727_);
lean_dec_ref(v_pre_2726_);
v_a_2777_ = lean_ctor_get(v___x_2741_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2779_ = v___x_2741_;
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2741_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6(lean_object* v_pre_2785_, lean_object* v_post_2786_, uint8_t v_usedLetOnly_2787_, uint8_t v_skipConstInApp_2788_, uint8_t v_skipInstances_2789_, lean_object* v_fvars_2790_, lean_object* v_e_2791_, lean_object* v_a_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
if (lean_obj_tag(v_e_2791_) == 7)
{
lean_object* v_binderName_2800_; lean_object* v_binderType_2801_; lean_object* v_body_2802_; uint8_t v_binderInfo_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___f_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
v_binderName_2800_ = lean_ctor_get(v_e_2791_, 0);
lean_inc(v_binderName_2800_);
v_binderType_2801_ = lean_ctor_get(v_e_2791_, 1);
lean_inc_ref(v_binderType_2801_);
v_body_2802_ = lean_ctor_get(v_e_2791_, 2);
lean_inc_ref(v_body_2802_);
v_binderInfo_2803_ = lean_ctor_get_uint8(v_e_2791_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2791_, 3);
v___x_2804_ = lean_box(v_usedLetOnly_2787_);
v___x_2805_ = lean_box(v_skipConstInApp_2788_);
v___x_2806_ = lean_box(v_skipInstances_2789_);
lean_inc_ref(v_post_2786_);
lean_inc_ref(v_pre_2785_);
lean_inc_ref(v_fvars_2790_);
v___f_2807_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6___lam__0___boxed), 16, 7);
lean_closure_set(v___f_2807_, 0, v_fvars_2790_);
lean_closure_set(v___f_2807_, 1, v_pre_2785_);
lean_closure_set(v___f_2807_, 2, v_post_2786_);
lean_closure_set(v___f_2807_, 3, v___x_2804_);
lean_closure_set(v___f_2807_, 4, v___x_2805_);
lean_closure_set(v___f_2807_, 5, v___x_2806_);
lean_closure_set(v___f_2807_, 6, v_body_2802_);
v___x_2808_ = lean_expr_instantiate_rev(v_binderType_2801_, v_fvars_2790_);
lean_dec_ref(v_fvars_2790_);
lean_dec_ref(v_binderType_2801_);
v___x_2809_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2785_, v_post_2786_, v_usedLetOnly_2787_, v_skipConstInApp_2788_, v_skipInstances_2789_, v___x_2808_, v_a_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
if (lean_obj_tag(v___x_2809_) == 0)
{
lean_object* v_a_2810_; uint8_t v___x_2811_; lean_object* v___x_2812_; 
v_a_2810_ = lean_ctor_get(v___x_2809_, 0);
lean_inc(v_a_2810_);
lean_dec_ref_known(v___x_2809_, 1);
v___x_2811_ = 0;
v___x_2812_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_2800_, v_binderInfo_2803_, v_a_2810_, v___f_2807_, v___x_2811_, v_a_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
return v___x_2812_;
}
else
{
lean_dec_ref(v___f_2807_);
lean_dec(v_binderName_2800_);
return v___x_2809_;
}
}
else
{
lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2813_ = lean_expr_instantiate_rev(v_e_2791_, v_fvars_2790_);
lean_dec_ref(v_e_2791_);
lean_inc_ref(v_post_2786_);
lean_inc_ref(v_pre_2785_);
v___x_2814_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2785_, v_post_2786_, v_usedLetOnly_2787_, v_skipConstInApp_2788_, v_skipInstances_2789_, v___x_2813_, v_a_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_a_2815_; uint8_t v___x_2816_; uint8_t v___x_2817_; uint8_t v___x_2818_; lean_object* v___x_2819_; 
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2815_);
lean_dec_ref_known(v___x_2814_, 1);
v___x_2816_ = 0;
v___x_2817_ = 1;
v___x_2818_ = 1;
v___x_2819_ = l_Lean_Meta_mkForallFVars(v_fvars_2790_, v_a_2815_, v___x_2816_, v_usedLetOnly_2787_, v___x_2817_, v___x_2818_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
lean_dec_ref(v_fvars_2790_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v_a_2820_; lean_object* v___x_2821_; 
v_a_2820_ = lean_ctor_get(v___x_2819_, 0);
lean_inc(v_a_2820_);
lean_dec_ref_known(v___x_2819_, 1);
v___x_2821_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2785_, v_post_2786_, v_usedLetOnly_2787_, v_skipConstInApp_2788_, v_skipInstances_2789_, v_a_2820_, v_a_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
return v___x_2821_;
}
else
{
lean_dec_ref(v_post_2786_);
lean_dec_ref(v_pre_2785_);
return v___x_2819_;
}
}
else
{
lean_dec_ref(v_fvars_2790_);
lean_dec_ref(v_post_2786_);
lean_dec_ref(v_pre_2785_);
return v___x_2814_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6___lam__0(lean_object* v_fvars_2822_, lean_object* v_pre_2823_, lean_object* v_post_2824_, uint8_t v_usedLetOnly_2825_, uint8_t v_skipConstInApp_2826_, uint8_t v_skipInstances_2827_, lean_object* v_body_2828_, lean_object* v_x_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_){
_start:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; 
v___x_2838_ = lean_array_push(v_fvars_2822_, v_x_2829_);
v___x_2839_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6(v_pre_2823_, v_post_2824_, v_usedLetOnly_2825_, v_skipConstInApp_2826_, v_skipInstances_2827_, v___x_2838_, v_body_2828_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
return v___x_2839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_2840_, lean_object* v_post_2841_, lean_object* v_usedLetOnly_2842_, lean_object* v_skipConstInApp_2843_, lean_object* v_skipInstances_2844_, lean_object* v_e_2845_, lean_object* v_a_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_){
_start:
{
uint8_t v_usedLetOnly_boxed_2854_; uint8_t v_skipConstInApp_boxed_2855_; uint8_t v_skipInstances_boxed_2856_; lean_object* v_res_2857_; 
v_usedLetOnly_boxed_2854_ = lean_unbox(v_usedLetOnly_2842_);
v_skipConstInApp_boxed_2855_ = lean_unbox(v_skipConstInApp_2843_);
v_skipInstances_boxed_2856_ = lean_unbox(v_skipInstances_2844_);
v_res_2857_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2840_, v_post_2841_, v_usedLetOnly_boxed_2854_, v_skipConstInApp_boxed_2855_, v_skipInstances_boxed_2856_, v_e_2845_, v_a_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
lean_dec(v_a_2846_);
return v_res_2857_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_2858_, lean_object* v_post_2859_, lean_object* v_usedLetOnly_2860_, lean_object* v_skipConstInApp_2861_, lean_object* v_skipInstances_2862_, lean_object* v_sz_2863_, lean_object* v_i_2864_, lean_object* v_bs_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_){
_start:
{
uint8_t v_usedLetOnly_boxed_2874_; uint8_t v_skipConstInApp_boxed_2875_; uint8_t v_skipInstances_boxed_2876_; size_t v_sz_boxed_2877_; size_t v_i_boxed_2878_; lean_object* v_res_2879_; 
v_usedLetOnly_boxed_2874_ = lean_unbox(v_usedLetOnly_2860_);
v_skipConstInApp_boxed_2875_ = lean_unbox(v_skipConstInApp_2861_);
v_skipInstances_boxed_2876_ = lean_unbox(v_skipInstances_2862_);
v_sz_boxed_2877_ = lean_unbox_usize(v_sz_2863_);
lean_dec(v_sz_2863_);
v_i_boxed_2878_ = lean_unbox_usize(v_i_2864_);
lean_dec(v_i_2864_);
v_res_2879_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__2(v_pre_2858_, v_post_2859_, v_usedLetOnly_boxed_2874_, v_skipConstInApp_boxed_2875_, v_skipInstances_boxed_2876_, v_sz_boxed_2877_, v_i_boxed_2878_, v_bs_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
lean_dec(v___y_2866_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___boxed(lean_object* v_pre_2880_, lean_object* v_post_2881_, lean_object* v_usedLetOnly_2882_, lean_object* v_skipConstInApp_2883_, lean_object* v_skipInstances_2884_, lean_object* v_e_2885_, lean_object* v_a_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_){
_start:
{
uint8_t v_usedLetOnly_boxed_2894_; uint8_t v_skipConstInApp_boxed_2895_; uint8_t v_skipInstances_boxed_2896_; lean_object* v_res_2897_; 
v_usedLetOnly_boxed_2894_ = lean_unbox(v_usedLetOnly_2882_);
v_skipConstInApp_boxed_2895_ = lean_unbox(v_skipConstInApp_2883_);
v_skipInstances_boxed_2896_ = lean_unbox(v_skipInstances_2884_);
v_res_2897_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2880_, v_post_2881_, v_usedLetOnly_boxed_2894_, v_skipConstInApp_boxed_2895_, v_skipInstances_boxed_2896_, v_e_2885_, v_a_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
lean_dec(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
lean_dec(v_a_2886_);
return v_res_2897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6___boxed(lean_object* v_pre_2898_, lean_object* v_post_2899_, lean_object* v_usedLetOnly_2900_, lean_object* v_skipConstInApp_2901_, lean_object* v_skipInstances_2902_, lean_object* v_fvars_2903_, lean_object* v_e_2904_, lean_object* v_a_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_){
_start:
{
uint8_t v_usedLetOnly_boxed_2913_; uint8_t v_skipConstInApp_boxed_2914_; uint8_t v_skipInstances_boxed_2915_; lean_object* v_res_2916_; 
v_usedLetOnly_boxed_2913_ = lean_unbox(v_usedLetOnly_2900_);
v_skipConstInApp_boxed_2914_ = lean_unbox(v_skipConstInApp_2901_);
v_skipInstances_boxed_2915_ = lean_unbox(v_skipInstances_2902_);
v_res_2916_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6(v_pre_2898_, v_post_2899_, v_usedLetOnly_boxed_2913_, v_skipConstInApp_boxed_2914_, v_skipInstances_boxed_2915_, v_fvars_2903_, v_e_2904_, v_a_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
lean_dec(v___y_2909_);
lean_dec_ref(v___y_2908_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v_a_2905_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7___boxed(lean_object* v_pre_2917_, lean_object* v_post_2918_, lean_object* v_usedLetOnly_2919_, lean_object* v_skipConstInApp_2920_, lean_object* v_skipInstances_2921_, lean_object* v_fvars_2922_, lean_object* v_e_2923_, lean_object* v_a_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_){
_start:
{
uint8_t v_usedLetOnly_boxed_2932_; uint8_t v_skipConstInApp_boxed_2933_; uint8_t v_skipInstances_boxed_2934_; lean_object* v_res_2935_; 
v_usedLetOnly_boxed_2932_ = lean_unbox(v_usedLetOnly_2919_);
v_skipConstInApp_boxed_2933_ = lean_unbox(v_skipConstInApp_2920_);
v_skipInstances_boxed_2934_ = lean_unbox(v_skipInstances_2921_);
v_res_2935_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7(v_pre_2917_, v_post_2918_, v_usedLetOnly_boxed_2932_, v_skipConstInApp_boxed_2933_, v_skipInstances_boxed_2934_, v_fvars_2922_, v_e_2923_, v_a_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_);
lean_dec(v___y_2930_);
lean_dec_ref(v___y_2929_);
lean_dec(v___y_2928_);
lean_dec_ref(v___y_2927_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v_a_2924_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8___boxed(lean_object* v_pre_2936_, lean_object* v_post_2937_, lean_object* v_usedLetOnly_2938_, lean_object* v_skipConstInApp_2939_, lean_object* v_skipInstances_2940_, lean_object* v_fvars_2941_, lean_object* v_e_2942_, lean_object* v_a_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
uint8_t v_usedLetOnly_boxed_2951_; uint8_t v_skipConstInApp_boxed_2952_; uint8_t v_skipInstances_boxed_2953_; lean_object* v_res_2954_; 
v_usedLetOnly_boxed_2951_ = lean_unbox(v_usedLetOnly_2938_);
v_skipConstInApp_boxed_2952_ = lean_unbox(v_skipConstInApp_2939_);
v_skipInstances_boxed_2953_ = lean_unbox(v_skipInstances_2940_);
v_res_2954_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8(v_pre_2936_, v_post_2937_, v_usedLetOnly_boxed_2951_, v_skipConstInApp_boxed_2952_, v_skipInstances_boxed_2953_, v_fvars_2941_, v_e_2942_, v_a_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v_a_2943_);
return v_res_2954_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_2955_ = _args[0];
lean_object* v___x_2956_ = _args[1];
lean_object* v_pre_2957_ = _args[2];
lean_object* v_post_2958_ = _args[3];
lean_object* v_usedLetOnly_2959_ = _args[4];
lean_object* v_skipConstInApp_2960_ = _args[5];
lean_object* v_skipInstances_2961_ = _args[6];
lean_object* v_a_2962_ = _args[7];
lean_object* v_b_2963_ = _args[8];
lean_object* v___y_2964_ = _args[9];
lean_object* v___y_2965_ = _args[10];
lean_object* v___y_2966_ = _args[11];
lean_object* v___y_2967_ = _args[12];
lean_object* v___y_2968_ = _args[13];
lean_object* v___y_2969_ = _args[14];
lean_object* v___y_2970_ = _args[15];
lean_object* v___y_2971_ = _args[16];
_start:
{
uint8_t v_usedLetOnly_boxed_2972_; uint8_t v_skipConstInApp_boxed_2973_; uint8_t v_skipInstances_boxed_2974_; lean_object* v_res_2975_; 
v_usedLetOnly_boxed_2972_ = lean_unbox(v_usedLetOnly_2959_);
v_skipConstInApp_boxed_2973_ = lean_unbox(v_skipConstInApp_2960_);
v_skipInstances_boxed_2974_ = lean_unbox(v_skipInstances_2961_);
v_res_2975_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg(v_upperBound_2955_, v___x_2956_, v_pre_2957_, v_post_2958_, v_usedLetOnly_boxed_2972_, v_skipConstInApp_boxed_2973_, v_skipInstances_boxed_2974_, v_a_2962_, v_b_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v___y_2964_);
lean_dec_ref(v___x_2956_);
lean_dec(v_upperBound_2955_);
return v_res_2975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__9___boxed(lean_object* v_skipInstances_2976_, lean_object* v_pre_2977_, lean_object* v_post_2978_, lean_object* v_usedLetOnly_2979_, lean_object* v_skipConstInApp_2980_, lean_object* v_x_2981_, lean_object* v_x_2982_, lean_object* v_x_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_){
_start:
{
uint8_t v_skipInstances_boxed_2992_; uint8_t v_usedLetOnly_boxed_2993_; uint8_t v_skipConstInApp_boxed_2994_; lean_object* v_res_2995_; 
v_skipInstances_boxed_2992_ = lean_unbox(v_skipInstances_2976_);
v_usedLetOnly_boxed_2993_ = lean_unbox(v_usedLetOnly_2979_);
v_skipConstInApp_boxed_2994_ = lean_unbox(v_skipConstInApp_2980_);
v_res_2995_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__9(v_skipInstances_boxed_2992_, v_pre_2977_, v_post_2978_, v_usedLetOnly_boxed_2993_, v_skipConstInApp_boxed_2994_, v_x_2981_, v_x_2982_, v_x_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_);
lean_dec(v___y_2990_);
lean_dec_ref(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec_ref(v___y_2985_);
lean_dec(v___y_2984_);
return v_res_2995_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2996_ = lean_box(0);
v___x_2997_ = lean_unsigned_to_nat(16u);
v___x_2998_ = lean_mk_array(v___x_2997_, v___x_2996_);
return v___x_2998_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_2999_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__0);
v___x_3000_ = lean_unsigned_to_nat(0u);
v___x_3001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3001_, 0, v___x_3000_);
lean_ctor_set(v___x_3001_, 1, v___x_2999_);
return v___x_3001_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__2(void){
_start:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; 
v___x_3002_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__1, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__1);
v___x_3003_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3003_, 0, lean_box(0));
lean_closure_set(v___x_3003_, 1, lean_box(0));
lean_closure_set(v___x_3003_, 2, v___x_3002_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1(lean_object* v_input_3004_, lean_object* v_pre_3005_, lean_object* v_post_3006_, uint8_t v_usedLetOnly_3007_, uint8_t v_skipConstInApp_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_){
_start:
{
uint8_t v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v_a_3019_; lean_object* v___x_3020_; 
v___x_3016_ = 0;
v___x_3017_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__2, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__2);
v___x_3018_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___lam__0(lean_box(0), v___x_3017_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_);
v_a_3019_ = lean_ctor_get(v___x_3018_, 0);
lean_inc(v_a_3019_);
lean_dec_ref(v___x_3018_);
v___x_3020_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_3005_, v_post_3006_, v_usedLetOnly_3007_, v_skipConstInApp_3008_, v___x_3016_, v_input_3004_, v_a_3019_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_);
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_object* v_a_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3030_; 
v_a_3021_ = lean_ctor_get(v___x_3020_, 0);
lean_inc(v_a_3021_);
lean_dec_ref_known(v___x_3020_, 1);
v___x_3022_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3022_, 0, lean_box(0));
lean_closure_set(v___x_3022_, 1, lean_box(0));
lean_closure_set(v___x_3022_, 2, v_a_3019_);
v___x_3023_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___lam__0(lean_box(0), v___x_3022_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3030_ == 0)
{
lean_object* v_unused_3031_; 
v_unused_3031_ = lean_ctor_get(v___x_3023_, 0);
lean_dec(v_unused_3031_);
v___x_3025_ = v___x_3023_;
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
else
{
lean_dec(v___x_3023_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3028_; 
if (v_isShared_3026_ == 0)
{
lean_ctor_set(v___x_3025_, 0, v_a_3021_);
v___x_3028_ = v___x_3025_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3021_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
else
{
lean_dec(v_a_3019_);
return v___x_3020_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___boxed(lean_object* v_input_3032_, lean_object* v_pre_3033_, lean_object* v_post_3034_, lean_object* v_usedLetOnly_3035_, lean_object* v_skipConstInApp_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_){
_start:
{
uint8_t v_usedLetOnly_boxed_3044_; uint8_t v_skipConstInApp_boxed_3045_; lean_object* v_res_3046_; 
v_usedLetOnly_boxed_3044_ = lean_unbox(v_usedLetOnly_3035_);
v_skipConstInApp_boxed_3045_ = lean_unbox(v_skipConstInApp_3036_);
v_res_3046_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1(v_input_3032_, v_pre_3033_, v_post_3034_, v_usedLetOnly_boxed_3044_, v_skipConstInApp_boxed_3045_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_);
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3041_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
return v_res_3046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts(lean_object* v_stx_3077_, lean_object* v_expectedType_x3f_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_){
_start:
{
lean_object* v___f_3086_; lean_object* v___f_3087_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___x_3119_; 
v___f_3086_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__0));
v___f_3087_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__1));
lean_inc(v_expectedType_x3f_3078_);
v___x_3119_ = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(v_expectedType_x3f_3078_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_);
if (lean_obj_tag(v___x_3119_) == 0)
{
lean_dec_ref_known(v___x_3119_, 1);
if (lean_obj_tag(v_expectedType_x3f_3078_) == 1)
{
lean_object* v_val_3120_; lean_object* v___x_3121_; lean_object* v_a_3122_; uint8_t v___x_3123_; 
v_val_3120_ = lean_ctor_get(v_expectedType_x3f_3078_, 0);
lean_inc(v_val_3120_);
v___x_3121_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0___redArg(v_val_3120_, v_a_3082_);
v_a_3122_ = lean_ctor_get(v___x_3121_, 0);
lean_inc(v_a_3122_);
lean_dec_ref(v___x_3121_);
v___x_3123_ = l_Lean_Expr_hasExprMVar(v_a_3122_);
lean_dec(v_a_3122_);
if (v___x_3123_ == 0)
{
v___y_3089_ = v_a_3079_;
v___y_3090_ = v_a_3080_;
v___y_3091_ = v_a_3081_;
v___y_3092_ = v_a_3082_;
v___y_3093_ = v_a_3083_;
v___y_3094_ = v_a_3084_;
goto v___jp_3088_;
}
else
{
lean_object* v___x_3124_; 
v___x_3124_ = l_Lean_Elab_Term_tryPostpone(v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_);
if (lean_obj_tag(v___x_3124_) == 0)
{
lean_dec_ref_known(v___x_3124_, 1);
v___y_3089_ = v_a_3079_;
v___y_3090_ = v_a_3080_;
v___y_3091_ = v_a_3081_;
v___y_3092_ = v_a_3082_;
v___y_3093_ = v_a_3083_;
v___y_3094_ = v_a_3084_;
goto v___jp_3088_;
}
else
{
lean_object* v_a_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3132_; 
lean_dec_ref_known(v_expectedType_x3f_3078_, 1);
v_a_3125_ = lean_ctor_get(v___x_3124_, 0);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3124_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3127_ = v___x_3124_;
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_a_3125_);
lean_dec(v___x_3124_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___x_3130_; 
if (v_isShared_3128_ == 0)
{
v___x_3130_ = v___x_3127_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_a_3125_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
}
}
}
}
}
else
{
v___y_3089_ = v_a_3079_;
v___y_3090_ = v_a_3080_;
v___y_3091_ = v_a_3081_;
v___y_3092_ = v_a_3082_;
v___y_3093_ = v_a_3083_;
v___y_3094_ = v_a_3084_;
goto v___jp_3088_;
}
}
else
{
lean_object* v_a_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3140_; 
lean_dec(v_expectedType_x3f_3078_);
v_a_3133_ = lean_ctor_get(v___x_3119_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3135_ = v___x_3119_;
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_a_3133_);
lean_dec(v___x_3119_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3138_; 
if (v_isShared_3136_ == 0)
{
v___x_3138_ = v___x_3135_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_a_3133_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
v___jp_3088_:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; uint8_t v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; uint8_t v___x_3101_; lean_object* v___x_3102_; 
v___x_3095_ = lean_unsigned_to_nat(1u);
v___x_3096_ = l_Lean_Syntax_getArg(v_stx_3077_, v___x_3095_);
v___x_3097_ = 1;
v___x_3098_ = lean_box(v___x_3097_);
v___x_3099_ = lean_box(v___x_3097_);
v___x_3100_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(v___x_3100_, 0, v___x_3096_);
lean_closure_set(v___x_3100_, 1, v_expectedType_x3f_3078_);
lean_closure_set(v___x_3100_, 2, v___x_3098_);
lean_closure_set(v___x_3100_, 3, v___x_3099_);
v___x_3101_ = 1;
v___x_3102_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_3100_, v___x_3101_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_);
if (lean_obj_tag(v___x_3102_) == 0)
{
lean_object* v_a_3103_; lean_object* v___x_3104_; lean_object* v_a_3105_; uint8_t v___x_3106_; lean_object* v___x_3107_; 
v_a_3103_ = lean_ctor_get(v___x_3102_, 0);
lean_inc(v_a_3103_);
lean_dec_ref_known(v___x_3102_, 1);
v___x_3104_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0___redArg(v_a_3103_, v___y_3092_);
v_a_3105_ = lean_ctor_get(v___x_3104_, 0);
lean_inc_n(v_a_3105_, 2);
lean_dec_ref(v___x_3104_);
v___x_3106_ = 0;
v___x_3107_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1(v_a_3105_, v___f_3087_, v___f_3086_, v___x_3106_, v___x_3106_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_);
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3118_; 
v_a_3108_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3118_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3110_ = v___x_3107_;
v_isShared_3111_ = v_isSharedCheck_3118_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_3107_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3118_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
uint8_t v___x_3112_; 
v___x_3112_ = lean_expr_eqv(v_a_3108_, v_a_3105_);
if (v___x_3112_ == 0)
{
lean_object* v___x_3113_; lean_object* v___x_3114_; 
lean_del_object(v___x_3110_);
lean_dec(v_a_3105_);
v___x_3113_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__10));
v___x_3114_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith(v___x_3113_, v_a_3108_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_);
return v___x_3114_;
}
else
{
lean_object* v___x_3116_; 
lean_dec(v_a_3108_);
if (v_isShared_3111_ == 0)
{
lean_ctor_set(v___x_3110_, 0, v_a_3105_);
v___x_3116_ = v___x_3110_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v_a_3105_);
v___x_3116_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
return v___x_3116_;
}
}
}
}
else
{
lean_dec(v_a_3105_);
return v___x_3107_;
}
}
else
{
return v___x_3102_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts___boxed(lean_object* v_stx_3141_, lean_object* v_expectedType_x3f_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_){
_start:
{
lean_object* v_res_3150_; 
v_res_3150_ = l_Lean_Elab_Tactic_Do_elabContractEPosts(v_stx_3141_, v_expectedType_x3f_3142_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_);
lean_dec(v_a_3148_);
lean_dec_ref(v_a_3147_);
lean_dec(v_a_3146_);
lean_dec_ref(v_a_3145_);
lean_dec(v_a_3144_);
lean_dec_ref(v_a_3143_);
lean_dec(v_stx_3141_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4(lean_object* v_upperBound_3151_, lean_object* v___x_3152_, lean_object* v_pre_3153_, lean_object* v_post_3154_, uint8_t v_usedLetOnly_3155_, uint8_t v_skipConstInApp_3156_, uint8_t v_skipInstances_3157_, lean_object* v___x_3158_, lean_object* v_inst_3159_, lean_object* v_R_3160_, lean_object* v_a_3161_, lean_object* v_b_3162_, lean_object* v_c_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
lean_object* v___x_3172_; 
v___x_3172_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg(v_upperBound_3151_, v___x_3152_, v_pre_3153_, v_post_3154_, v_usedLetOnly_3155_, v_skipConstInApp_3156_, v_skipInstances_3157_, v_a_3161_, v_b_3162_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_3173_ = _args[0];
lean_object* v___x_3174_ = _args[1];
lean_object* v_pre_3175_ = _args[2];
lean_object* v_post_3176_ = _args[3];
lean_object* v_usedLetOnly_3177_ = _args[4];
lean_object* v_skipConstInApp_3178_ = _args[5];
lean_object* v_skipInstances_3179_ = _args[6];
lean_object* v___x_3180_ = _args[7];
lean_object* v_inst_3181_ = _args[8];
lean_object* v_R_3182_ = _args[9];
lean_object* v_a_3183_ = _args[10];
lean_object* v_b_3184_ = _args[11];
lean_object* v_c_3185_ = _args[12];
lean_object* v___y_3186_ = _args[13];
lean_object* v___y_3187_ = _args[14];
lean_object* v___y_3188_ = _args[15];
lean_object* v___y_3189_ = _args[16];
lean_object* v___y_3190_ = _args[17];
lean_object* v___y_3191_ = _args[18];
lean_object* v___y_3192_ = _args[19];
lean_object* v___y_3193_ = _args[20];
_start:
{
uint8_t v_usedLetOnly_boxed_3194_; uint8_t v_skipConstInApp_boxed_3195_; uint8_t v_skipInstances_boxed_3196_; lean_object* v_res_3197_; 
v_usedLetOnly_boxed_3194_ = lean_unbox(v_usedLetOnly_3177_);
v_skipConstInApp_boxed_3195_ = lean_unbox(v_skipConstInApp_3178_);
v_skipInstances_boxed_3196_ = lean_unbox(v_skipInstances_3179_);
v_res_3197_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4(v_upperBound_3173_, v___x_3174_, v_pre_3175_, v_post_3176_, v_usedLetOnly_boxed_3194_, v_skipConstInApp_boxed_3195_, v_skipInstances_boxed_3196_, v___x_3180_, v_inst_3181_, v_R_3182_, v_a_3183_, v_b_3184_, v_c_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3191_);
lean_dec(v___y_3190_);
lean_dec_ref(v___y_3189_);
lean_dec(v___y_3188_);
lean_dec_ref(v___y_3187_);
lean_dec(v___y_3186_);
lean_dec(v___x_3180_);
lean_dec_ref(v___x_3174_);
lean_dec(v_upperBound_3173_);
return v_res_3197_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5(lean_object* v_00_u03b2_3198_, lean_object* v_m_3199_, lean_object* v_a_3200_){
_start:
{
lean_object* v___x_3201_; 
v___x_3201_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5___redArg(v_m_3199_, v_a_3200_);
return v___x_3201_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5___boxed(lean_object* v_00_u03b2_3202_, lean_object* v_m_3203_, lean_object* v_a_3204_){
_start:
{
lean_object* v_res_3205_; 
v_res_3205_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5(v_00_u03b2_3202_, v_m_3203_, v_a_3204_);
lean_dec_ref(v_a_3204_);
lean_dec_ref(v_m_3203_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8(lean_object* v_00_u03b1_3206_, lean_object* v_name_3207_, uint8_t v_bi_3208_, lean_object* v_type_3209_, lean_object* v_k_3210_, uint8_t v_kind_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_){
_start:
{
lean_object* v___x_3220_; 
v___x_3220_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg(v_name_3207_, v_bi_3208_, v_type_3209_, v_k_3210_, v_kind_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
return v___x_3220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___boxed(lean_object* v_00_u03b1_3221_, lean_object* v_name_3222_, lean_object* v_bi_3223_, lean_object* v_type_3224_, lean_object* v_k_3225_, lean_object* v_kind_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_){
_start:
{
uint8_t v_bi_boxed_3235_; uint8_t v_kind_boxed_3236_; lean_object* v_res_3237_; 
v_bi_boxed_3235_ = lean_unbox(v_bi_3223_);
v_kind_boxed_3236_ = lean_unbox(v_kind_3226_);
v_res_3237_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8(v_00_u03b1_3221_, v_name_3222_, v_bi_boxed_3235_, v_type_3224_, v_k_3225_, v_kind_boxed_3236_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_);
lean_dec(v___y_3233_);
lean_dec_ref(v___y_3232_);
lean_dec(v___y_3231_);
lean_dec_ref(v___y_3230_);
lean_dec(v___y_3229_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3227_);
return v_res_3237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11(lean_object* v_00_u03b1_3238_, lean_object* v_name_3239_, lean_object* v_type_3240_, lean_object* v_val_3241_, lean_object* v_k_3242_, uint8_t v_nondep_3243_, uint8_t v_kind_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_){
_start:
{
lean_object* v___x_3253_; 
v___x_3253_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11___redArg(v_name_3239_, v_type_3240_, v_val_3241_, v_k_3242_, v_nondep_3243_, v_kind_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
return v___x_3253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11___boxed(lean_object* v_00_u03b1_3254_, lean_object* v_name_3255_, lean_object* v_type_3256_, lean_object* v_val_3257_, lean_object* v_k_3258_, lean_object* v_nondep_3259_, lean_object* v_kind_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_){
_start:
{
uint8_t v_nondep_boxed_3269_; uint8_t v_kind_boxed_3270_; lean_object* v_res_3271_; 
v_nondep_boxed_3269_ = lean_unbox(v_nondep_3259_);
v_kind_boxed_3270_ = lean_unbox(v_kind_3260_);
v_res_3271_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11(v_00_u03b1_3254_, v_name_3255_, v_type_3256_, v_val_3257_, v_k_3258_, v_nondep_boxed_3269_, v_kind_boxed_3270_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_);
lean_dec(v___y_3267_);
lean_dec_ref(v___y_3266_);
lean_dec(v___y_3265_);
lean_dec_ref(v___y_3264_);
lean_dec(v___y_3263_);
lean_dec_ref(v___y_3262_);
lean_dec(v___y_3261_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14(lean_object* v_00_u03b1_3272_, lean_object* v_ref_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_){
_start:
{
lean_object* v___x_3279_; 
v___x_3279_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_3273_);
return v___x_3279_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___boxed(lean_object* v_00_u03b1_3280_, lean_object* v_ref_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_){
_start:
{
lean_object* v_res_3287_; 
v_res_3287_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14(v_00_u03b1_3280_, v_ref_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_);
lean_dec(v___y_3285_);
lean_dec_ref(v___y_3284_);
lean_dec(v___y_3283_);
lean_dec_ref(v___y_3282_);
return v_res_3287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10(lean_object* v_00_u03b1_3288_, lean_object* v_x_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_){
_start:
{
lean_object* v___x_3298_; 
v___x_3298_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10___redArg(v_x_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_);
return v___x_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10___boxed(lean_object* v_00_u03b1_3299_, lean_object* v_x_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_){
_start:
{
lean_object* v_res_3309_; 
v_res_3309_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10(v_00_u03b1_3299_, v_x_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_);
lean_dec(v___y_3307_);
lean_dec_ref(v___y_3306_);
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec(v___y_3301_);
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11(lean_object* v_00_u03b2_3310_, lean_object* v_m_3311_, lean_object* v_a_3312_, lean_object* v_b_3313_){
_start:
{
lean_object* v___x_3314_; 
v___x_3314_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11___redArg(v_m_3311_, v_a_3312_, v_b_3313_);
return v___x_3314_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5_spec__6(lean_object* v_00_u03b2_3315_, lean_object* v_a_3316_, lean_object* v_x_3317_){
_start:
{
lean_object* v___x_3318_; 
v___x_3318_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5_spec__6___redArg(v_a_3316_, v_x_3317_);
return v___x_3318_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5_spec__6___boxed(lean_object* v_00_u03b2_3319_, lean_object* v_a_3320_, lean_object* v_x_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5_spec__6(v_00_u03b2_3319_, v_a_3320_, v_x_3321_);
lean_dec(v_x_3321_);
lean_dec_ref(v_a_3320_);
return v_res_3322_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16(lean_object* v_00_u03b2_3323_, lean_object* v_a_3324_, lean_object* v_x_3325_){
_start:
{
uint8_t v___x_3326_; 
v___x_3326_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16___redArg(v_a_3324_, v_x_3325_);
return v___x_3326_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16___boxed(lean_object* v_00_u03b2_3327_, lean_object* v_a_3328_, lean_object* v_x_3329_){
_start:
{
uint8_t v_res_3330_; lean_object* v_r_3331_; 
v_res_3330_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16(v_00_u03b2_3327_, v_a_3328_, v_x_3329_);
lean_dec(v_x_3329_);
lean_dec_ref(v_a_3328_);
v_r_3331_ = lean_box(v_res_3330_);
return v_r_3331_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17(lean_object* v_00_u03b2_3332_, lean_object* v_data_3333_){
_start:
{
lean_object* v___x_3334_; 
v___x_3334_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17___redArg(v_data_3333_);
return v___x_3334_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__18(lean_object* v_00_u03b2_3335_, lean_object* v_a_3336_, lean_object* v_b_3337_, lean_object* v_x_3338_){
_start:
{
lean_object* v___x_3339_; 
v___x_3339_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__18___redArg(v_a_3336_, v_b_3337_, v_x_3338_);
return v___x_3339_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17_spec__18(lean_object* v_00_u03b2_3340_, lean_object* v_i_3341_, lean_object* v_source_3342_, lean_object* v_target_3343_){
_start:
{
lean_object* v___x_3344_; 
v___x_3344_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v_i_3341_, v_source_3342_, v_target_3343_);
return v___x_3344_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19(lean_object* v_00_u03b2_3345_, lean_object* v_x_3346_, lean_object* v_x_3347_){
_start:
{
lean_object* v___x_3348_; 
v___x_3348_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_x_3346_, v_x_3347_);
return v___x_3348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1(){
_start:
{
lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; 
v___x_3362_ = l_Lean_Elab_Term_termElabAttribute;
v___x_3363_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___closed__0));
v___x_3364_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___closed__2));
v___x_3365_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elabContractEPosts___boxed), 9, 0);
v___x_3366_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3362_, v___x_3363_, v___x_3364_, v___x_3365_);
return v___x_3366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___boxed(lean_object* v_a_3367_){
_start:
{
lean_object* v_res_3368_; 
v_res_3368_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1();
return v_res_3368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts_docString__3(){
_start:
{
lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; 
v___x_3371_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___closed__2));
v___x_3372_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts_docString__3___closed__0));
v___x_3373_ = l_Lean_addBuiltinDocString(v___x_3371_, v___x_3372_);
return v___x_3373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts_docString__3___boxed(lean_object* v_a_3374_){
_start:
{
lean_object* v_res_3375_; 
v_res_3375_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts_docString__3();
return v_res_3375_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0(uint8_t v_suppressElabErrors_3377_, lean_object* v_x_3378_){
_start:
{
if (lean_obj_tag(v_x_3378_) == 1)
{
lean_object* v_pre_3379_; 
v_pre_3379_ = lean_ctor_get(v_x_3378_, 0);
if (lean_obj_tag(v_pre_3379_) == 0)
{
lean_object* v_str_3380_; lean_object* v___x_3381_; uint8_t v___x_3382_; 
v_str_3380_ = lean_ctor_get(v_x_3378_, 1);
v___x_3381_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0___closed__0));
v___x_3382_ = lean_string_dec_eq(v_str_3380_, v___x_3381_);
if (v___x_3382_ == 0)
{
return v___x_3382_;
}
else
{
return v_suppressElabErrors_3377_;
}
}
else
{
uint8_t v___x_3383_; 
v___x_3383_ = 0;
return v___x_3383_;
}
}
else
{
uint8_t v___x_3384_; 
v___x_3384_ = 0;
return v___x_3384_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0___boxed(lean_object* v_suppressElabErrors_3385_, lean_object* v_x_3386_){
_start:
{
uint8_t v_suppressElabErrors_boxed_3387_; uint8_t v_res_3388_; lean_object* v_r_3389_; 
v_suppressElabErrors_boxed_3387_ = lean_unbox(v_suppressElabErrors_3385_);
v_res_3388_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0(v_suppressElabErrors_boxed_3387_, v_x_3386_);
lean_dec(v_x_3386_);
v_r_3389_ = lean_box(v_res_3388_);
return v_r_3389_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0(lean_object* v_opts_3390_, lean_object* v_opt_3391_){
_start:
{
lean_object* v_name_3392_; lean_object* v_defValue_3393_; lean_object* v_map_3394_; lean_object* v___x_3395_; 
v_name_3392_ = lean_ctor_get(v_opt_3391_, 0);
v_defValue_3393_ = lean_ctor_get(v_opt_3391_, 1);
v_map_3394_ = lean_ctor_get(v_opts_3390_, 0);
v___x_3395_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3394_, v_name_3392_);
if (lean_obj_tag(v___x_3395_) == 0)
{
uint8_t v___x_3396_; 
v___x_3396_ = lean_unbox(v_defValue_3393_);
return v___x_3396_;
}
else
{
lean_object* v_val_3397_; 
v_val_3397_ = lean_ctor_get(v___x_3395_, 0);
lean_inc(v_val_3397_);
lean_dec_ref_known(v___x_3395_, 1);
if (lean_obj_tag(v_val_3397_) == 1)
{
uint8_t v_v_3398_; 
v_v_3398_ = lean_ctor_get_uint8(v_val_3397_, 0);
lean_dec_ref_known(v_val_3397_, 0);
return v_v_3398_;
}
else
{
uint8_t v___x_3399_; 
lean_dec(v_val_3397_);
v___x_3399_ = lean_unbox(v_defValue_3393_);
return v___x_3399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0___boxed(lean_object* v_opts_3400_, lean_object* v_opt_3401_){
_start:
{
uint8_t v_res_3402_; lean_object* v_r_3403_; 
v_res_3402_ = l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0(v_opts_3400_, v_opt_3401_);
lean_dec_ref(v_opt_3401_);
lean_dec_ref(v_opts_3400_);
v_r_3403_ = lean_box(v_res_3402_);
return v_r_3403_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3404_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0);
v___x_3405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3404_);
return v___x_3405_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; 
v___x_3406_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__0);
v___x_3407_ = lean_unsigned_to_nat(0u);
v___x_3408_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3408_, 0, v___x_3407_);
lean_ctor_set(v___x_3408_, 1, v___x_3407_);
lean_ctor_set(v___x_3408_, 2, v___x_3407_);
lean_ctor_set(v___x_3408_, 3, v___x_3407_);
lean_ctor_set(v___x_3408_, 4, v___x_3406_);
lean_ctor_set(v___x_3408_, 5, v___x_3406_);
lean_ctor_set(v___x_3408_, 6, v___x_3406_);
lean_ctor_set(v___x_3408_, 7, v___x_3406_);
lean_ctor_set(v___x_3408_, 8, v___x_3406_);
lean_ctor_set(v___x_3408_, 9, v___x_3406_);
lean_ctor_set(v___x_3408_, 10, v___x_3406_);
return v___x_3408_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; 
v___x_3409_ = lean_unsigned_to_nat(32u);
v___x_3410_ = lean_mk_empty_array_with_capacity(v___x_3409_);
v___x_3411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3411_, 0, v___x_3410_);
return v___x_3411_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__3(void){
_start:
{
size_t v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___x_3412_ = ((size_t)5ULL);
v___x_3413_ = lean_unsigned_to_nat(0u);
v___x_3414_ = lean_unsigned_to_nat(32u);
v___x_3415_ = lean_mk_empty_array_with_capacity(v___x_3414_);
v___x_3416_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__2);
v___x_3417_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3417_, 0, v___x_3416_);
lean_ctor_set(v___x_3417_, 1, v___x_3415_);
lean_ctor_set(v___x_3417_, 2, v___x_3413_);
lean_ctor_set(v___x_3417_, 3, v___x_3413_);
lean_ctor_set_usize(v___x_3417_, 4, v___x_3412_);
return v___x_3417_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__4(void){
_start:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; 
v___x_3418_ = lean_box(1);
v___x_3419_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__3);
v___x_3420_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__0);
v___x_3421_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3420_);
lean_ctor_set(v___x_3421_, 1, v___x_3419_);
lean_ctor_set(v___x_3421_, 2, v___x_3418_);
return v___x_3421_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_msgData_3422_, lean_object* v___y_3423_){
_start:
{
lean_object* v___x_3425_; lean_object* v_env_3426_; uint8_t v___x_3427_; lean_object* v_env_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v_scopes_3431_; lean_object* v___x_3432_; lean_object* v_opts_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3425_ = lean_st_ref_get(v___y_3423_);
v_env_3426_ = lean_ctor_get(v___x_3425_, 0);
lean_inc_ref(v_env_3426_);
lean_dec(v___x_3425_);
v___x_3427_ = 0;
v_env_3428_ = l_Lean_Environment_setRecordingDeps(v_env_3426_, v___x_3427_);
v___x_3429_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3430_ = lean_st_ref_get(v___y_3423_);
v_scopes_3431_ = lean_ctor_get(v___x_3430_, 2);
lean_inc(v_scopes_3431_);
lean_dec(v___x_3430_);
v___x_3432_ = l_List_head_x21___redArg(v___x_3429_, v_scopes_3431_);
lean_dec(v_scopes_3431_);
v_opts_3433_ = lean_ctor_get(v___x_3432_, 1);
lean_inc_ref(v_opts_3433_);
lean_dec(v___x_3432_);
v___x_3434_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__1);
v___x_3435_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__4);
v___x_3436_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3436_, 0, v_env_3428_);
lean_ctor_set(v___x_3436_, 1, v___x_3434_);
lean_ctor_set(v___x_3436_, 2, v___x_3435_);
lean_ctor_set(v___x_3436_, 3, v_opts_3433_);
v___x_3437_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3436_);
lean_ctor_set(v___x_3437_, 1, v_msgData_3422_);
v___x_3438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3437_);
return v___x_3438_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_msgData_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_){
_start:
{
lean_object* v_res_3442_; 
v_res_3442_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg(v_msgData_3439_, v___y_3440_);
lean_dec(v___y_3440_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2(lean_object* v_ref_3443_, lean_object* v_msgData_3444_, uint8_t v_severity_3445_, uint8_t v_isSilent_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_){
_start:
{
lean_object* v___y_3451_; lean_object* v___y_3452_; uint8_t v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; uint8_t v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3516_; uint8_t v___y_3517_; uint8_t v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3542_; uint8_t v___y_3543_; uint8_t v___y_3544_; lean_object* v___y_3545_; uint8_t v___y_3549_; uint8_t v___y_3550_; uint8_t v___x_3565_; uint8_t v___y_3567_; uint8_t v___x_3577_; 
v___x_3565_ = 2;
v___x_3577_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3445_, v___x_3565_);
if (v___x_3577_ == 0)
{
v___y_3567_ = v___x_3577_;
goto v___jp_3566_;
}
else
{
uint8_t v___x_3578_; 
lean_inc_ref(v_msgData_3444_);
v___x_3578_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3444_);
if (v___x_3578_ == 0)
{
v___y_3567_ = v___x_3578_;
goto v___jp_3566_;
}
else
{
lean_object* v___x_3579_; lean_object* v___x_3580_; 
lean_dec_ref(v_msgData_3444_);
v___x_3579_ = lean_box(0);
v___x_3580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3580_, 0, v___x_3579_);
return v___x_3580_;
}
}
v___jp_3450_:
{
lean_object* v___x_3459_; 
v___x_3459_ = l_Lean_Elab_Command_getScope___redArg(v___y_3458_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_a_3460_; lean_object* v_currNamespace_3461_; lean_object* v___x_3462_; 
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_a_3460_);
lean_dec_ref_known(v___x_3459_, 1);
v_currNamespace_3461_ = lean_ctor_get(v_a_3460_, 2);
lean_inc(v_currNamespace_3461_);
lean_dec(v_a_3460_);
v___x_3462_ = l_Lean_Elab_Command_getScope___redArg(v___y_3458_);
if (lean_obj_tag(v___x_3462_) == 0)
{
lean_object* v_a_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3498_; 
v_a_3463_ = lean_ctor_get(v___x_3462_, 0);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3465_ = v___x_3462_;
v_isShared_3466_ = v_isSharedCheck_3498_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___x_3462_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3498_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v_openDecls_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v_env_3472_; lean_object* v_messages_3473_; lean_object* v_scopes_3474_; lean_object* v_usedQuotCtxts_3475_; lean_object* v_nextMacroScope_3476_; lean_object* v_maxRecDepth_3477_; lean_object* v_ngen_3478_; lean_object* v_auxDeclNGen_3479_; lean_object* v_infoState_3480_; lean_object* v_traceState_3481_; lean_object* v_snapshotTasks_3482_; lean_object* v_prevLinterStates_3483_; lean_object* v_codeQualityEntryTasks_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3497_; 
v_openDecls_3467_ = lean_ctor_get(v_a_3463_, 3);
lean_inc(v_openDecls_3467_);
lean_dec(v_a_3463_);
v___x_3468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3468_, 0, v_currNamespace_3461_);
lean_ctor_set(v___x_3468_, 1, v_openDecls_3467_);
v___x_3469_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3468_);
lean_ctor_set(v___x_3469_, 1, v___y_3454_);
lean_inc_ref(v___y_3455_);
lean_inc_ref(v___y_3452_);
v___x_3470_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3470_, 0, v___y_3452_);
lean_ctor_set(v___x_3470_, 1, v___y_3456_);
lean_ctor_set(v___x_3470_, 2, v___y_3451_);
lean_ctor_set(v___x_3470_, 3, v___y_3455_);
lean_ctor_set(v___x_3470_, 4, v___x_3469_);
lean_ctor_set_uint8(v___x_3470_, sizeof(void*)*5, v___y_3453_);
lean_ctor_set_uint8(v___x_3470_, sizeof(void*)*5 + 1, v___y_3457_);
lean_ctor_set_uint8(v___x_3470_, sizeof(void*)*5 + 2, v_isSilent_3446_);
v___x_3471_ = lean_st_ref_take(v___y_3458_);
v_env_3472_ = lean_ctor_get(v___x_3471_, 0);
v_messages_3473_ = lean_ctor_get(v___x_3471_, 1);
v_scopes_3474_ = lean_ctor_get(v___x_3471_, 2);
v_usedQuotCtxts_3475_ = lean_ctor_get(v___x_3471_, 3);
v_nextMacroScope_3476_ = lean_ctor_get(v___x_3471_, 4);
v_maxRecDepth_3477_ = lean_ctor_get(v___x_3471_, 5);
v_ngen_3478_ = lean_ctor_get(v___x_3471_, 6);
v_auxDeclNGen_3479_ = lean_ctor_get(v___x_3471_, 7);
v_infoState_3480_ = lean_ctor_get(v___x_3471_, 8);
v_traceState_3481_ = lean_ctor_get(v___x_3471_, 9);
v_snapshotTasks_3482_ = lean_ctor_get(v___x_3471_, 10);
v_prevLinterStates_3483_ = lean_ctor_get(v___x_3471_, 11);
v_codeQualityEntryTasks_3484_ = lean_ctor_get(v___x_3471_, 12);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3471_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3486_ = v___x_3471_;
v_isShared_3487_ = v_isSharedCheck_3497_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3484_);
lean_inc(v_prevLinterStates_3483_);
lean_inc(v_snapshotTasks_3482_);
lean_inc(v_traceState_3481_);
lean_inc(v_infoState_3480_);
lean_inc(v_auxDeclNGen_3479_);
lean_inc(v_ngen_3478_);
lean_inc(v_maxRecDepth_3477_);
lean_inc(v_nextMacroScope_3476_);
lean_inc(v_usedQuotCtxts_3475_);
lean_inc(v_scopes_3474_);
lean_inc(v_messages_3473_);
lean_inc(v_env_3472_);
lean_dec(v___x_3471_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3497_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3491_; 
v___x_3488_ = lean_box(0);
v___x_3489_ = l_Lean_MessageLog_add(v___x_3470_, v_messages_3473_);
if (v_isShared_3487_ == 0)
{
lean_ctor_set(v___x_3486_, 1, v___x_3489_);
v___x_3491_ = v___x_3486_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_env_3472_);
lean_ctor_set(v_reuseFailAlloc_3496_, 1, v___x_3489_);
lean_ctor_set(v_reuseFailAlloc_3496_, 2, v_scopes_3474_);
lean_ctor_set(v_reuseFailAlloc_3496_, 3, v_usedQuotCtxts_3475_);
lean_ctor_set(v_reuseFailAlloc_3496_, 4, v_nextMacroScope_3476_);
lean_ctor_set(v_reuseFailAlloc_3496_, 5, v_maxRecDepth_3477_);
lean_ctor_set(v_reuseFailAlloc_3496_, 6, v_ngen_3478_);
lean_ctor_set(v_reuseFailAlloc_3496_, 7, v_auxDeclNGen_3479_);
lean_ctor_set(v_reuseFailAlloc_3496_, 8, v_infoState_3480_);
lean_ctor_set(v_reuseFailAlloc_3496_, 9, v_traceState_3481_);
lean_ctor_set(v_reuseFailAlloc_3496_, 10, v_snapshotTasks_3482_);
lean_ctor_set(v_reuseFailAlloc_3496_, 11, v_prevLinterStates_3483_);
lean_ctor_set(v_reuseFailAlloc_3496_, 12, v_codeQualityEntryTasks_3484_);
v___x_3491_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
lean_object* v___x_3492_; lean_object* v___x_3494_; 
v___x_3492_ = lean_st_ref_put(v___y_3458_, v___x_3491_);
if (v_isShared_3466_ == 0)
{
lean_ctor_set(v___x_3465_, 0, v___x_3488_);
v___x_3494_ = v___x_3465_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v___x_3488_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
}
}
}
}
}
else
{
lean_object* v_a_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3506_; 
lean_dec(v_currNamespace_3461_);
lean_dec_ref(v___y_3456_);
lean_dec_ref(v___y_3454_);
lean_dec(v___y_3451_);
v_a_3499_ = lean_ctor_get(v___x_3462_, 0);
v_isSharedCheck_3506_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3501_ = v___x_3462_;
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_a_3499_);
lean_dec(v___x_3462_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v___x_3504_; 
if (v_isShared_3502_ == 0)
{
v___x_3504_ = v___x_3501_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_a_3499_);
v___x_3504_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
return v___x_3504_;
}
}
}
}
else
{
lean_object* v_a_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3514_; 
lean_dec_ref(v___y_3456_);
lean_dec_ref(v___y_3454_);
lean_dec(v___y_3451_);
v_a_3507_ = lean_ctor_get(v___x_3459_, 0);
v_isSharedCheck_3514_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3514_ == 0)
{
v___x_3509_ = v___x_3459_;
v_isShared_3510_ = v_isSharedCheck_3514_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_a_3507_);
lean_dec(v___x_3459_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3514_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v___x_3512_; 
if (v_isShared_3510_ == 0)
{
v___x_3512_ = v___x_3509_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v_a_3507_);
v___x_3512_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
return v___x_3512_;
}
}
}
}
v___jp_3515_:
{
lean_object* v_fileName_3520_; lean_object* v_fileMap_3521_; uint8_t v_suppressElabErrors_3522_; lean_object* v___x_3523_; lean_object* v___f_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v_a_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3540_; 
v_fileName_3520_ = lean_ctor_get(v___y_3447_, 0);
v_fileMap_3521_ = lean_ctor_get(v___y_3447_, 1);
v_suppressElabErrors_3522_ = lean_ctor_get_uint8(v___y_3447_, sizeof(void*)*10);
v___x_3523_ = lean_box(v_suppressElabErrors_3522_);
v___f_3524_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3524_, 0, v___x_3523_);
v___x_3525_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3444_);
v___x_3526_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg(v___x_3525_, v___y_3448_);
v_a_3527_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3529_ = v___x_3526_;
v_isShared_3530_ = v_isSharedCheck_3540_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_a_3527_);
lean_dec(v___x_3526_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3540_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; 
lean_inc_ref_n(v_fileMap_3521_, 2);
v___x_3531_ = l_Lean_FileMap_toPosition(v_fileMap_3521_, v___y_3516_);
lean_dec(v___y_3516_);
v___x_3532_ = l_Lean_FileMap_toPosition(v_fileMap_3521_, v___y_3519_);
lean_dec(v___y_3519_);
v___x_3533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3533_, 0, v___x_3532_);
v___x_3534_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__19));
if (v_suppressElabErrors_3522_ == 0)
{
lean_del_object(v___x_3529_);
lean_dec_ref(v___f_3524_);
v___y_3451_ = v___x_3533_;
v___y_3452_ = v_fileName_3520_;
v___y_3453_ = v___y_3517_;
v___y_3454_ = v_a_3527_;
v___y_3455_ = v___x_3534_;
v___y_3456_ = v___x_3531_;
v___y_3457_ = v___y_3518_;
v___y_3458_ = v___y_3448_;
goto v___jp_3450_;
}
else
{
uint8_t v___x_3535_; 
lean_inc(v_a_3527_);
v___x_3535_ = l_Lean_MessageData_hasTag(v___f_3524_, v_a_3527_);
if (v___x_3535_ == 0)
{
lean_object* v___x_3536_; lean_object* v___x_3538_; 
lean_dec_ref_known(v___x_3533_, 1);
lean_dec_ref(v___x_3531_);
lean_dec(v_a_3527_);
v___x_3536_ = lean_box(0);
if (v_isShared_3530_ == 0)
{
lean_ctor_set(v___x_3529_, 0, v___x_3536_);
v___x_3538_ = v___x_3529_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v___x_3536_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
else
{
lean_del_object(v___x_3529_);
v___y_3451_ = v___x_3533_;
v___y_3452_ = v_fileName_3520_;
v___y_3453_ = v___y_3517_;
v___y_3454_ = v_a_3527_;
v___y_3455_ = v___x_3534_;
v___y_3456_ = v___x_3531_;
v___y_3457_ = v___y_3518_;
v___y_3458_ = v___y_3448_;
goto v___jp_3450_;
}
}
}
}
v___jp_3541_:
{
lean_object* v___x_3546_; 
v___x_3546_ = l_Lean_Syntax_getTailPos_x3f(v___y_3542_, v___y_3543_);
lean_dec(v___y_3542_);
if (lean_obj_tag(v___x_3546_) == 0)
{
lean_inc(v___y_3545_);
v___y_3516_ = v___y_3545_;
v___y_3517_ = v___y_3543_;
v___y_3518_ = v___y_3544_;
v___y_3519_ = v___y_3545_;
goto v___jp_3515_;
}
else
{
lean_object* v_val_3547_; 
v_val_3547_ = lean_ctor_get(v___x_3546_, 0);
lean_inc(v_val_3547_);
lean_dec_ref_known(v___x_3546_, 1);
v___y_3516_ = v___y_3545_;
v___y_3517_ = v___y_3543_;
v___y_3518_ = v___y_3544_;
v___y_3519_ = v_val_3547_;
goto v___jp_3515_;
}
}
v___jp_3548_:
{
lean_object* v___x_3551_; 
v___x_3551_ = l_Lean_Elab_Command_getRef___redArg(v___y_3447_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v_a_3552_; lean_object* v_ref_3553_; lean_object* v___x_3554_; 
v_a_3552_ = lean_ctor_get(v___x_3551_, 0);
lean_inc(v_a_3552_);
lean_dec_ref_known(v___x_3551_, 1);
v_ref_3553_ = l_Lean_replaceRef(v_ref_3443_, v_a_3552_);
lean_dec(v_a_3552_);
v___x_3554_ = l_Lean_Syntax_getPos_x3f(v_ref_3553_, v___y_3549_);
if (lean_obj_tag(v___x_3554_) == 0)
{
lean_object* v___x_3555_; 
v___x_3555_ = lean_unsigned_to_nat(0u);
v___y_3542_ = v_ref_3553_;
v___y_3543_ = v___y_3549_;
v___y_3544_ = v___y_3550_;
v___y_3545_ = v___x_3555_;
goto v___jp_3541_;
}
else
{
lean_object* v_val_3556_; 
v_val_3556_ = lean_ctor_get(v___x_3554_, 0);
lean_inc(v_val_3556_);
lean_dec_ref_known(v___x_3554_, 1);
v___y_3542_ = v_ref_3553_;
v___y_3543_ = v___y_3549_;
v___y_3544_ = v___y_3550_;
v___y_3545_ = v_val_3556_;
goto v___jp_3541_;
}
}
else
{
lean_object* v_a_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3564_; 
lean_dec_ref(v_msgData_3444_);
v_a_3557_ = lean_ctor_get(v___x_3551_, 0);
v_isSharedCheck_3564_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3559_ = v___x_3551_;
v_isShared_3560_ = v_isSharedCheck_3564_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_a_3557_);
lean_dec(v___x_3551_);
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
v___jp_3566_:
{
lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v_scopes_3570_; lean_object* v___x_3571_; lean_object* v_opts_3572_; uint8_t v___x_3573_; uint8_t v___x_3574_; 
v___x_3568_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3569_ = lean_st_ref_get(v___y_3448_);
v_scopes_3570_ = lean_ctor_get(v___x_3569_, 2);
lean_inc(v_scopes_3570_);
lean_dec(v___x_3569_);
v___x_3571_ = l_List_head_x21___redArg(v___x_3568_, v_scopes_3570_);
lean_dec(v_scopes_3570_);
v_opts_3572_ = lean_ctor_get(v___x_3571_, 1);
lean_inc_ref(v_opts_3572_);
lean_dec(v___x_3571_);
v___x_3573_ = 1;
v___x_3574_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3445_, v___x_3573_);
if (v___x_3574_ == 0)
{
lean_dec_ref(v_opts_3572_);
v___y_3549_ = v___y_3567_;
v___y_3550_ = v_severity_3445_;
goto v___jp_3548_;
}
else
{
lean_object* v___x_3575_; uint8_t v___x_3576_; 
v___x_3575_ = l_Lean_warningAsError;
v___x_3576_ = l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0(v_opts_3572_, v___x_3575_);
lean_dec_ref(v_opts_3572_);
if (v___x_3576_ == 0)
{
v___y_3549_ = v___y_3567_;
v___y_3550_ = v_severity_3445_;
goto v___jp_3548_;
}
else
{
v___y_3549_ = v___y_3567_;
v___y_3550_ = v___x_3565_;
goto v___jp_3548_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___boxed(lean_object* v_ref_3581_, lean_object* v_msgData_3582_, lean_object* v_severity_3583_, lean_object* v_isSilent_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_){
_start:
{
uint8_t v_severity_boxed_3588_; uint8_t v_isSilent_boxed_3589_; lean_object* v_res_3590_; 
v_severity_boxed_3588_ = lean_unbox(v_severity_3583_);
v_isSilent_boxed_3589_ = lean_unbox(v_isSilent_3584_);
v_res_3590_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2(v_ref_3581_, v_msgData_3582_, v_severity_boxed_3588_, v_isSilent_boxed_3589_, v___y_3585_, v___y_3586_);
lean_dec(v___y_3586_);
lean_dec_ref(v___y_3585_);
lean_dec(v_ref_3581_);
return v_res_3590_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1(lean_object* v_ref_3591_, lean_object* v_msgData_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_){
_start:
{
uint8_t v___x_3596_; uint8_t v___x_3597_; lean_object* v___x_3598_; 
v___x_3596_ = 1;
v___x_3597_ = 0;
v___x_3598_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2(v_ref_3591_, v_msgData_3592_, v___x_3596_, v___x_3597_, v___y_3593_, v___y_3594_);
return v___x_3598_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1___boxed(lean_object* v_ref_3599_, lean_object* v_msgData_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1(v_ref_3599_, v_msgData_3600_, v___y_3601_, v___y_3602_);
lean_dec(v___y_3602_);
lean_dec_ref(v___y_3601_);
lean_dec(v_ref_3599_);
return v_res_3604_;
}
}
static lean_object* _init_l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3606_; lean_object* v___x_3607_; 
v___x_3606_ = ((lean_object*)(l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__0));
v___x_3607_ = l_Lean_stringToMessageData(v___x_3606_);
return v___x_3607_;
}
}
static lean_object* _init_l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3609_; lean_object* v___x_3610_; 
v___x_3609_ = ((lean_object*)(l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__2));
v___x_3610_ = l_Lean_stringToMessageData(v___x_3609_);
return v___x_3610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0(lean_object* v_kw_3611_, lean_object* v_what_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_){
_start:
{
lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v_scopes_3618_; lean_object* v___x_3619_; lean_object* v_opts_3620_; lean_object* v___x_3621_; uint8_t v___x_3622_; 
v___x_3616_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3617_ = lean_st_ref_get(v___y_3614_);
v_scopes_3618_ = lean_ctor_get(v___x_3617_, 2);
lean_inc(v_scopes_3618_);
lean_dec(v___x_3617_);
v___x_3619_ = l_List_head_x21___redArg(v___x_3616_, v_scopes_3618_);
lean_dec(v_scopes_3618_);
v_opts_3620_ = lean_ctor_get(v___x_3619_, 1);
lean_inc_ref(v_opts_3620_);
lean_dec(v___x_3619_);
v___x_3621_ = l_Lean_Elab_Do_experimental_intrinsic;
v___x_3622_ = l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0(v_opts_3620_, v___x_3621_);
lean_dec_ref(v_opts_3620_);
if (v___x_3622_ == 0)
{
lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; 
v___x_3623_ = lean_obj_once(&l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1, &l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1_once, _init_l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1);
v___x_3624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3624_, 0, v___x_3623_);
lean_ctor_set(v___x_3624_, 1, v_what_3612_);
v___x_3625_ = lean_obj_once(&l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3, &l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3_once, _init_l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3);
v___x_3626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3626_, 0, v___x_3624_);
lean_ctor_set(v___x_3626_, 1, v___x_3625_);
v___x_3627_ = l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1(v_kw_3611_, v___x_3626_, v___y_3613_, v___y_3614_);
return v___x_3627_;
}
else
{
lean_object* v___x_3628_; lean_object* v___x_3629_; 
lean_dec_ref(v_what_3612_);
v___x_3628_ = lean_box(0);
v___x_3629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3629_, 0, v___x_3628_);
return v___x_3629_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___boxed(lean_object* v_kw_3630_, lean_object* v_what_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_){
_start:
{
lean_object* v_res_3635_; 
v_res_3635_ = l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0(v_kw_3630_, v_what_3631_, v___y_3632_, v___y_3633_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
lean_dec(v_kw_3630_);
return v_res_3635_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3637_; lean_object* v___x_3638_; 
v___x_3637_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__0));
v___x_3638_ = l_Lean_stringToMessageData(v___x_3637_);
return v___x_3638_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__3(void){
_start:
{
lean_object* v___x_3640_; lean_object* v___x_3641_; 
v___x_3640_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__2));
v___x_3641_ = l_Lean_stringToMessageData(v___x_3640_);
return v___x_3641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1(lean_object* v_as_3642_, size_t v_sz_3643_, size_t v_i_3644_, lean_object* v_b_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_){
_start:
{
uint8_t v___x_3649_; 
v___x_3649_ = lean_usize_dec_lt(v_i_3644_, v_sz_3643_);
if (v___x_3649_ == 0)
{
lean_object* v___x_3650_; 
v___x_3650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3650_, 0, v_b_3645_);
return v___x_3650_;
}
else
{
lean_object* v___x_3651_; lean_object* v_a_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3651_ = lean_box(0);
v_a_3652_ = lean_array_uget_borrowed(v_as_3642_, v_i_3644_);
v___x_3653_ = lean_unsigned_to_nat(0u);
v___x_3654_ = l_Lean_Syntax_getArg(v_a_3652_, v___x_3653_);
v___x_3655_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__1);
v___x_3656_ = l_Lean_Syntax_getAtomVal(v___x_3654_);
v___x_3657_ = l_Lean_stringToMessageData(v___x_3656_);
v___x_3658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3658_, 0, v___x_3655_);
lean_ctor_set(v___x_3658_, 1, v___x_3657_);
v___x_3659_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__3);
v___x_3660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3660_, 0, v___x_3658_);
lean_ctor_set(v___x_3660_, 1, v___x_3659_);
v___x_3661_ = l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0(v___x_3654_, v___x_3660_, v___y_3646_, v___y_3647_);
lean_dec(v___x_3654_);
if (lean_obj_tag(v___x_3661_) == 0)
{
size_t v___x_3662_; size_t v___x_3663_; 
lean_dec_ref_known(v___x_3661_, 1);
v___x_3662_ = ((size_t)1ULL);
v___x_3663_ = lean_usize_add(v_i_3644_, v___x_3662_);
v_i_3644_ = v___x_3663_;
v_b_3645_ = v___x_3651_;
goto _start;
}
else
{
return v___x_3661_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___boxed(lean_object* v_as_3665_, lean_object* v_sz_3666_, lean_object* v_i_3667_, lean_object* v_b_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_){
_start:
{
size_t v_sz_boxed_3672_; size_t v_i_boxed_3673_; lean_object* v_res_3674_; 
v_sz_boxed_3672_ = lean_unbox_usize(v_sz_3666_);
lean_dec(v_sz_3666_);
v_i_boxed_3673_ = lean_unbox_usize(v_i_3667_);
lean_dec(v_i_3667_);
v_res_3674_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1(v_as_3665_, v_sz_boxed_3672_, v_i_boxed_3673_, v_b_3668_, v___y_3669_, v___y_3670_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
lean_dec_ref(v_as_3665_);
return v_res_3674_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__2(lean_object* v_as_3675_, size_t v_sz_3676_, size_t v_i_3677_, lean_object* v_b_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_){
_start:
{
uint8_t v___x_3682_; 
v___x_3682_ = lean_usize_dec_lt(v_i_3677_, v_sz_3676_);
if (v___x_3682_ == 0)
{
lean_object* v___x_3683_; 
v___x_3683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3683_, 0, v_b_3678_);
return v___x_3683_;
}
else
{
lean_object* v___x_3684_; lean_object* v_a_3685_; lean_object* v___x_3686_; size_t v_sz_3687_; size_t v___x_3688_; lean_object* v___x_3689_; 
v___x_3684_ = lean_box(0);
v_a_3685_ = lean_array_uget_borrowed(v_as_3675_, v_i_3677_);
v___x_3686_ = l_Lean_Syntax_getArgs(v_a_3685_);
v_sz_3687_ = lean_array_size(v___x_3686_);
v___x_3688_ = ((size_t)0ULL);
v___x_3689_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1(v___x_3686_, v_sz_3687_, v___x_3688_, v___x_3684_, v___y_3679_, v___y_3680_);
lean_dec_ref(v___x_3686_);
if (lean_obj_tag(v___x_3689_) == 0)
{
size_t v___x_3690_; size_t v___x_3691_; 
lean_dec_ref_known(v___x_3689_, 1);
v___x_3690_ = ((size_t)1ULL);
v___x_3691_ = lean_usize_add(v_i_3677_, v___x_3690_);
v_i_3677_ = v___x_3691_;
v_b_3678_ = v___x_3684_;
goto _start;
}
else
{
return v___x_3689_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__2___boxed(lean_object* v_as_3693_, lean_object* v_sz_3694_, lean_object* v_i_3695_, lean_object* v_b_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_){
_start:
{
size_t v_sz_boxed_3700_; size_t v_i_boxed_3701_; lean_object* v_res_3702_; 
v_sz_boxed_3700_ = lean_unbox_usize(v_sz_3694_);
lean_dec(v_sz_3694_);
v_i_boxed_3701_ = lean_unbox_usize(v_i_3695_);
lean_dec(v_i_3695_);
v_res_3702_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__2(v_as_3693_, v_sz_boxed_3700_, v_i_boxed_3701_, v_b_3696_, v___y_3697_, v___y_3698_);
lean_dec(v___y_3698_);
lean_dec_ref(v___y_3697_);
lean_dec_ref(v_as_3693_);
return v_res_3702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractNotice(lean_object* v_stx_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_){
_start:
{
lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; size_t v_sz_3710_; size_t v___x_3711_; lean_object* v___x_3712_; 
v___x_3707_ = l_Lean_Syntax_getArgs(v_stx_3703_);
v___x_3708_ = lean_array_pop(v___x_3707_);
v___x_3709_ = lean_box(0);
v_sz_3710_ = lean_array_size(v___x_3708_);
v___x_3711_ = ((size_t)0ULL);
v___x_3712_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__2(v___x_3708_, v_sz_3710_, v___x_3711_, v___x_3709_, v_a_3704_, v_a_3705_);
lean_dec_ref(v___x_3708_);
if (lean_obj_tag(v___x_3712_) == 0)
{
lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3719_; 
v_isSharedCheck_3719_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3719_ == 0)
{
lean_object* v_unused_3720_; 
v_unused_3720_ = lean_ctor_get(v___x_3712_, 0);
lean_dec(v_unused_3720_);
v___x_3714_ = v___x_3712_;
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
else
{
lean_dec(v___x_3712_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___x_3717_; 
if (v_isShared_3715_ == 0)
{
lean_ctor_set(v___x_3714_, 0, v___x_3709_);
v___x_3717_ = v___x_3714_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v___x_3709_);
v___x_3717_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
return v___x_3717_;
}
}
}
else
{
return v___x_3712_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractNotice___boxed(lean_object* v_stx_3721_, lean_object* v_a_3722_, lean_object* v_a_3723_, lean_object* v_a_3724_){
_start:
{
lean_object* v_res_3725_; 
v_res_3725_ = l_Lean_Elab_Tactic_Do_elabContractNotice(v_stx_3721_, v_a_3722_, v_a_3723_);
lean_dec(v_a_3723_);
lean_dec_ref(v_a_3722_);
lean_dec(v_stx_3721_);
return v_res_3725_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5(lean_object* v_msgData_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_){
_start:
{
lean_object* v___x_3730_; 
v___x_3730_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg(v_msgData_3726_, v___y_3728_);
return v___x_3730_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___boxed(lean_object* v_msgData_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_){
_start:
{
lean_object* v_res_3735_; 
v_res_3735_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5(v_msgData_3731_, v___y_3732_, v___y_3733_);
lean_dec(v___y_3733_);
lean_dec_ref(v___y_3732_);
return v_res_3735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1(){
_start:
{
lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; 
v___x_3744_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3745_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__1));
v___x_3746_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__1));
v___x_3747_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elabContractNotice___boxed), 4, 0);
v___x_3748_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3744_, v___x_3745_, v___x_3746_, v___x_3747_);
return v___x_3748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___boxed(lean_object* v_a_3749_){
_start:
{
lean_object* v_res_3750_; 
v_res_3750_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1();
return v_res_3750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice_docString__3(){
_start:
{
lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; 
v___x_3753_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__1));
v___x_3754_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice_docString__3___closed__0));
v___x_3755_ = l_Lean_addBuiltinDocString(v___x_3753_, v___x_3754_);
return v___x_3755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice_docString__3___boxed(lean_object* v_a_3756_){
_start:
{
lean_object* v_res_3757_; 
v_res_3757_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice_docString__3();
return v_res_3757_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; 
v___x_3758_ = lean_box(0);
v___x_3759_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3760_, 0, v___x_3759_);
lean_ctor_set(v___x_3760_, 1, v___x_3758_);
return v___x_3760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg(){
_start:
{
lean_object* v___x_3762_; lean_object* v___x_3763_; 
v___x_3762_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg___closed__0);
v___x_3763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3763_, 0, v___x_3762_);
return v___x_3763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg___boxed(lean_object* v___y_3764_){
_start:
{
lean_object* v_res_3765_; 
v_res_3765_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg();
return v_res_3765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2(lean_object* v_00_u03b1_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_){
_start:
{
lean_object* v___x_3775_; 
v___x_3775_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg();
return v___x_3775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___boxed(lean_object* v_00_u03b1_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_){
_start:
{
lean_object* v_res_3785_; 
v_res_3785_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2(v_00_u03b1_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_);
lean_dec(v___y_3783_);
lean_dec_ref(v___y_3782_);
lean_dec(v___y_3781_);
lean_dec_ref(v___y_3780_);
lean_dec(v___y_3779_);
lean_dec_ref(v___y_3778_);
lean_dec_ref(v___y_3777_);
return v_res_3785_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2_spec__5(lean_object* v_msgData_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_){
_start:
{
lean_object* v___x_3792_; lean_object* v_env_3793_; uint8_t v___x_3794_; lean_object* v_env_3795_; lean_object* v___x_3796_; lean_object* v_toCold_3797_; lean_object* v_mctx_3798_; lean_object* v_lctx_3799_; lean_object* v_options_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; 
v___x_3792_ = lean_st_ref_get(v___y_3790_);
v_env_3793_ = lean_ctor_get(v___x_3792_, 0);
lean_inc_ref(v_env_3793_);
lean_dec(v___x_3792_);
v___x_3794_ = 0;
v_env_3795_ = l_Lean_Environment_setRecordingDeps(v_env_3793_, v___x_3794_);
v___x_3796_ = lean_st_ref_get(v___y_3788_);
v_toCold_3797_ = lean_ctor_get(v___y_3789_, 0);
v_mctx_3798_ = lean_ctor_get(v___x_3796_, 0);
lean_inc_ref(v_mctx_3798_);
lean_dec(v___x_3796_);
v_lctx_3799_ = lean_ctor_get(v___y_3787_, 2);
v_options_3800_ = lean_ctor_get(v_toCold_3797_, 2);
lean_inc_ref(v_options_3800_);
lean_inc_ref(v_lctx_3799_);
v___x_3801_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3801_, 0, v_env_3795_);
lean_ctor_set(v___x_3801_, 1, v_mctx_3798_);
lean_ctor_set(v___x_3801_, 2, v_lctx_3799_);
lean_ctor_set(v___x_3801_, 3, v_options_3800_);
v___x_3802_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3802_, 0, v___x_3801_);
lean_ctor_set(v___x_3802_, 1, v_msgData_3786_);
v___x_3803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3803_, 0, v___x_3802_);
return v___x_3803_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2_spec__5___boxed(lean_object* v_msgData_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_){
_start:
{
lean_object* v_res_3810_; 
v_res_3810_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2_spec__5(v_msgData_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
lean_dec(v___y_3808_);
lean_dec_ref(v___y_3807_);
lean_dec(v___y_3806_);
lean_dec_ref(v___y_3805_);
return v_res_3810_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0(uint8_t v_suppressElabErrors_3816_, lean_object* v_x_3817_){
_start:
{
if (lean_obj_tag(v_x_3817_) == 1)
{
lean_object* v_pre_3818_; 
v_pre_3818_ = lean_ctor_get(v_x_3817_, 0);
switch(lean_obj_tag(v_pre_3818_))
{
case 1:
{
lean_object* v_pre_3819_; 
v_pre_3819_ = lean_ctor_get(v_pre_3818_, 0);
switch(lean_obj_tag(v_pre_3819_))
{
case 0:
{
lean_object* v_str_3820_; lean_object* v_str_3821_; lean_object* v___x_3822_; uint8_t v___x_3823_; 
v_str_3820_ = lean_ctor_get(v_x_3817_, 1);
v_str_3821_ = lean_ctor_get(v_pre_3818_, 1);
v___x_3822_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__21));
v___x_3823_ = lean_string_dec_eq(v_str_3821_, v___x_3822_);
if (v___x_3823_ == 0)
{
lean_object* v___x_3824_; uint8_t v___x_3825_; 
v___x_3824_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__22));
v___x_3825_ = lean_string_dec_eq(v_str_3821_, v___x_3824_);
if (v___x_3825_ == 0)
{
return v___x_3825_;
}
else
{
lean_object* v___x_3826_; uint8_t v___x_3827_; 
v___x_3826_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__0));
v___x_3827_ = lean_string_dec_eq(v_str_3820_, v___x_3826_);
if (v___x_3827_ == 0)
{
return v___x_3827_;
}
else
{
return v_suppressElabErrors_3816_;
}
}
}
else
{
lean_object* v___x_3828_; uint8_t v___x_3829_; 
v___x_3828_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__1));
v___x_3829_ = lean_string_dec_eq(v_str_3820_, v___x_3828_);
if (v___x_3829_ == 0)
{
return v___x_3829_;
}
else
{
return v_suppressElabErrors_3816_;
}
}
}
case 1:
{
lean_object* v_pre_3830_; 
v_pre_3830_ = lean_ctor_get(v_pre_3819_, 0);
if (lean_obj_tag(v_pre_3830_) == 0)
{
lean_object* v_str_3831_; lean_object* v_str_3832_; lean_object* v_str_3833_; lean_object* v___x_3834_; uint8_t v___x_3835_; 
v_str_3831_ = lean_ctor_get(v_x_3817_, 1);
v_str_3832_ = lean_ctor_get(v_pre_3818_, 1);
v_str_3833_ = lean_ctor_get(v_pre_3819_, 1);
v___x_3834_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__2));
v___x_3835_ = lean_string_dec_eq(v_str_3833_, v___x_3834_);
if (v___x_3835_ == 0)
{
return v___x_3835_;
}
else
{
lean_object* v___x_3836_; uint8_t v___x_3837_; 
v___x_3836_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__3));
v___x_3837_ = lean_string_dec_eq(v_str_3832_, v___x_3836_);
if (v___x_3837_ == 0)
{
return v___x_3837_;
}
else
{
lean_object* v___x_3838_; uint8_t v___x_3839_; 
v___x_3838_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__4));
v___x_3839_ = lean_string_dec_eq(v_str_3831_, v___x_3838_);
if (v___x_3839_ == 0)
{
return v___x_3839_;
}
else
{
return v_suppressElabErrors_3816_;
}
}
}
}
else
{
uint8_t v___x_3840_; 
v___x_3840_ = 0;
return v___x_3840_;
}
}
default: 
{
uint8_t v___x_3841_; 
v___x_3841_ = 0;
return v___x_3841_;
}
}
}
case 0:
{
lean_object* v_str_3842_; lean_object* v___x_3843_; uint8_t v___x_3844_; 
v_str_3842_ = lean_ctor_get(v_x_3817_, 1);
v___x_3843_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0___closed__0));
v___x_3844_ = lean_string_dec_eq(v_str_3842_, v___x_3843_);
if (v___x_3844_ == 0)
{
return v___x_3844_;
}
else
{
return v_suppressElabErrors_3816_;
}
}
default: 
{
uint8_t v___x_3845_; 
v___x_3845_ = 0;
return v___x_3845_;
}
}
}
else
{
uint8_t v___x_3846_; 
v___x_3846_ = 0;
return v___x_3846_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_3847_, lean_object* v_x_3848_){
_start:
{
uint8_t v_suppressElabErrors_boxed_3849_; uint8_t v_res_3850_; lean_object* v_r_3851_; 
v_suppressElabErrors_boxed_3849_ = lean_unbox(v_suppressElabErrors_3847_);
v_res_3850_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0(v_suppressElabErrors_boxed_3849_, v_x_3848_);
lean_dec(v_x_3848_);
v_r_3851_ = lean_box(v_res_3850_);
return v_r_3851_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_3852_, lean_object* v_msgData_3853_, uint8_t v_severity_3854_, uint8_t v_isSilent_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_){
_start:
{
lean_object* v___y_3862_; lean_object* v___y_3863_; uint8_t v___y_3864_; lean_object* v___y_3865_; lean_object* v___y_3866_; lean_object* v___y_3867_; uint8_t v___y_3868_; lean_object* v_toCold_3869_; lean_object* v___y_3870_; lean_object* v___y_3899_; lean_object* v___y_3900_; uint8_t v___y_3901_; lean_object* v___y_3902_; lean_object* v___y_3903_; uint8_t v___y_3904_; uint8_t v___y_3905_; lean_object* v___y_3906_; lean_object* v___y_3926_; lean_object* v___y_3927_; uint8_t v___y_3928_; uint8_t v___y_3929_; lean_object* v___y_3930_; uint8_t v___y_3931_; lean_object* v___y_3932_; uint8_t v___y_3936_; uint8_t v___y_3937_; uint8_t v___x_3947_; uint8_t v___y_3949_; uint8_t v___x_3955_; 
v___x_3947_ = 2;
v___x_3955_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3854_, v___x_3947_);
if (v___x_3955_ == 0)
{
v___y_3949_ = v___x_3955_;
goto v___jp_3948_;
}
else
{
uint8_t v___x_3956_; 
lean_inc_ref(v_msgData_3853_);
v___x_3956_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3853_);
if (v___x_3956_ == 0)
{
v___y_3949_ = v___x_3956_;
goto v___jp_3948_;
}
else
{
lean_object* v___x_3957_; lean_object* v___x_3958_; 
lean_dec_ref(v_msgData_3853_);
v___x_3957_ = lean_box(0);
v___x_3958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3958_, 0, v___x_3957_);
return v___x_3958_;
}
}
v___jp_3861_:
{
lean_object* v_currNamespace_3871_; lean_object* v_openDecls_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v_env_3877_; lean_object* v_nextMacroScope_3878_; lean_object* v_ngen_3879_; lean_object* v_auxDeclNGen_3880_; lean_object* v_traceState_3881_; lean_object* v_cache_3882_; lean_object* v_recordedDeps_3883_; lean_object* v_messages_3884_; lean_object* v_infoState_3885_; lean_object* v_snapshotTasks_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3897_; 
v_currNamespace_3871_ = lean_ctor_get(v_toCold_3869_, 4);
v_openDecls_3872_ = lean_ctor_get(v_toCold_3869_, 5);
lean_inc(v_openDecls_3872_);
lean_inc(v_currNamespace_3871_);
v___x_3873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3873_, 0, v_currNamespace_3871_);
lean_ctor_set(v___x_3873_, 1, v_openDecls_3872_);
v___x_3874_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3874_, 0, v___x_3873_);
lean_ctor_set(v___x_3874_, 1, v___y_3867_);
lean_inc_ref(v___y_3862_);
lean_inc_ref(v___y_3865_);
v___x_3875_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3875_, 0, v___y_3865_);
lean_ctor_set(v___x_3875_, 1, v___y_3863_);
lean_ctor_set(v___x_3875_, 2, v___y_3866_);
lean_ctor_set(v___x_3875_, 3, v___y_3862_);
lean_ctor_set(v___x_3875_, 4, v___x_3874_);
lean_ctor_set_uint8(v___x_3875_, sizeof(void*)*5, v___y_3864_);
lean_ctor_set_uint8(v___x_3875_, sizeof(void*)*5 + 1, v___y_3868_);
lean_ctor_set_uint8(v___x_3875_, sizeof(void*)*5 + 2, v_isSilent_3855_);
v___x_3876_ = lean_st_ref_take(v___y_3870_);
v_env_3877_ = lean_ctor_get(v___x_3876_, 0);
v_nextMacroScope_3878_ = lean_ctor_get(v___x_3876_, 1);
v_ngen_3879_ = lean_ctor_get(v___x_3876_, 2);
v_auxDeclNGen_3880_ = lean_ctor_get(v___x_3876_, 3);
v_traceState_3881_ = lean_ctor_get(v___x_3876_, 4);
v_cache_3882_ = lean_ctor_get(v___x_3876_, 5);
v_recordedDeps_3883_ = lean_ctor_get(v___x_3876_, 6);
v_messages_3884_ = lean_ctor_get(v___x_3876_, 7);
v_infoState_3885_ = lean_ctor_get(v___x_3876_, 8);
v_snapshotTasks_3886_ = lean_ctor_get(v___x_3876_, 9);
v_isSharedCheck_3897_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3897_ == 0)
{
v___x_3888_ = v___x_3876_;
v_isShared_3889_ = v_isSharedCheck_3897_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_snapshotTasks_3886_);
lean_inc(v_infoState_3885_);
lean_inc(v_messages_3884_);
lean_inc(v_recordedDeps_3883_);
lean_inc(v_cache_3882_);
lean_inc(v_traceState_3881_);
lean_inc(v_auxDeclNGen_3880_);
lean_inc(v_ngen_3879_);
lean_inc(v_nextMacroScope_3878_);
lean_inc(v_env_3877_);
lean_dec(v___x_3876_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3897_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3893_; 
v___x_3890_ = lean_box(0);
v___x_3891_ = l_Lean_MessageLog_add(v___x_3875_, v_messages_3884_);
if (v_isShared_3889_ == 0)
{
lean_ctor_set(v___x_3888_, 7, v___x_3891_);
v___x_3893_ = v___x_3888_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v_env_3877_);
lean_ctor_set(v_reuseFailAlloc_3896_, 1, v_nextMacroScope_3878_);
lean_ctor_set(v_reuseFailAlloc_3896_, 2, v_ngen_3879_);
lean_ctor_set(v_reuseFailAlloc_3896_, 3, v_auxDeclNGen_3880_);
lean_ctor_set(v_reuseFailAlloc_3896_, 4, v_traceState_3881_);
lean_ctor_set(v_reuseFailAlloc_3896_, 5, v_cache_3882_);
lean_ctor_set(v_reuseFailAlloc_3896_, 6, v_recordedDeps_3883_);
lean_ctor_set(v_reuseFailAlloc_3896_, 7, v___x_3891_);
lean_ctor_set(v_reuseFailAlloc_3896_, 8, v_infoState_3885_);
lean_ctor_set(v_reuseFailAlloc_3896_, 9, v_snapshotTasks_3886_);
v___x_3893_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
lean_object* v___x_3894_; lean_object* v___x_3895_; 
v___x_3894_ = lean_st_ref_put(v___y_3870_, v___x_3893_);
v___x_3895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3895_, 0, v___x_3890_);
return v___x_3895_;
}
}
}
v___jp_3898_:
{
lean_object* v_fileName_3907_; lean_object* v_fileMap_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v_a_3911_; lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_3924_; 
v_fileName_3907_ = lean_ctor_get(v___y_3903_, 0);
v_fileMap_3908_ = lean_ctor_get(v___y_3903_, 1);
v___x_3909_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3853_);
v___x_3910_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2_spec__5(v___x_3909_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
v_a_3911_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3913_ = v___x_3910_;
v_isShared_3914_ = v_isSharedCheck_3924_;
goto v_resetjp_3912_;
}
else
{
lean_inc(v_a_3911_);
lean_dec(v___x_3910_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_3924_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; 
lean_inc_ref_n(v_fileMap_3908_, 2);
v___x_3915_ = l_Lean_FileMap_toPosition(v_fileMap_3908_, v___y_3902_);
lean_dec(v___y_3902_);
v___x_3916_ = l_Lean_FileMap_toPosition(v_fileMap_3908_, v___y_3906_);
lean_dec(v___y_3906_);
v___x_3917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3917_, 0, v___x_3916_);
v___x_3918_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__19));
if (v___y_3904_ == 0)
{
lean_del_object(v___x_3913_);
lean_dec_ref(v___y_3899_);
v___y_3862_ = v___x_3918_;
v___y_3863_ = v___x_3915_;
v___y_3864_ = v___y_3901_;
v___y_3865_ = v_fileName_3907_;
v___y_3866_ = v___x_3917_;
v___y_3867_ = v_a_3911_;
v___y_3868_ = v___y_3905_;
v_toCold_3869_ = v___y_3900_;
v___y_3870_ = v___y_3859_;
goto v___jp_3861_;
}
else
{
uint8_t v___x_3919_; 
lean_inc(v_a_3911_);
v___x_3919_ = l_Lean_MessageData_hasTag(v___y_3899_, v_a_3911_);
if (v___x_3919_ == 0)
{
lean_object* v___x_3920_; lean_object* v___x_3922_; 
lean_dec_ref_known(v___x_3917_, 1);
lean_dec_ref(v___x_3915_);
lean_dec(v_a_3911_);
v___x_3920_ = lean_box(0);
if (v_isShared_3914_ == 0)
{
lean_ctor_set(v___x_3913_, 0, v___x_3920_);
v___x_3922_ = v___x_3913_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v___x_3920_);
v___x_3922_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
return v___x_3922_;
}
}
else
{
lean_del_object(v___x_3913_);
v___y_3862_ = v___x_3918_;
v___y_3863_ = v___x_3915_;
v___y_3864_ = v___y_3901_;
v___y_3865_ = v_fileName_3907_;
v___y_3866_ = v___x_3917_;
v___y_3867_ = v_a_3911_;
v___y_3868_ = v___y_3905_;
v_toCold_3869_ = v___y_3900_;
v___y_3870_ = v___y_3859_;
goto v___jp_3861_;
}
}
}
}
v___jp_3925_:
{
lean_object* v___x_3933_; 
v___x_3933_ = l_Lean_Syntax_getTailPos_x3f(v___y_3930_, v___y_3929_);
lean_dec(v___y_3930_);
if (lean_obj_tag(v___x_3933_) == 0)
{
lean_inc(v___y_3932_);
v___y_3899_ = v___y_3926_;
v___y_3900_ = v___y_3927_;
v___y_3901_ = v___y_3929_;
v___y_3902_ = v___y_3932_;
v___y_3903_ = v___y_3927_;
v___y_3904_ = v___y_3928_;
v___y_3905_ = v___y_3931_;
v___y_3906_ = v___y_3932_;
goto v___jp_3898_;
}
else
{
lean_object* v_val_3934_; 
v_val_3934_ = lean_ctor_get(v___x_3933_, 0);
lean_inc(v_val_3934_);
lean_dec_ref_known(v___x_3933_, 1);
v___y_3899_ = v___y_3926_;
v___y_3900_ = v___y_3927_;
v___y_3901_ = v___y_3929_;
v___y_3902_ = v___y_3932_;
v___y_3903_ = v___y_3927_;
v___y_3904_ = v___y_3928_;
v___y_3905_ = v___y_3931_;
v___y_3906_ = v_val_3934_;
goto v___jp_3898_;
}
}
v___jp_3935_:
{
lean_object* v_toCold_3938_; lean_object* v_ref_3939_; uint8_t v_suppressElabErrors_3940_; lean_object* v___x_3941_; lean_object* v___f_3942_; lean_object* v_ref_3943_; lean_object* v___x_3944_; 
v_toCold_3938_ = lean_ctor_get(v___y_3858_, 0);
v_ref_3939_ = lean_ctor_get(v___y_3858_, 2);
v_suppressElabErrors_3940_ = lean_ctor_get_uint8(v___y_3858_, sizeof(void*)*3 + 2);
v___x_3941_ = lean_box(v_suppressElabErrors_3940_);
v___f_3942_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3942_, 0, v___x_3941_);
v_ref_3943_ = l_Lean_replaceRef(v_ref_3852_, v_ref_3939_);
v___x_3944_ = l_Lean_Syntax_getPos_x3f(v_ref_3943_, v___y_3936_);
if (lean_obj_tag(v___x_3944_) == 0)
{
lean_object* v___x_3945_; 
v___x_3945_ = lean_unsigned_to_nat(0u);
v___y_3926_ = v___f_3942_;
v___y_3927_ = v_toCold_3938_;
v___y_3928_ = v_suppressElabErrors_3940_;
v___y_3929_ = v___y_3936_;
v___y_3930_ = v_ref_3943_;
v___y_3931_ = v___y_3937_;
v___y_3932_ = v___x_3945_;
goto v___jp_3925_;
}
else
{
lean_object* v_val_3946_; 
v_val_3946_ = lean_ctor_get(v___x_3944_, 0);
lean_inc(v_val_3946_);
lean_dec_ref_known(v___x_3944_, 1);
v___y_3926_ = v___f_3942_;
v___y_3927_ = v_toCold_3938_;
v___y_3928_ = v_suppressElabErrors_3940_;
v___y_3929_ = v___y_3936_;
v___y_3930_ = v_ref_3943_;
v___y_3931_ = v___y_3937_;
v___y_3932_ = v_val_3946_;
goto v___jp_3925_;
}
}
v___jp_3948_:
{
uint8_t v___x_3950_; uint8_t v___x_3951_; 
v___x_3950_ = 1;
v___x_3951_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3854_, v___x_3950_);
if (v___x_3951_ == 0)
{
v___y_3936_ = v___y_3949_;
v___y_3937_ = v_severity_3854_;
goto v___jp_3935_;
}
else
{
lean_object* v___x_3952_; lean_object* v___x_3953_; uint8_t v___x_3954_; 
v___x_3952_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3858_);
v___x_3953_ = l_Lean_warningAsError;
v___x_3954_ = l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0(v___x_3952_, v___x_3953_);
lean_dec_ref(v___x_3952_);
if (v___x_3954_ == 0)
{
v___y_3936_ = v___y_3949_;
v___y_3937_ = v_severity_3854_;
goto v___jp_3935_;
}
else
{
v___y_3936_ = v___y_3949_;
v___y_3937_ = v___x_3947_;
goto v___jp_3935_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_3959_, lean_object* v_msgData_3960_, lean_object* v_severity_3961_, lean_object* v_isSilent_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_){
_start:
{
uint8_t v_severity_boxed_3968_; uint8_t v_isSilent_boxed_3969_; lean_object* v_res_3970_; 
v_severity_boxed_3968_ = lean_unbox(v_severity_3961_);
v_isSilent_boxed_3969_ = lean_unbox(v_isSilent_3962_);
v_res_3970_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg(v_ref_3959_, v_msgData_3960_, v_severity_boxed_3968_, v_isSilent_boxed_3969_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_);
lean_dec(v___y_3966_);
lean_dec_ref(v___y_3965_);
lean_dec(v___y_3964_);
lean_dec_ref(v___y_3963_);
lean_dec(v_ref_3959_);
return v_res_3970_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0(lean_object* v_ref_3971_, lean_object* v_msgData_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_){
_start:
{
uint8_t v___x_3981_; uint8_t v___x_3982_; lean_object* v___x_3983_; 
v___x_3981_ = 1;
v___x_3982_ = 0;
v___x_3983_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg(v_ref_3971_, v_msgData_3972_, v___x_3981_, v___x_3982_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_);
return v___x_3983_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0___boxed(lean_object* v_ref_3984_, lean_object* v_msgData_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_){
_start:
{
lean_object* v_res_3994_; 
v_res_3994_ = l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0(v_ref_3984_, v_msgData_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_);
lean_dec(v___y_3992_);
lean_dec_ref(v___y_3991_);
lean_dec(v___y_3990_);
lean_dec_ref(v___y_3989_);
lean_dec(v___y_3988_);
lean_dec_ref(v___y_3987_);
lean_dec_ref(v___y_3986_);
lean_dec(v_ref_3984_);
return v_res_3994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0(lean_object* v_kw_3995_, lean_object* v_what_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_){
_start:
{
lean_object* v___x_4005_; lean_object* v___x_4006_; uint8_t v___x_4007_; 
v___x_4005_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_4002_);
v___x_4006_ = l_Lean_Elab_Do_experimental_intrinsic;
v___x_4007_ = l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0(v___x_4005_, v___x_4006_);
lean_dec_ref(v___x_4005_);
if (v___x_4007_ == 0)
{
lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; 
v___x_4008_ = lean_obj_once(&l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1, &l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1_once, _init_l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1);
v___x_4009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4009_, 0, v___x_4008_);
lean_ctor_set(v___x_4009_, 1, v_what_3996_);
v___x_4010_ = lean_obj_once(&l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3, &l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3_once, _init_l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3);
v___x_4011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4011_, 0, v___x_4009_);
lean_ctor_set(v___x_4011_, 1, v___x_4010_);
v___x_4012_ = l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0(v_kw_3995_, v___x_4011_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_);
return v___x_4012_;
}
else
{
lean_object* v___x_4013_; lean_object* v___x_4014_; 
lean_dec_ref(v_what_3996_);
v___x_4013_ = lean_box(0);
v___x_4014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4014_, 0, v___x_4013_);
return v___x_4014_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0___boxed(lean_object* v_kw_4015_, lean_object* v_what_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_){
_start:
{
lean_object* v_res_4025_; 
v_res_4025_ = l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0(v_kw_4015_, v_what_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_);
lean_dec(v___y_4023_);
lean_dec_ref(v___y_4022_);
lean_dec(v___y_4021_);
lean_dec_ref(v___y_4020_);
lean_dec(v___y_4019_);
lean_dec_ref(v___y_4018_);
lean_dec_ref(v___y_4017_);
lean_dec(v_kw_4015_);
return v_res_4025_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2___redArg(lean_object* v_msg_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_){
_start:
{
lean_object* v_ref_4032_; lean_object* v___x_4033_; lean_object* v_a_4034_; lean_object* v___x_4036_; uint8_t v_isShared_4037_; uint8_t v_isSharedCheck_4042_; 
v_ref_4032_ = lean_ctor_get(v___y_4029_, 2);
v___x_4033_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2_spec__5(v_msg_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_);
v_a_4034_ = lean_ctor_get(v___x_4033_, 0);
v_isSharedCheck_4042_ = !lean_is_exclusive(v___x_4033_);
if (v_isSharedCheck_4042_ == 0)
{
v___x_4036_ = v___x_4033_;
v_isShared_4037_ = v_isSharedCheck_4042_;
goto v_resetjp_4035_;
}
else
{
lean_inc(v_a_4034_);
lean_dec(v___x_4033_);
v___x_4036_ = lean_box(0);
v_isShared_4037_ = v_isSharedCheck_4042_;
goto v_resetjp_4035_;
}
v_resetjp_4035_:
{
lean_object* v___x_4038_; lean_object* v___x_4040_; 
lean_inc(v_ref_4032_);
v___x_4038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4038_, 0, v_ref_4032_);
lean_ctor_set(v___x_4038_, 1, v_a_4034_);
if (v_isShared_4037_ == 0)
{
lean_ctor_set_tag(v___x_4036_, 1);
lean_ctor_set(v___x_4036_, 0, v___x_4038_);
v___x_4040_ = v___x_4036_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v___x_4038_);
v___x_4040_ = v_reuseFailAlloc_4041_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
return v___x_4040_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2___redArg___boxed(lean_object* v_msg_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_){
_start:
{
lean_object* v_res_4049_; 
v_res_4049_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2___redArg(v_msg_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_);
lean_dec(v___y_4047_);
lean_dec_ref(v___y_4046_);
lean_dec(v___y_4045_);
lean_dec_ref(v___y_4044_);
return v_res_4049_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg(lean_object* v_ref_4050_, lean_object* v_msg_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_){
_start:
{
lean_object* v_toCold_4060_; lean_object* v_currRecDepth_4061_; lean_object* v_ref_4062_; uint16_t v_optionFlags_4063_; uint8_t v_suppressElabErrors_4064_; uint8_t v_checkDeprecated_4065_; uint8_t v_isRecordingDeps_4066_; lean_object* v_ref_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; 
v_toCold_4060_ = lean_ctor_get(v___y_4057_, 0);
v_currRecDepth_4061_ = lean_ctor_get(v___y_4057_, 1);
v_ref_4062_ = lean_ctor_get(v___y_4057_, 2);
v_optionFlags_4063_ = lean_ctor_get_uint16(v___y_4057_, sizeof(void*)*3);
v_suppressElabErrors_4064_ = lean_ctor_get_uint8(v___y_4057_, sizeof(void*)*3 + 2);
v_checkDeprecated_4065_ = lean_ctor_get_uint8(v___y_4057_, sizeof(void*)*3 + 3);
v_isRecordingDeps_4066_ = lean_ctor_get_uint8(v___y_4057_, sizeof(void*)*3 + 4);
v_ref_4067_ = l_Lean_replaceRef(v_ref_4050_, v_ref_4062_);
lean_inc(v_currRecDepth_4061_);
lean_inc_ref(v_toCold_4060_);
v___x_4068_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_4068_, 0, v_toCold_4060_);
lean_ctor_set(v___x_4068_, 1, v_currRecDepth_4061_);
lean_ctor_set(v___x_4068_, 2, v_ref_4067_);
lean_ctor_set_uint16(v___x_4068_, sizeof(void*)*3, v_optionFlags_4063_);
lean_ctor_set_uint8(v___x_4068_, sizeof(void*)*3 + 2, v_suppressElabErrors_4064_);
lean_ctor_set_uint8(v___x_4068_, sizeof(void*)*3 + 3, v_checkDeprecated_4065_);
lean_ctor_set_uint8(v___x_4068_, sizeof(void*)*3 + 4, v_isRecordingDeps_4066_);
v___x_4069_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2___redArg(v_msg_4051_, v___y_4055_, v___y_4056_, v___x_4068_, v___y_4058_);
lean_dec_ref_known(v___x_4068_, 3);
return v___x_4069_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg___boxed(lean_object* v_ref_4070_, lean_object* v_msg_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_){
_start:
{
lean_object* v_res_4080_; 
v_res_4080_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg(v_ref_4070_, v_msg_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
lean_dec(v___y_4076_);
lean_dec_ref(v___y_4075_);
lean_dec(v___y_4074_);
lean_dec_ref(v___y_4073_);
lean_dec_ref(v___y_4072_);
lean_dec(v_ref_4070_);
return v_res_4080_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__1(void){
_start:
{
lean_object* v___x_4082_; lean_object* v___x_4083_; 
v___x_4082_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__0));
v___x_4083_ = l_Lean_stringToMessageData(v___x_4082_);
return v___x_4083_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__9(void){
_start:
{
lean_object* v___x_4107_; lean_object* v___x_4108_; 
v___x_4107_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__8));
v___x_4108_ = l_Lean_mkCIdent(v___x_4107_);
return v___x_4108_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__11(void){
_start:
{
lean_object* v___x_4110_; lean_object* v___x_4111_; 
v___x_4110_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__10));
v___x_4111_ = l_Lean_stringToMessageData(v___x_4110_);
return v___x_4111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion(lean_object* v_stx_4118_, lean_object* v_dec_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_, lean_object* v_a_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_){
_start:
{
lean_object* v___x_4128_; lean_object* v_tk_4129_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v_as_4208_; lean_object* v___y_4209_; lean_object* v___y_4210_; lean_object* v___y_4211_; lean_object* v___y_4212_; lean_object* v___y_4213_; lean_object* v___y_4214_; lean_object* v___y_4215_; lean_object* v___x_4231_; uint8_t v___x_4232_; 
v___x_4128_ = lean_unsigned_to_nat(0u);
v_tk_4129_ = l_Lean_Syntax_getArg(v_stx_4118_, v___x_4128_);
v___x_4231_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__13));
lean_inc(v_stx_4118_);
v___x_4232_ = l_Lean_Syntax_isOfKind(v_stx_4118_, v___x_4231_);
if (v___x_4232_ == 0)
{
lean_object* v___x_4233_; lean_object* v_a_4234_; lean_object* v___x_4236_; uint8_t v_isShared_4237_; uint8_t v_isSharedCheck_4241_; 
lean_dec(v_tk_4129_);
lean_dec_ref(v_dec_4119_);
lean_dec(v_stx_4118_);
v___x_4233_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg();
v_a_4234_ = lean_ctor_get(v___x_4233_, 0);
v_isSharedCheck_4241_ = !lean_is_exclusive(v___x_4233_);
if (v_isSharedCheck_4241_ == 0)
{
v___x_4236_ = v___x_4233_;
v_isShared_4237_ = v_isSharedCheck_4241_;
goto v_resetjp_4235_;
}
else
{
lean_inc(v_a_4234_);
lean_dec(v___x_4233_);
v___x_4236_ = lean_box(0);
v_isShared_4237_ = v_isSharedCheck_4241_;
goto v_resetjp_4235_;
}
v_resetjp_4235_:
{
lean_object* v___x_4239_; 
if (v_isShared_4237_ == 0)
{
v___x_4239_ = v___x_4236_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4240_; 
v_reuseFailAlloc_4240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4240_, 0, v_a_4234_);
v___x_4239_ = v_reuseFailAlloc_4240_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
return v___x_4239_;
}
}
}
else
{
lean_object* v___x_4242_; lean_object* v_p_4243_; lean_object* v___x_4244_; uint8_t v___x_4245_; 
v___x_4242_ = lean_unsigned_to_nat(1u);
v_p_4243_ = l_Lean_Syntax_getArg(v_stx_4118_, v___x_4242_);
lean_dec(v_stx_4118_);
v___x_4244_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__3));
lean_inc(v_p_4243_);
v___x_4245_ = l_Lean_Syntax_isOfKind(v_p_4243_, v___x_4244_);
if (v___x_4245_ == 0)
{
v_as_4208_ = v_p_4243_;
v___y_4209_ = v_a_4120_;
v___y_4210_ = v_a_4121_;
v___y_4211_ = v_a_4122_;
v___y_4212_ = v_a_4123_;
v___y_4213_ = v_a_4124_;
v___y_4214_ = v_a_4125_;
v___y_4215_ = v_a_4126_;
goto v___jp_4207_;
}
else
{
lean_object* v_ref_4246_; uint8_t v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; 
v_ref_4246_ = lean_ctor_get(v_a_4125_, 2);
v___x_4247_ = 0;
v___x_4248_ = l_Lean_SourceInfo_fromRef(v_ref_4246_, v___x_4247_);
v___x_4249_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__40));
v___x_4250_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__41));
lean_inc(v___x_4248_);
v___x_4251_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4251_, 0, v___x_4248_);
lean_ctor_set(v___x_4251_, 1, v___x_4249_);
v___x_4252_ = l_Lean_Syntax_node2(v___x_4248_, v___x_4250_, v___x_4251_, v_p_4243_);
v_as_4208_ = v___x_4252_;
v___y_4209_ = v_a_4120_;
v___y_4210_ = v_a_4121_;
v___y_4211_ = v_a_4122_;
v___y_4212_ = v_a_4123_;
v___y_4213_ = v_a_4124_;
v___y_4214_ = v_a_4125_;
v___y_4215_ = v_a_4126_;
goto v___jp_4207_;
}
}
v___jp_4130_:
{
lean_object* v___x_4139_; lean_object* v___x_4140_; 
v___x_4139_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__1, &l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__1_once, _init_l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__1);
v___x_4140_ = l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0(v_tk_4129_, v___x_4139_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_);
if (lean_obj_tag(v___x_4140_) == 0)
{
lean_object* v___x_4141_; 
lean_dec_ref_known(v___x_4140_, 1);
v___x_4141_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_4119_, v_tk_4129_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_);
lean_dec(v_tk_4129_);
if (lean_obj_tag(v___x_4141_) == 0)
{
lean_object* v_toCold_4142_; lean_object* v_a_4143_; lean_object* v_ref_4144_; lean_object* v_quotContext_4145_; lean_object* v_currMacroScope_4146_; uint8_t v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; 
v_toCold_4142_ = lean_ctor_get(v___y_4137_, 0);
v_a_4143_ = lean_ctor_get(v___x_4141_, 0);
lean_inc(v_a_4143_);
lean_dec_ref_known(v___x_4141_, 1);
v_ref_4144_ = lean_ctor_get(v___y_4137_, 2);
v_quotContext_4145_ = lean_ctor_get(v_toCold_4142_, 8);
v_currMacroScope_4146_ = lean_ctor_get(v_toCold_4142_, 9);
v___x_4147_ = 0;
v___x_4148_ = l_Lean_SourceInfo_fromRef(v_ref_4144_, v___x_4147_);
v___x_4149_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__1));
v___x_4150_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__2));
lean_inc_n(v___x_4148_, 9);
v___x_4151_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4151_, 0, v___x_4148_);
lean_ctor_set(v___x_4151_, 1, v___x_4149_);
v___x_4152_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__3));
v___x_4153_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__3));
v___x_4154_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4154_, 0, v___x_4148_);
lean_ctor_set(v___x_4154_, 1, v___x_4153_);
v___x_4155_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__2));
v___x_4156_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_expandDefContract___closed__5, &l_Lean_Elab_Tactic_Do_expandDefContract___closed__5_once, _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__5);
v___x_4157_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__29));
lean_inc_n(v_currMacroScope_4146_, 2);
lean_inc_n(v_quotContext_4145_, 2);
v___x_4158_ = l_Lean_addMacroScope(v_quotContext_4145_, v___x_4157_, v_currMacroScope_4146_);
v___x_4159_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__4));
v___x_4160_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4160_, 0, v___x_4148_);
lean_ctor_set(v___x_4160_, 1, v___x_4156_);
lean_ctor_set(v___x_4160_, 2, v___x_4158_);
lean_ctor_set(v___x_4160_, 3, v___x_4159_);
v___x_4161_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_expandDefContract___closed__7, &l_Lean_Elab_Tactic_Do_expandDefContract___closed__7_once, _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__7);
v___x_4162_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__27));
v___x_4163_ = l_Lean_addMacroScope(v_quotContext_4145_, v___x_4162_, v_currMacroScope_4146_);
v___x_4164_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__5));
v___x_4165_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4165_, 0, v___x_4148_);
lean_ctor_set(v___x_4165_, 1, v___x_4161_);
lean_ctor_set(v___x_4165_, 2, v___x_4163_);
lean_ctor_set(v___x_4165_, 3, v___x_4164_);
v___x_4166_ = l_Lean_Syntax_node2(v___x_4148_, v___x_4155_, v___x_4160_, v___x_4165_);
v___x_4167_ = l_Lean_Syntax_node2(v___x_4148_, v___x_4152_, v___x_4154_, v___x_4166_);
v___x_4168_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__0));
v___x_4169_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4169_, 0, v___x_4148_);
lean_ctor_set(v___x_4169_, 1, v___x_4168_);
v___x_4170_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__7));
v___x_4171_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__9, &l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__9_once, _init_l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__9);
v___x_4172_ = l_Lean_Syntax_node1(v___x_4148_, v___x_4155_, v___y_4131_);
v___x_4173_ = l_Lean_Syntax_node2(v___x_4148_, v___x_4170_, v___x_4171_, v___x_4172_);
v___x_4174_ = l_Lean_Syntax_node4(v___x_4148_, v___x_4150_, v___x_4151_, v___x_4167_, v___x_4169_, v___x_4173_);
v___x_4175_ = l_Lean_Elab_Do_mkPUnit___redArg(v___y_4132_);
if (lean_obj_tag(v___x_4175_) == 0)
{
lean_object* v_a_4176_; lean_object* v___x_4177_; 
v_a_4176_ = lean_ctor_get(v___x_4175_, 0);
lean_inc(v_a_4176_);
lean_dec_ref_known(v___x_4175_, 1);
v___x_4177_ = l_Lean_Elab_Do_mkMonadApp(v_a_4176_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_);
if (lean_obj_tag(v___x_4177_) == 0)
{
lean_object* v_a_4178_; lean_object* v___x_4180_; uint8_t v_isShared_4181_; uint8_t v_isSharedCheck_4190_; 
v_a_4178_ = lean_ctor_get(v___x_4177_, 0);
v_isSharedCheck_4190_ = !lean_is_exclusive(v___x_4177_);
if (v_isSharedCheck_4190_ == 0)
{
v___x_4180_ = v___x_4177_;
v_isShared_4181_ = v_isSharedCheck_4190_;
goto v_resetjp_4179_;
}
else
{
lean_inc(v_a_4178_);
lean_dec(v___x_4177_);
v___x_4180_ = lean_box(0);
v_isShared_4181_ = v_isSharedCheck_4190_;
goto v_resetjp_4179_;
}
v_resetjp_4179_:
{
lean_object* v___x_4183_; 
if (v_isShared_4181_ == 0)
{
lean_ctor_set_tag(v___x_4180_, 1);
v___x_4183_ = v___x_4180_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v_a_4178_);
v___x_4183_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
uint8_t v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; 
v___x_4184_ = 1;
v___x_4185_ = lean_box(0);
v___x_4186_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_4174_, v___x_4183_, v___x_4184_, v___x_4184_, v___x_4185_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_);
if (lean_obj_tag(v___x_4186_) == 0)
{
lean_object* v_a_4187_; lean_object* v___x_4188_; 
v_a_4187_ = lean_ctor_get(v___x_4186_, 0);
lean_inc(v_a_4187_);
lean_dec_ref_known(v___x_4186_, 1);
v___x_4188_ = l_Lean_Elab_Do_DoElemCont_mkBindUnlessPure(v_a_4143_, v_a_4187_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_);
return v___x_4188_;
}
else
{
lean_dec(v_a_4143_);
return v___x_4186_;
}
}
}
}
else
{
lean_dec(v___x_4174_);
lean_dec(v_a_4143_);
return v___x_4177_;
}
}
else
{
lean_dec(v___x_4174_);
lean_dec(v_a_4143_);
return v___x_4175_;
}
}
else
{
lean_object* v_a_4191_; lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4198_; 
lean_dec(v___y_4131_);
v_a_4191_ = lean_ctor_get(v___x_4141_, 0);
v_isSharedCheck_4198_ = !lean_is_exclusive(v___x_4141_);
if (v_isSharedCheck_4198_ == 0)
{
v___x_4193_ = v___x_4141_;
v_isShared_4194_ = v_isSharedCheck_4198_;
goto v_resetjp_4192_;
}
else
{
lean_inc(v_a_4191_);
lean_dec(v___x_4141_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4198_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
lean_object* v___x_4196_; 
if (v_isShared_4194_ == 0)
{
v___x_4196_ = v___x_4193_;
goto v_reusejp_4195_;
}
else
{
lean_object* v_reuseFailAlloc_4197_; 
v_reuseFailAlloc_4197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4197_, 0, v_a_4191_);
v___x_4196_ = v_reuseFailAlloc_4197_;
goto v_reusejp_4195_;
}
v_reusejp_4195_:
{
return v___x_4196_;
}
}
}
}
else
{
lean_object* v_a_4199_; lean_object* v___x_4201_; uint8_t v_isShared_4202_; uint8_t v_isSharedCheck_4206_; 
lean_dec(v___y_4131_);
lean_dec(v_tk_4129_);
lean_dec_ref(v_dec_4119_);
v_a_4199_ = lean_ctor_get(v___x_4140_, 0);
v_isSharedCheck_4206_ = !lean_is_exclusive(v___x_4140_);
if (v_isSharedCheck_4206_ == 0)
{
v___x_4201_ = v___x_4140_;
v_isShared_4202_ = v_isSharedCheck_4206_;
goto v_resetjp_4200_;
}
else
{
lean_inc(v_a_4199_);
lean_dec(v___x_4140_);
v___x_4201_ = lean_box(0);
v_isShared_4202_ = v_isSharedCheck_4206_;
goto v_resetjp_4200_;
}
v_resetjp_4200_:
{
lean_object* v___x_4204_; 
if (v_isShared_4202_ == 0)
{
v___x_4204_ = v___x_4201_;
goto v_reusejp_4203_;
}
else
{
lean_object* v_reuseFailAlloc_4205_; 
v_reuseFailAlloc_4205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4205_, 0, v_a_4199_);
v___x_4204_ = v_reuseFailAlloc_4205_;
goto v_reusejp_4203_;
}
v_reusejp_4203_:
{
return v___x_4204_;
}
}
}
}
v___jp_4207_:
{
lean_object* v___x_4216_; lean_object* v_env_4217_; lean_object* v___x_4218_; uint8_t v___x_4219_; uint8_t v___x_4220_; 
v___x_4216_ = lean_st_ref_get(v___y_4215_);
v_env_4217_ = lean_ctor_get(v___x_4216_, 0);
lean_inc_ref(v_env_4217_);
lean_dec(v___x_4216_);
v___x_4218_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__8));
v___x_4219_ = 1;
v___x_4220_ = l_Lean_Environment_contains(v_env_4217_, v___x_4218_, v___x_4219_);
if (v___x_4220_ == 0)
{
lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v_a_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4230_; 
lean_dec(v_as_4208_);
lean_dec_ref(v_dec_4119_);
v___x_4221_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__11, &l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__11_once, _init_l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__11);
v___x_4222_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg(v_tk_4129_, v___x_4221_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_);
lean_dec(v_tk_4129_);
v_a_4223_ = lean_ctor_get(v___x_4222_, 0);
v_isSharedCheck_4230_ = !lean_is_exclusive(v___x_4222_);
if (v_isSharedCheck_4230_ == 0)
{
v___x_4225_ = v___x_4222_;
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_a_4223_);
lean_dec(v___x_4222_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
lean_object* v___x_4228_; 
if (v_isShared_4226_ == 0)
{
v___x_4228_ = v___x_4225_;
goto v_reusejp_4227_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v_a_4223_);
v___x_4228_ = v_reuseFailAlloc_4229_;
goto v_reusejp_4227_;
}
v_reusejp_4227_:
{
return v___x_4228_;
}
}
}
else
{
v___y_4131_ = v_as_4208_;
v___y_4132_ = v___y_4209_;
v___y_4133_ = v___y_4210_;
v___y_4134_ = v___y_4211_;
v___y_4135_ = v___y_4212_;
v___y_4136_ = v___y_4213_;
v___y_4137_ = v___y_4214_;
v___y_4138_ = v___y_4215_;
goto v___jp_4130_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___boxed(lean_object* v_stx_4253_, lean_object* v_dec_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_, lean_object* v_a_4257_, lean_object* v_a_4258_, lean_object* v_a_4259_, lean_object* v_a_4260_, lean_object* v_a_4261_, lean_object* v_a_4262_){
_start:
{
lean_object* v_res_4263_; 
v_res_4263_ = l_Lean_Elab_Tactic_Do_elabDoAssertion(v_stx_4253_, v_dec_4254_, v_a_4255_, v_a_4256_, v_a_4257_, v_a_4258_, v_a_4259_, v_a_4260_, v_a_4261_);
lean_dec(v_a_4261_);
lean_dec_ref(v_a_4260_);
lean_dec(v_a_4259_);
lean_dec_ref(v_a_4258_);
lean_dec(v_a_4257_);
lean_dec_ref(v_a_4256_);
lean_dec_ref(v_a_4255_);
return v_res_4263_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1(lean_object* v_00_u03b1_4264_, lean_object* v_ref_4265_, lean_object* v_msg_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_){
_start:
{
lean_object* v___x_4275_; 
v___x_4275_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg(v_ref_4265_, v_msg_4266_, v___y_4267_, v___y_4268_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_);
return v___x_4275_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___boxed(lean_object* v_00_u03b1_4276_, lean_object* v_ref_4277_, lean_object* v_msg_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_){
_start:
{
lean_object* v_res_4287_; 
v_res_4287_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1(v_00_u03b1_4276_, v_ref_4277_, v_msg_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_);
lean_dec(v___y_4285_);
lean_dec_ref(v___y_4284_);
lean_dec(v___y_4283_);
lean_dec_ref(v___y_4282_);
lean_dec(v___y_4281_);
lean_dec_ref(v___y_4280_);
lean_dec_ref(v___y_4279_);
lean_dec(v_ref_4277_);
return v_res_4287_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2(lean_object* v_00_u03b1_4288_, lean_object* v_msg_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_){
_start:
{
lean_object* v___x_4298_; 
v___x_4298_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2___redArg(v_msg_4289_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_);
return v___x_4298_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2___boxed(lean_object* v_00_u03b1_4299_, lean_object* v_msg_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_){
_start:
{
lean_object* v_res_4309_; 
v_res_4309_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2(v_00_u03b1_4299_, v_msg_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_);
lean_dec(v___y_4307_);
lean_dec_ref(v___y_4306_);
lean_dec(v___y_4305_);
lean_dec_ref(v___y_4304_);
lean_dec(v___y_4303_);
lean_dec_ref(v___y_4302_);
lean_dec_ref(v___y_4301_);
return v_res_4309_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2(lean_object* v_ref_4310_, lean_object* v_msgData_4311_, uint8_t v_severity_4312_, uint8_t v_isSilent_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_){
_start:
{
lean_object* v___x_4322_; 
v___x_4322_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg(v_ref_4310_, v_msgData_4311_, v_severity_4312_, v_isSilent_4313_, v___y_4317_, v___y_4318_, v___y_4319_, v___y_4320_);
return v___x_4322_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___boxed(lean_object* v_ref_4323_, lean_object* v_msgData_4324_, lean_object* v_severity_4325_, lean_object* v_isSilent_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_){
_start:
{
uint8_t v_severity_boxed_4335_; uint8_t v_isSilent_boxed_4336_; lean_object* v_res_4337_; 
v_severity_boxed_4335_ = lean_unbox(v_severity_4325_);
v_isSilent_boxed_4336_ = lean_unbox(v_isSilent_4326_);
v_res_4337_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2(v_ref_4323_, v_msgData_4324_, v_severity_boxed_4335_, v_isSilent_boxed_4336_, v___y_4327_, v___y_4328_, v___y_4329_, v___y_4330_, v___y_4331_, v___y_4332_, v___y_4333_);
lean_dec(v___y_4333_);
lean_dec_ref(v___y_4332_);
lean_dec(v___y_4331_);
lean_dec_ref(v___y_4330_);
lean_dec(v___y_4329_);
lean_dec_ref(v___y_4328_);
lean_dec_ref(v___y_4327_);
lean_dec(v_ref_4323_);
return v_res_4337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1(){
_start:
{
lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; 
v___x_4346_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4347_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__13));
v___x_4348_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___closed__1));
v___x_4349_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___boxed), 10, 0);
v___x_4350_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4346_, v___x_4347_, v___x_4348_, v___x_4349_);
return v___x_4350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___boxed(lean_object* v_a_4351_){
_start:
{
lean_object* v_res_4352_; 
v_res_4352_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1();
return v_res_4352_;
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
