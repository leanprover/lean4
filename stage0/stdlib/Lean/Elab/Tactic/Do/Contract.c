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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0_spec__0(lean_object* v_as_1_, size_t v_i_2_, size_t v_stop_3_, lean_object* v_b_4_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1_ = stack[0].m_obj;
size_t v_i_2_ = stack[1].m_num;
size_t v_stop_3_ = stack[2].m_num;
lean_object* v_b_4_ = stack[3].m_obj;
lean_object* v_res_14_;
v_res_14_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0_spec__0(v_as_1_, v_i_2_, v_stop_3_, v_b_4_);
stack->m_obj
 = v_res_14_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0_spec__0___boxed(lean_object* v_as_15_, lean_object* v_i_16_, lean_object* v_stop_17_, lean_object* v_b_18_){
_start:
{
size_t v_i_boxed_19_; size_t v_stop_boxed_20_; lean_object* v_res_21_; 
v_i_boxed_19_ = lean_unbox_usize(v_i_16_);
lean_dec(v_i_16_);
v_stop_boxed_20_ = lean_unbox_usize(v_stop_17_);
lean_dec(v_stop_17_);
v_res_21_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0_spec__0(v_as_15_, v_i_boxed_19_, v_stop_boxed_20_, v_b_18_);
lean_dec_ref(v_as_15_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0(lean_object* v_as_24_, lean_object* v_start_25_, lean_object* v_stop_26_){
_start:
{
lean_object* v___x_27_; uint8_t v___x_28_; 
v___x_27_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0___closed__0));
v___x_28_ = lean_nat_dec_lt(v_start_25_, v_stop_26_);
if (v___x_28_ == 0)
{
return v___x_27_;
}
else
{
lean_object* v___x_29_; uint8_t v___x_30_; 
v___x_29_ = lean_array_get_size(v_as_24_);
v___x_30_ = lean_nat_dec_le(v_stop_26_, v___x_29_);
if (v___x_30_ == 0)
{
uint8_t v___x_31_; 
v___x_31_ = lean_nat_dec_lt(v_start_25_, v___x_29_);
if (v___x_31_ == 0)
{
return v___x_27_;
}
else
{
size_t v___x_32_; size_t v___x_33_; lean_object* v___x_34_; 
v___x_32_ = lean_usize_of_nat(v_start_25_);
v___x_33_ = lean_usize_of_nat(v___x_29_);
v___x_34_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0_spec__0(v_as_24_, v___x_32_, v___x_33_, v___x_27_);
return v___x_34_;
}
}
else
{
size_t v___x_35_; size_t v___x_36_; lean_object* v___x_37_; 
v___x_35_ = lean_usize_of_nat(v_start_25_);
v___x_36_ = lean_usize_of_nat(v_stop_26_);
v___x_37_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0_spec__0(v_as_24_, v___x_35_, v___x_36_, v___x_27_);
return v___x_37_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0___boxed(lean_object* v_as_38_, lean_object* v_start_39_, lean_object* v_stop_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0(v_as_38_, v_start_39_, v_stop_40_);
lean_dec(v_stop_40_);
lean_dec(v_start_39_);
lean_dec_ref(v_as_38_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_contractBinderIdents(lean_object* v_binder_51_){
_start:
{
lean_object* v___x_52_; uint8_t v___x_53_; 
v___x_52_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__4));
lean_inc(v_binder_51_);
v___x_53_ = l_Lean_Syntax_isOfKind(v_binder_51_, v___x_52_);
if (v___x_53_ == 0)
{
uint8_t v___x_54_; 
v___x_54_ = l_Lean_Syntax_isIdent(v_binder_51_);
if (v___x_54_ == 0)
{
lean_object* v___x_55_; 
lean_dec(v_binder_51_);
v___x_55_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0___closed__0));
return v___x_55_;
}
else
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_56_ = lean_unsigned_to_nat(1u);
v___x_57_ = lean_mk_empty_array_with_capacity(v___x_56_);
v___x_58_ = lean_array_push(v___x_57_, v_binder_51_);
return v___x_58_;
}
}
else
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
v___x_59_ = lean_unsigned_to_nat(0u);
v___x_60_ = lean_unsigned_to_nat(1u);
v___x_61_ = l_Lean_Syntax_getArg(v_binder_51_, v___x_60_);
v___x_66_ = lean_unsigned_to_nat(2u);
v___x_67_ = l_Lean_Syntax_getArg(v_binder_51_, v___x_66_);
v___x_68_ = l_Lean_Syntax_isNone(v___x_67_);
if (v___x_68_ == 0)
{
uint8_t v___x_69_; 
v___x_69_ = l_Lean_Syntax_matchesNull(v___x_67_, v___x_66_);
if (v___x_69_ == 0)
{
uint8_t v___x_70_; 
lean_dec(v___x_61_);
v___x_70_ = l_Lean_Syntax_isIdent(v_binder_51_);
if (v___x_70_ == 0)
{
lean_object* v___x_71_; 
lean_dec(v_binder_51_);
v___x_71_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0___closed__0));
return v___x_71_;
}
else
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = lean_mk_empty_array_with_capacity(v___x_60_);
v___x_73_ = lean_array_push(v___x_72_, v_binder_51_);
return v___x_73_;
}
}
else
{
lean_dec(v_binder_51_);
goto v___jp_62_;
}
}
else
{
lean_dec(v___x_67_);
lean_dec(v_binder_51_);
goto v___jp_62_;
}
v___jp_62_:
{
lean_object* v_ids_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v_ids_63_ = l_Lean_Syntax_getArgs(v___x_61_);
lean_dec(v___x_61_);
v___x_64_ = lean_array_get_size(v_ids_63_);
v___x_65_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_contractBinderIdents_spec__0(v_ids_63_, v___x_59_, v___x_64_);
lean_dec_ref(v_ids_63_);
return v___x_65_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f(lean_object* v_v_108_){
_start:
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__2));
lean_inc(v_v_108_);
v___x_110_ = l_Lean_Syntax_isOfKind(v_v_108_, v___x_109_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_111_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__4));
lean_inc(v_v_108_);
v___x_112_ = l_Lean_Syntax_isOfKind(v_v_108_, v___x_111_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_113_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__6));
v___x_114_ = l_Lean_Syntax_isOfKind(v_v_108_, v___x_113_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; 
v___x_115_ = lean_box(0);
return v___x_115_;
}
else
{
lean_object* v___x_116_; 
v___x_116_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__9));
return v___x_116_;
}
}
else
{
lean_object* v___x_117_; 
lean_dec(v_v_108_);
v___x_117_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__10));
return v___x_117_;
}
}
else
{
lean_object* v___x_118_; 
lean_dec(v_v_108_);
v___x_118_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__12));
return v___x_118_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_getPath(lean_object* v_s_119_, lean_object* v_x_120_){
_start:
{
if (lean_obj_tag(v_x_120_) == 0)
{
return v_s_119_;
}
else
{
lean_object* v_head_121_; lean_object* v_tail_122_; lean_object* v___x_123_; 
v_head_121_ = lean_ctor_get(v_x_120_, 0);
v_tail_122_ = lean_ctor_get(v_x_120_, 1);
v___x_123_ = l_Lean_Syntax_getArg(v_s_119_, v_head_121_);
lean_dec(v_s_119_);
v_s_119_ = v___x_123_;
v_x_120_ = v_tail_122_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_getPath___boxed(lean_object* v_s_125_, lean_object* v_x_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_getPath(v_s_125_, v_x_126_);
lean_dec(v_x_126_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_setPath(lean_object* v_s_128_, lean_object* v_x_129_, lean_object* v_x_130_){
_start:
{
if (lean_obj_tag(v_x_129_) == 0)
{
lean_dec(v_s_128_);
lean_inc(v_x_130_);
return v_x_130_;
}
else
{
lean_object* v_head_131_; lean_object* v_tail_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v_head_131_ = lean_ctor_get(v_x_129_, 0);
v_tail_132_ = lean_ctor_get(v_x_129_, 1);
v___x_133_ = l_Lean_Syntax_getArg(v_s_128_, v_head_131_);
v___x_134_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_setPath(v___x_133_, v_tail_132_, v_x_130_);
v___x_135_ = l_Lean_Syntax_setArg(v_s_128_, v_head_131_, v___x_134_);
return v___x_135_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_setPath___boxed(lean_object* v_s_136_, lean_object* v_x_137_, lean_object* v_x_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_setPath(v_s_136_, v_x_137_, v_x_138_);
lean_dec(v_x_138_);
lean_dec(v_x_137_);
return v_res_139_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0(lean_object* v_as_143_, size_t v_sz_144_, size_t v_i_145_, lean_object* v_b_146_){
_start:
{
lean_object* v_a_148_; uint8_t v___x_152_; 
v___x_152_ = lean_usize_dec_lt(v_i_145_, v_sz_144_);
if (v___x_152_ == 0)
{
return v_b_146_;
}
else
{
lean_object* v_fst_153_; lean_object* v_snd_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_173_; 
v_fst_153_ = lean_ctor_get(v_b_146_, 0);
v_snd_154_ = lean_ctor_get(v_b_146_, 1);
v_isSharedCheck_173_ = !lean_is_exclusive(v_b_146_);
if (v_isSharedCheck_173_ == 0)
{
v___x_156_ = v_b_146_;
v_isShared_157_ = v_isSharedCheck_173_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_snd_154_);
lean_inc(v_fst_153_);
lean_dec(v_b_146_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_173_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v_a_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v_a_158_ = lean_array_uget_borrowed(v_as_143_, v_i_145_);
v___x_159_ = lean_unsigned_to_nat(1u);
v___x_160_ = l_Lean_Syntax_getArg(v_a_158_, v___x_159_);
v___x_161_ = l_Lean_Syntax_getId(v___x_160_);
lean_dec(v___x_160_);
v___x_162_ = l_Lean_Name_eraseMacroScopes(v___x_161_);
lean_dec(v___x_161_);
v___x_163_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0___closed__1));
v___x_164_ = lean_name_eq(v___x_162_, v___x_163_);
lean_dec(v___x_162_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; lean_object* v___x_167_; 
lean_inc(v_a_158_);
v___x_165_ = lean_array_push(v_snd_154_, v_a_158_);
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 1, v___x_165_);
v___x_167_ = v___x_156_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_fst_153_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v___x_165_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
v_a_148_ = v___x_167_;
goto v___jp_147_;
}
}
else
{
lean_object* v___x_169_; lean_object* v___x_171_; 
lean_inc(v_a_158_);
v___x_169_ = lean_array_push(v_fst_153_, v_a_158_);
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 0, v___x_169_);
v___x_171_ = v___x_156_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_169_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v_snd_154_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
v_a_148_ = v___x_171_;
goto v___jp_147_;
}
}
}
}
v___jp_147_:
{
size_t v___x_149_; size_t v___x_150_; 
v___x_149_ = ((size_t)1ULL);
v___x_150_ = lean_usize_add(v_i_145_, v___x_149_);
v_i_145_ = v___x_150_;
v_b_146_ = v_a_148_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_143_ = stack[0].m_obj;
size_t v_sz_144_ = stack[1].m_num;
size_t v_i_145_ = stack[2].m_num;
lean_object* v_b_146_ = stack[3].m_obj;
lean_object* v_res_174_;
v_res_174_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0(v_as_143_, v_sz_144_, v_i_145_, v_b_146_);
stack->m_obj
 = v_res_174_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0___boxed(lean_object* v_as_175_, lean_object* v_sz_176_, lean_object* v_i_177_, lean_object* v_b_178_){
_start:
{
size_t v_sz_boxed_179_; size_t v_i_boxed_180_; lean_object* v_res_181_; 
v_sz_boxed_179_ = lean_unbox_usize(v_sz_176_);
lean_dec(v_sz_176_);
v_i_boxed_180_ = lean_unbox_usize(v_i_177_);
lean_dec(v_i_177_);
v_res_181_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0(v_as_175_, v_sz_boxed_179_, v_i_boxed_180_, v_b_178_);
lean_dec_ref(v_as_175_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection(lean_object* v_v_188_, lean_object* v_a_189_, lean_object* v_a_190_){
_start:
{
lean_object* v___x_191_; 
lean_inc(v_v_188_);
v___x_191_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f(v_v_188_);
if (lean_obj_tag(v___x_191_) == 1)
{
lean_object* v_val_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_269_; 
v_val_192_ = lean_ctor_get(v___x_191_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_269_ == 0)
{
v___x_194_ = v___x_191_;
v_isShared_195_ = v_isSharedCheck_269_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_val_192_);
lean_dec(v___x_191_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_269_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v_optWd_196_; uint8_t v___x_197_; 
lean_inc(v_v_188_);
v_optWd_196_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_getPath(v_v_188_, v_val_192_);
v___x_197_ = l_Lean_Syntax_isNone(v_optWd_196_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; lean_object* v_wd_199_; lean_object* v___x_200_; lean_object* v_optWf_201_; uint8_t v___x_202_; 
v___x_198_ = lean_unsigned_to_nat(0u);
v_wd_199_ = l_Lean_Syntax_getArg(v_optWd_196_, v___x_198_);
lean_dec(v_optWd_196_);
v___x_200_ = lean_unsigned_to_nat(2u);
v_optWf_201_ = l_Lean_Syntax_getArg(v_wd_199_, v___x_200_);
v___x_202_ = l_Lean_Syntax_isNone(v_optWf_201_);
if (v___x_202_ == 0)
{
lean_object* v_wf_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; size_t v_sz_207_; size_t v___x_208_; lean_object* v___x_209_; lean_object* v_fst_210_; lean_object* v_snd_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_262_; 
v_wf_203_ = l_Lean_Syntax_getArg(v_optWf_201_, v___x_198_);
lean_dec(v_optWf_201_);
v___x_204_ = l_Lean_Syntax_getArg(v_wf_203_, v___x_200_);
v___x_205_ = l_Lean_Syntax_getArgs(v___x_204_);
lean_dec(v___x_204_);
v___x_206_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__0));
v_sz_207_ = lean_array_size(v___x_205_);
v___x_208_ = ((size_t)0ULL);
v___x_209_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0(v___x_205_, v_sz_207_, v___x_208_, v___x_206_);
lean_dec_ref(v___x_205_);
v_fst_210_ = lean_ctor_get(v___x_209_, 0);
v_snd_211_ = lean_ctor_get(v___x_209_, 1);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_262_ == 0)
{
v___x_213_ = v___x_209_;
v_isShared_214_ = v_isSharedCheck_262_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_snd_211_);
lean_inc(v_fst_210_);
lean_dec(v___x_209_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_262_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_215_ = lean_array_get_size(v_fst_210_);
v___x_216_ = lean_nat_dec_eq(v___x_215_, v___x_198_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; lean_object* v___y_219_; lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_217_ = lean_box(0);
v___x_242_ = lean_unsigned_to_nat(1u);
v___x_243_ = lean_nat_dec_lt(v___x_242_, v___x_215_);
if (v___x_243_ == 0)
{
v___y_219_ = v_a_190_;
goto v___jp_218_;
}
else
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_244_ = lean_array_fget_borrowed(v_fst_210_, v___x_242_);
v___x_245_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__3));
v___x_246_ = l_Lean_Macro_throwErrorAt___redArg(v___x_244_, v___x_245_, v_a_189_, v_a_190_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v_a_247_; 
v_a_247_ = lean_ctor_get(v___x_246_, 1);
lean_inc(v_a_247_);
lean_dec_ref_known(v___x_246_, 2);
v___y_219_ = v_a_247_;
goto v___jp_218_;
}
else
{
lean_object* v_a_248_; lean_object* v_a_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_256_; 
lean_del_object(v___x_213_);
lean_dec(v_snd_211_);
lean_dec(v_fst_210_);
lean_dec(v_wf_203_);
lean_dec(v_wd_199_);
lean_del_object(v___x_194_);
lean_dec(v_val_192_);
lean_dec(v_v_188_);
v_a_248_ = lean_ctor_get(v___x_246_, 0);
v_a_249_ = lean_ctor_get(v___x_246_, 1);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_256_ == 0)
{
v___x_251_ = v___x_246_;
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_a_249_);
lean_inc(v_a_248_);
lean_dec(v___x_246_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_254_; 
if (v_isShared_252_ == 0)
{
v___x_254_ = v___x_251_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_a_248_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v_a_249_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
}
v___jp_218_:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v_wf_x27_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_220_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__2));
v___x_221_ = lean_box(2);
v___x_222_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set(v___x_222_, 1, v___x_220_);
lean_ctor_set(v___x_222_, 2, v_snd_211_);
v_wf_x27_223_ = l_Lean_Syntax_setArg(v_wf_203_, v___x_200_, v___x_222_);
v___x_224_ = lean_array_get(v___x_217_, v_fst_210_, v___x_198_);
lean_dec(v_fst_210_);
v___x_225_ = lean_unsigned_to_nat(3u);
v___x_226_ = l_Lean_Syntax_getArg(v___x_224_, v___x_225_);
lean_dec(v___x_224_);
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 0, v___x_226_);
v___x_228_ = v___x_194_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_226_);
v___x_228_ = v_reuseFailAlloc_241_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_238_; 
v___x_229_ = lean_unsigned_to_nat(1u);
v___x_230_ = lean_mk_empty_array_with_capacity(v___x_229_);
lean_inc_ref(v___x_230_);
v___x_231_ = lean_array_push(v___x_230_, v_wf_x27_223_);
v___x_232_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_232_, 0, v___x_221_);
lean_ctor_set(v___x_232_, 1, v___x_220_);
lean_ctor_set(v___x_232_, 2, v___x_231_);
v___x_233_ = l_Lean_Syntax_setArg(v_wd_199_, v___x_200_, v___x_232_);
v___x_234_ = lean_array_push(v___x_230_, v___x_233_);
v___x_235_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_235_, 0, v___x_221_);
lean_ctor_set(v___x_235_, 1, v___x_220_);
lean_ctor_set(v___x_235_, 2, v___x_234_);
v___x_236_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_setPath(v_v_188_, v_val_192_, v___x_235_);
lean_dec_ref_known(v___x_235_, 3);
lean_dec(v_val_192_);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 1, v___x_236_);
lean_ctor_set(v___x_213_, 0, v___x_228_);
v___x_238_ = v___x_213_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_228_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v___x_236_);
v___x_238_ = v_reuseFailAlloc_240_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_239_; 
v___x_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set(v___x_239_, 1, v___y_219_);
return v___x_239_;
}
}
}
}
else
{
lean_object* v___x_257_; lean_object* v___x_259_; 
lean_dec(v_snd_211_);
lean_dec(v_fst_210_);
lean_dec(v_wf_203_);
lean_dec(v_wd_199_);
lean_del_object(v___x_194_);
lean_dec(v_val_192_);
v___x_257_ = lean_box(0);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 1, v_v_188_);
lean_ctor_set(v___x_213_, 0, v___x_257_);
v___x_259_ = v___x_213_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_257_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_v_188_);
v___x_259_ = v_reuseFailAlloc_261_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
lean_object* v___x_260_; 
v___x_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
lean_ctor_set(v___x_260_, 1, v_a_190_);
return v___x_260_;
}
}
}
}
else
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
lean_dec(v_optWf_201_);
lean_dec(v_wd_199_);
lean_del_object(v___x_194_);
lean_dec(v_val_192_);
v___x_263_ = lean_box(0);
v___x_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
lean_ctor_set(v___x_264_, 1, v_v_188_);
v___x_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set(v___x_265_, 1, v_a_190_);
return v___x_265_;
}
}
else
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
lean_dec(v_optWd_196_);
lean_del_object(v___x_194_);
lean_dec(v_val_192_);
v___x_266_ = lean_box(0);
v___x_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
lean_ctor_set(v___x_267_, 1, v_v_188_);
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
lean_ctor_set(v___x_268_, 1, v_a_190_);
return v___x_268_;
}
}
}
else
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
lean_dec(v___x_191_);
v___x_270_ = lean_box(0);
v___x_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
lean_ctor_set(v___x_271_, 1, v_v_188_);
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_ctor_set(v___x_272_, 1, v_a_190_);
return v___x_272_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___boxed(lean_object* v_v_273_, lean_object* v_a_274_, lean_object* v_a_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection(v_v_273_, v_a_274_, v_a_275_);
lean_dec_ref(v_a_274_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice(lean_object* v_val_287_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_288_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__1));
v___x_289_ = l_Lean_Syntax_getArgs(v_val_287_);
v___x_290_ = lean_array_pop(v___x_289_);
v___x_291_ = lean_box(2);
v___x_292_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__2));
v___x_293_ = lean_array_push(v___x_290_, v___x_292_);
v___x_294_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_294_, 0, v___x_291_);
lean_ctor_set(v___x_294_, 1, v___x_288_);
lean_ctor_set(v___x_294_, 2, v___x_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___boxed(lean_object* v_val_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice(v_val_295_);
lean_dec(v_val_295_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___lam__0(lean_object* v_____do__lift_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
uint8_t v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_300_ = 0;
v___x_301_ = l_Lean_SourceInfo_fromRef(v_____do__lift_297_, v___x_300_);
v___x_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
lean_ctor_set(v___x_302_, 1, v___y_299_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___lam__0___boxed(lean_object* v_____do__lift_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_Elab_Tactic_Do_expandDefContract___lam__0(v_____do__lift_303_, v___y_304_, v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v_____do__lift_303_);
return v_res_306_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__3(lean_object* v_as_307_, size_t v_i_308_, size_t v_stop_309_, lean_object* v_b_310_){
_start:
{
uint8_t v___x_311_; 
v___x_311_ = lean_usize_dec_eq(v_i_308_, v_stop_309_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; size_t v___x_315_; size_t v___x_316_; 
v___x_312_ = lean_array_uget_borrowed(v_as_307_, v_i_308_);
lean_inc(v___x_312_);
v___x_313_ = l_Lean_Elab_Tactic_Do_contractBinderIdents(v___x_312_);
v___x_314_ = l_Array_append___redArg(v_b_310_, v___x_313_);
lean_dec_ref(v___x_313_);
v___x_315_ = ((size_t)1ULL);
v___x_316_ = lean_usize_add(v_i_308_, v___x_315_);
v_i_308_ = v___x_316_;
v_b_310_ = v___x_314_;
goto _start;
}
else
{
return v_b_310_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_307_ = stack[0].m_obj;
size_t v_i_308_ = stack[1].m_num;
size_t v_stop_309_ = stack[2].m_num;
lean_object* v_b_310_ = stack[3].m_obj;
lean_object* v_res_318_;
v_res_318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__3(v_as_307_, v_i_308_, v_stop_309_, v_b_310_);
stack->m_obj
 = v_res_318_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__3___boxed(lean_object* v_as_319_, lean_object* v_i_320_, lean_object* v_stop_321_, lean_object* v_b_322_){
_start:
{
size_t v_i_boxed_323_; size_t v_stop_boxed_324_; lean_object* v_res_325_; 
v_i_boxed_323_ = lean_unbox_usize(v_i_320_);
lean_dec(v_i_320_);
v_stop_boxed_324_ = lean_unbox_usize(v_stop_321_);
lean_dec(v_stop_321_);
v_res_325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__3(v_as_319_, v_i_boxed_323_, v_stop_boxed_324_, v_b_322_);
lean_dec_ref(v_as_319_);
return v_res_325_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__0(size_t v_sz_326_, size_t v_i_327_, lean_object* v_bs_328_){
_start:
{
uint8_t v___x_329_; 
v___x_329_ = lean_usize_dec_lt(v_i_327_, v_sz_326_);
if (v___x_329_ == 0)
{
return v_bs_328_;
}
else
{
lean_object* v_v_330_; lean_object* v___x_331_; lean_object* v_bs_x27_332_; size_t v___x_333_; size_t v___x_334_; lean_object* v___x_335_; 
v_v_330_ = lean_array_uget(v_bs_328_, v_i_327_);
v___x_331_ = lean_unsigned_to_nat(0u);
v_bs_x27_332_ = lean_array_uset(v_bs_328_, v_i_327_, v___x_331_);
v___x_333_ = ((size_t)1ULL);
v___x_334_ = lean_usize_add(v_i_327_, v___x_333_);
v___x_335_ = lean_array_uset(v_bs_x27_332_, v_i_327_, v_v_330_);
v_i_327_ = v___x_334_;
v_bs_328_ = v___x_335_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_326_ = stack[0].m_num;
size_t v_i_327_ = stack[1].m_num;
lean_object* v_bs_328_ = stack[2].m_obj;
lean_object* v_res_337_;
v_res_337_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__0(v_sz_326_, v_i_327_, v_bs_328_);
stack->m_obj
 = v_res_337_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__0___boxed(lean_object* v_sz_338_, lean_object* v_i_339_, lean_object* v_bs_340_){
_start:
{
size_t v_sz_boxed_341_; size_t v_i_boxed_342_; lean_object* v_res_343_; 
v_sz_boxed_341_ = lean_unbox_usize(v_sz_338_);
lean_dec(v_sz_338_);
v_i_boxed_342_ = lean_unbox_usize(v_i_339_);
lean_dec(v_i_339_);
v_res_343_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__0(v_sz_boxed_341_, v_i_boxed_342_, v_bs_340_);
return v_res_343_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__11(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__10));
v___x_372_ = l_Lean_mkCIdent(v___x_371_);
return v___x_372_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__20(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__19));
v___x_391_ = l_String_toRawSubstring_x27(v___x_390_);
return v___x_391_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2(lean_object* v_as_445_, size_t v_i_446_, size_t v_stop_447_, lean_object* v_b_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
uint8_t v___x_451_; 
v___x_451_ = lean_usize_dec_eq(v_i_446_, v_stop_447_);
if (v___x_451_ == 0)
{
lean_object* v_quotContext_452_; lean_object* v_currMacroScope_453_; lean_object* v_ref_454_; size_t v___x_455_; size_t v___x_456_; lean_object* v___y_458_; lean_object* v___x_462_; lean_object* v___x_463_; uint8_t v___x_464_; 
v_quotContext_452_ = lean_ctor_get(v___y_449_, 1);
v_currMacroScope_453_ = lean_ctor_get(v___y_449_, 2);
v_ref_454_ = lean_ctor_get(v___y_449_, 5);
v___x_455_ = ((size_t)1ULL);
v___x_456_ = lean_usize_sub(v_i_446_, v___x_455_);
v___x_462_ = lean_array_uget_borrowed(v_as_445_, v___x_456_);
v___x_463_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__1));
lean_inc(v___x_462_);
v___x_464_ = l_Lean_Syntax_isOfKind(v___x_462_, v___x_463_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; 
lean_dec(v_b_448_);
v___x_465_ = l_Lean_Macro_throwUnsupported___redArg(v___y_450_);
v___y_458_ = v___x_465_;
goto v___jp_457_;
}
else
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_466_ = lean_unsigned_to_nat(1u);
v___x_467_ = l_Lean_Syntax_getArg(v___x_462_, v___x_466_);
v___x_468_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__3));
lean_inc(v___x_467_);
v___x_469_ = l_Lean_Syntax_isOfKind(v___x_467_, v___x_468_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; 
lean_dec(v___x_467_);
lean_dec(v_b_448_);
v___x_470_ = l_Lean_Macro_throwUnsupported___redArg(v___y_450_);
v___y_458_ = v___x_470_;
goto v___jp_457_;
}
else
{
lean_object* v_ref_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v_ref_471_ = l_Lean_replaceRef(v___x_462_, v_ref_454_);
v___x_472_ = l_Lean_SourceInfo_fromRef(v_ref_471_, v___x_451_);
lean_dec(v_ref_471_);
v___x_473_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__7));
v___x_474_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__11, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__11);
v___x_475_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__2));
v___x_476_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__13));
v___x_477_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__15));
v___x_478_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__16));
lean_inc_n(v___x_472_, 9);
v___x_479_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_479_, 0, v___x_472_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
v___x_480_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__18));
v___x_481_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__20, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__20_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__20);
v___x_482_ = lean_box(0);
lean_inc(v_currMacroScope_453_);
lean_inc(v_quotContext_452_);
v___x_483_ = l_Lean_addMacroScope(v_quotContext_452_, v___x_482_, v_currMacroScope_453_);
v___x_484_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__39));
v___x_485_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_485_, 0, v___x_472_);
lean_ctor_set(v___x_485_, 1, v___x_481_);
lean_ctor_set(v___x_485_, 2, v___x_483_);
lean_ctor_set(v___x_485_, 3, v___x_484_);
v___x_486_ = l_Lean_Syntax_node1(v___x_472_, v___x_480_, v___x_485_);
v___x_487_ = l_Lean_Syntax_node2(v___x_472_, v___x_477_, v___x_479_, v___x_486_);
v___x_488_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__40));
v___x_489_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__41));
v___x_490_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_472_);
lean_ctor_set(v___x_490_, 1, v___x_488_);
v___x_491_ = l_Lean_Syntax_node2(v___x_472_, v___x_489_, v___x_490_, v___x_467_);
v___x_492_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__42));
v___x_493_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_472_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
v___x_494_ = l_Lean_Syntax_node3(v___x_472_, v___x_476_, v___x_487_, v___x_491_, v___x_493_);
v___x_495_ = l_Lean_Syntax_node2(v___x_472_, v___x_475_, v___x_494_, v_b_448_);
v___x_496_ = l_Lean_Syntax_node2(v___x_472_, v___x_473_, v___x_474_, v___x_495_);
v_i_446_ = v___x_456_;
v_b_448_ = v___x_496_;
goto _start;
}
}
v___jp_457_:
{
if (lean_obj_tag(v___y_458_) == 0)
{
lean_object* v_a_459_; lean_object* v_a_460_; 
v_a_459_ = lean_ctor_get(v___y_458_, 0);
lean_inc(v_a_459_);
v_a_460_ = lean_ctor_get(v___y_458_, 1);
lean_inc(v_a_460_);
lean_dec_ref_known(v___y_458_, 2);
v_i_446_ = v___x_456_;
v_b_448_ = v_a_459_;
v___y_450_ = v_a_460_;
goto _start;
}
else
{
return v___y_458_;
}
}
}
else
{
lean_object* v___x_498_; 
v___x_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_498_, 0, v_b_448_);
lean_ctor_set(v___x_498_, 1, v___y_450_);
return v___x_498_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_445_ = stack[0].m_obj;
size_t v_i_446_ = stack[1].m_num;
size_t v_stop_447_ = stack[2].m_num;
lean_object* v_b_448_ = stack[3].m_obj;
lean_object* v___y_449_ = stack[4].m_obj;
lean_object* v___y_450_ = stack[5].m_obj;
lean_object* v_res_499_;
v_res_499_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2(v_as_445_, v_i_446_, v_stop_447_, v_b_448_, v___y_449_, v___y_450_);
stack->m_obj
 = v_res_499_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___boxed(lean_object* v_as_500_, lean_object* v_i_501_, lean_object* v_stop_502_, lean_object* v_b_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
size_t v_i_boxed_506_; size_t v_stop_boxed_507_; lean_object* v_res_508_; 
v_i_boxed_506_ = lean_unbox_usize(v_i_501_);
lean_dec(v_i_501_);
v_stop_boxed_507_ = lean_unbox_usize(v_stop_502_);
lean_dec(v_stop_502_);
v_res_508_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2(v_as_500_, v_i_boxed_506_, v_stop_boxed_507_, v_b_503_, v___y_504_, v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec_ref(v_as_500_);
return v_res_508_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__1(size_t v_sz_509_, size_t v_i_510_, lean_object* v_bs_511_){
_start:
{
uint8_t v___x_512_; 
v___x_512_ = lean_usize_dec_lt(v_i_510_, v_sz_509_);
if (v___x_512_ == 0)
{
return v_bs_511_;
}
else
{
lean_object* v_v_513_; lean_object* v___x_514_; lean_object* v_bs_x27_515_; size_t v___x_516_; size_t v___x_517_; lean_object* v___x_518_; 
v_v_513_ = lean_array_uget(v_bs_511_, v_i_510_);
v___x_514_ = lean_unsigned_to_nat(0u);
v_bs_x27_515_ = lean_array_uset(v_bs_511_, v_i_510_, v___x_514_);
v___x_516_ = ((size_t)1ULL);
v___x_517_ = lean_usize_add(v_i_510_, v___x_516_);
v___x_518_ = lean_array_uset(v_bs_x27_515_, v_i_510_, v_v_513_);
v_i_510_ = v___x_517_;
v_bs_511_ = v___x_518_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_509_ = stack[0].m_num;
size_t v_i_510_ = stack[1].m_num;
lean_object* v_bs_511_ = stack[2].m_obj;
lean_object* v_res_520_;
v_res_520_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__1(v_sz_509_, v_i_510_, v_bs_511_);
stack->m_obj
 = v_res_520_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__1___boxed(lean_object* v_sz_521_, lean_object* v_i_522_, lean_object* v_bs_523_){
_start:
{
size_t v_sz_boxed_524_; size_t v_i_boxed_525_; lean_object* v_res_526_; 
v_sz_boxed_524_ = lean_unbox_usize(v_sz_521_);
lean_dec(v_sz_521_);
v_i_boxed_525_ = lean_unbox_usize(v_i_522_);
lean_dec(v_i_522_);
v_res_526_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__1(v_sz_boxed_524_, v_i_boxed_525_, v_bs_523_);
return v_res_526_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__5(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__4));
v___x_533_ = l_String_toRawSubstring_x27(v___x_532_);
return v___x_533_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__7(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__6));
v___x_536_ = l_String_toRawSubstring_x27(v___x_535_);
return v___x_536_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__49(void){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__48));
v___x_580_ = l_Lean_mkAtom(v___x_579_);
return v___x_580_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__53(void){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l_Array_mkArray0___redArg();
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_expandDefContract(lean_object* v_stx_634_, lean_object* v_a_635_, lean_object* v_a_636_){
_start:
{
lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v_specTac_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_873_; size_t v___y_874_; lean_object* v_a_875_; lean_object* v_a_876_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; size_t v___y_990_; lean_object* v_post_991_; lean_object* v___y_992_; lean_object* v_ref_993_; lean_object* v___y_994_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1039_; lean_object* v___y_1040_; lean_object* v___y_1041_; lean_object* v___y_1042_; size_t v___y_1043_; lean_object* v_post_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; lean_object* v___x_1048_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; lean_object* v___y_1057_; uint8_t v___y_1058_; lean_object* v___y_1059_; lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v___y_1062_; lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; size_t v___y_1067_; lean_object* v_pre_1068_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1134_; lean_object* v___y_1135_; lean_object* v___y_1136_; lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; uint8_t v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v___y_1149_; size_t v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1184_; lean_object* v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; uint8_t v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1194_; lean_object* v___y_1195_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1199_; lean_object* v___y_1200_; lean_object* v___y_1201_; lean_object* v___y_1202_; lean_object* v___y_1203_; lean_object* v_decl_1213_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v___y_1223_; lean_object* v___y_1224_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v___y_1281_; lean_object* v___y_1282_; lean_object* v___y_1283_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; uint8_t v___y_1332_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1361_; lean_object* v___y_1362_; lean_object* v___x_1378_; uint8_t v___x_1379_; 
v___x_1048_ = lean_unsigned_to_nat(1u);
v_decl_1213_ = l_Lean_Syntax_getArg(v_stx_634_, v___x_1048_);
v___x_1378_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__77));
lean_inc(v_decl_1213_);
v___x_1379_ = l_Lean_Syntax_isOfKind(v_decl_1213_, v___x_1378_);
if (v___x_1379_ == 0)
{
lean_object* v___x_1380_; 
v___x_1380_ = l_Lean_Macro_throwUnsupported___redArg(v_a_636_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_a_1381_; 
v_a_1381_ = lean_ctor_get(v___x_1380_, 1);
lean_inc(v_a_1381_);
lean_dec_ref_known(v___x_1380_, 2);
v___y_1361_ = v_a_635_;
v___y_1362_ = v_a_1381_;
goto v___jp_1360_;
}
else
{
lean_object* v_a_1382_; lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1390_; 
lean_dec(v_decl_1213_);
lean_dec(v_stx_634_);
v_a_1382_ = lean_ctor_get(v___x_1380_, 0);
v_a_1383_ = lean_ctor_get(v___x_1380_, 1);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1385_ = v___x_1380_;
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_inc(v_a_1382_);
lean_dec(v___x_1380_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1388_; 
if (v_isShared_1386_ == 0)
{
v___x_1388_ = v___x_1385_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_a_1382_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v_a_1383_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
}
else
{
v___y_1361_ = v_a_635_;
v___y_1362_ = v_a_636_;
goto v___jp_1360_;
}
v___jp_637_:
{
lean_object* v_quotContext_661_; lean_object* v_currMacroScope_662_; lean_object* v_ref_663_; lean_object* v___x_664_; lean_object* v_a_665_; lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_852_; 
v_quotContext_661_ = lean_ctor_get(v___y_659_, 1);
v_currMacroScope_662_ = lean_ctor_get(v___y_659_, 2);
v_ref_663_ = lean_ctor_get(v___y_659_, 5);
v___x_664_ = l_Lean_Elab_Tactic_Do_expandDefContract___lam__0(v_ref_663_, v___y_659_, v___y_660_);
v_a_665_ = lean_ctor_get(v___x_664_, 0);
v_a_666_ = lean_ctor_get(v___x_664_, 1);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_852_ == 0)
{
v___x_668_ = v___x_664_;
v_isShared_669_ = v_isSharedCheck_852_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_inc(v_a_665_);
lean_dec(v___x_664_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_852_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_850_; 
v___x_670_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__0));
v___x_671_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__0));
lean_inc_ref_n(v___y_643_, 30);
lean_inc_ref_n(v___y_638_, 32);
v___x_672_ = l_Lean_Name_mkStr4(v___y_638_, v___y_643_, v___x_670_, v___x_671_);
v___x_673_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__1));
v___x_674_ = l_Lean_Name_mkStr4(v___y_638_, v___y_643_, v___x_670_, v___x_673_);
lean_inc_n(v_a_665_, 76);
v___x_675_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_675_, 0, v_a_665_);
lean_ctor_set(v___x_675_, 1, v___x_673_);
v___x_676_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__2));
v___x_677_ = l_Lean_Name_mkStr4(v___y_638_, v___y_643_, v___x_670_, v___x_676_);
v___x_678_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__3));
v___x_679_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_679_, 0, v_a_665_);
lean_ctor_set(v___x_679_, 1, v___x_678_);
v___x_680_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_expandDefContract___closed__5, &l_Lean_Elab_Tactic_Do_expandDefContract___closed__5_once, _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__5);
lean_inc_ref(v___y_655_);
lean_inc_ref(v___y_649_);
v___x_681_ = l_Lean_Name_mkStr2(v___y_649_, v___y_655_);
lean_inc_n(v_currMacroScope_662_, 2);
lean_inc(v___x_681_);
lean_inc_n(v_quotContext_661_, 2);
v___x_682_ = l_Lean_addMacroScope(v_quotContext_661_, v___x_681_, v_currMacroScope_662_);
v___x_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_683_, 0, v___x_681_);
v___x_684_ = lean_box(0);
v___x_685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_683_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
v___x_686_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_686_, 0, v_a_665_);
lean_ctor_set(v___x_686_, 1, v___x_680_);
lean_ctor_set(v___x_686_, 2, v___x_682_);
lean_ctor_set(v___x_686_, 3, v___x_685_);
v___x_687_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_expandDefContract___closed__7, &l_Lean_Elab_Tactic_Do_expandDefContract___closed__7_once, _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__7);
lean_inc_ref(v___y_651_);
v___x_688_ = l_Lean_Name_mkStr2(v___y_638_, v___y_651_);
lean_inc(v___x_688_);
v___x_689_ = l_Lean_addMacroScope(v_quotContext_661_, v___x_688_, v_currMacroScope_662_);
v___x_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_690_, 0, v___x_688_);
v___x_691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
lean_ctor_set(v___x_691_, 1, v___x_684_);
v___x_692_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_692_, 0, v_a_665_);
lean_ctor_set(v___x_692_, 1, v___x_687_);
lean_ctor_set(v___x_692_, 2, v___x_689_);
lean_ctor_set(v___x_692_, 3, v___x_691_);
lean_inc_n(v___y_656_, 17);
v___x_693_ = l_Lean_Syntax_node2(v_a_665_, v___y_656_, v___x_686_, v___x_692_);
v___x_694_ = l_Lean_Syntax_node2(v_a_665_, v___x_677_, v___x_679_, v___x_693_);
v___x_695_ = l_Lean_Syntax_node2(v_a_665_, v___x_674_, v___x_675_, v___x_694_);
v___x_696_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_696_, 0, v_a_665_);
lean_ctor_set(v___x_696_, 1, v___x_671_);
v___x_697_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__8));
v___x_698_ = l_Lean_Name_mkStr4(v___y_638_, v___y_643_, v___x_670_, v___x_697_);
v___x_699_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__9));
v___x_700_ = l_Lean_Name_mkStr4(v___y_638_, v___y_643_, v___x_670_, v___x_699_);
lean_inc_ref(v___y_644_);
v___x_701_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_701_, 0, v_a_665_);
lean_ctor_set(v___x_701_, 1, v___y_656_);
lean_ctor_set(v___x_701_, 2, v___y_644_);
v___x_702_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__10));
lean_inc_ref_n(v___y_641_, 4);
v___x_703_ = l_Lean_Name_mkStr4(v___y_638_, v___y_643_, v___y_641_, v___x_702_);
v___x_704_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__11));
v___x_705_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_705_, 0, v_a_665_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
v___x_706_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__12));
v___x_707_ = l_Lean_Name_mkStr4(v___y_638_, v___y_643_, v___y_641_, v___x_706_);
v___x_708_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__13));
v___x_709_ = l_Lean_Name_mkStr4(v___y_638_, v___y_643_, v___y_641_, v___x_708_);
lean_inc_ref_n(v___x_701_, 24);
v___x_710_ = l_Lean_Syntax_node1(v_a_665_, v___x_709_, v___x_701_);
v___x_711_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__14));
lean_inc_ref_n(v___y_647_, 2);
v___x_712_ = l_Lean_Name_mkStr4(v___y_638_, v___y_643_, v___x_711_, v___y_647_);
v___x_713_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_713_, 0, v_a_665_);
lean_ctor_set(v___x_713_, 1, v___y_647_);
v___x_714_ = l_Lean_Syntax_node2(v_a_665_, v___x_712_, v___x_713_, v___x_701_);
v___x_715_ = l_Lean_Syntax_node2(v_a_665_, v___x_707_, v___x_710_, v___x_714_);
v___x_716_ = l_Lean_Syntax_node1(v_a_665_, v___y_656_, v___x_715_);
v___x_717_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__15));
v___x_718_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_718_, 0, v_a_665_);
lean_ctor_set(v___x_718_, 1, v___x_717_);
lean_inc_ref(v___x_718_);
v___x_719_ = l_Lean_Syntax_node3(v_a_665_, v___x_703_, v___x_705_, v___x_716_, v___x_718_);
v___x_720_ = l_Lean_Syntax_node1(v_a_665_, v___y_656_, v___x_719_);
v___x_721_ = l_Lean_Syntax_node7(v_a_665_, v___x_700_, v___x_701_, v___x_720_, v___x_701_, v___x_701_, v___x_701_, v___x_701_, v___x_701_);
v___x_722_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__16));
v___x_723_ = l_Lean_Name_mkStr4(v___y_638_, v___y_643_, v___x_670_, v___x_722_);
v___x_724_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_724_, 0, v_a_665_);
lean_ctor_set(v___x_724_, 1, v___x_722_);
v___x_725_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__17));
v___x_726_ = l_Lean_Name_mkStr4(v___y_638_, v___y_643_, v___x_670_, v___x_725_);
v___x_727_ = lean_mk_empty_array_with_capacity(v___y_640_);
lean_inc_n(v___y_653_, 2);
v___x_728_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_728_, 0, v___y_653_);
lean_ctor_set(v___x_728_, 1, v___y_656_);
lean_ctor_set(v___x_728_, 2, v___x_727_);
v___x_729_ = lean_array_push(v___y_657_, v___y_648_);
v___x_730_ = lean_array_push(v___x_729_, v___x_728_);
v___x_731_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_731_, 0, v___y_653_);
lean_ctor_set(v___x_731_, 1, v___x_726_);
lean_ctor_set(v___x_731_, 2, v___x_730_);
v___x_732_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__18));
v___x_733_ = l_Lean_Name_mkStr4(v___y_638_, v___y_643_, v___x_670_, v___x_732_);
v___x_734_ = l_Array_append___redArg(v___y_644_, v___y_646_);
lean_dec_ref(v___y_646_);
v___x_735_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_735_, 0, v_a_665_);
lean_ctor_set(v___x_735_, 1, v___y_656_);
lean_ctor_set(v___x_735_, 2, v___x_734_);
v___x_736_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__19));
v___x_737_ = l_Lean_Name_mkStr4(v___y_638_, v___y_643_, v___y_641_, v___x_736_);
v___x_738_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__20));
v___x_739_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_739_, 0, v_a_665_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
v___x_740_ = l_Lean_Syntax_node2(v_a_665_, v___x_737_, v___x_739_, v___y_650_);
v___x_741_ = l_Lean_Syntax_node2(v_a_665_, v___x_733_, v___x_735_, v___x_740_);
v___x_742_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_whereDeclsPath_x3f___closed__1));
v___x_743_ = l_Lean_Name_mkStr4(v___y_638_, v___y_643_, v___x_670_, v___x_742_);
v___x_744_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__21));
v___x_745_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_745_, 0, v_a_665_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v___x_746_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__22));
v___x_747_ = l_Lean_Name_mkStr4(v___y_638_, v___y_643_, v___y_641_, v___x_746_);
v___x_748_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__23));
v___x_749_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_749_, 0, v_a_665_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
v___x_750_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__22));
v___x_751_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__24));
v___x_752_ = l_Lean_Name_mkStr4(v___y_638_, v___y_643_, v___x_750_, v___x_751_);
v___x_753_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__25));
v___x_754_ = l_Lean_Name_mkStr4(v___y_638_, v___y_643_, v___x_750_, v___x_753_);
v___x_755_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__26));
v___x_756_ = l_Lean_Name_mkStr4(v___y_638_, v___y_643_, v___x_750_, v___x_755_);
v___x_757_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_757_, 0, v_a_665_);
lean_ctor_set(v___x_757_, 1, v___x_755_);
v___x_758_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__27));
v___x_759_ = l_Lean_Name_mkStr4(v___y_638_, v___y_643_, v___x_750_, v___x_758_);
v___x_760_ = l_Lean_Syntax_node1(v_a_665_, v___x_759_, v___x_701_);
v___x_761_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__28));
v___x_762_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_762_, 0, v_a_665_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
v___x_763_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__29));
v___x_764_ = l_Lean_Name_mkStr4(v___y_638_, v___y_643_, v___x_750_, v___x_763_);
v___x_765_ = l_Lean_Syntax_node3(v_a_665_, v___x_764_, v___x_701_, v___x_701_, v___y_654_);
v___x_766_ = l_Lean_Syntax_node1(v_a_665_, v___y_656_, v___x_765_);
v___x_767_ = l_Lean_Syntax_node3(v_a_665_, v___y_656_, v___x_762_, v___x_766_, v___x_718_);
v___x_768_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__30));
v___x_769_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_769_, 0, v_a_665_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
v___x_770_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__31));
v___x_771_ = l_Lean_Name_mkStr4(v___y_638_, v___y_643_, v___x_750_, v___x_770_);
v___x_772_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__32));
v___x_773_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__12));
v___x_774_ = l_Lean_Name_mkStr5(v___y_638_, v___y_643_, v___x_750_, v___x_772_, v___x_773_);
v___x_775_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__16));
v___x_776_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_776_, 0, v_a_665_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
v___x_777_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__33));
v___x_778_ = l_Lean_Name_mkStr5(v___y_638_, v___y_643_, v___x_750_, v___x_772_, v___x_777_);
v___x_779_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__34));
v___x_780_ = l_Lean_Name_mkStr5(v___y_638_, v___y_643_, v___x_750_, v___x_772_, v___x_779_);
v___x_781_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__35));
v___x_782_ = l_Lean_Name_mkStr5(v___y_638_, v___y_643_, v___x_750_, v___x_772_, v___x_781_);
v___x_783_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__36));
v___x_784_ = l_Lean_Name_mkStr5(v___y_638_, v___y_643_, v___x_750_, v___x_772_, v___x_783_);
v___x_785_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__37));
v___x_786_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_786_, 0, v_a_665_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
v___x_787_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__38));
v___x_788_ = l_Lean_Name_mkStr5(v___y_638_, v___y_643_, v___x_750_, v___x_772_, v___x_787_);
v___x_789_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_789_, 0, v_a_665_);
lean_ctor_set(v___x_789_, 1, v___x_787_);
v___x_790_ = l_Lean_Syntax_node4(v_a_665_, v___x_788_, v___x_789_, v___x_701_, v___x_701_, v___x_701_);
lean_inc(v___x_782_);
v___x_791_ = l_Lean_Syntax_node2(v_a_665_, v___x_782_, v___x_790_, v___x_701_);
v___x_792_ = l_Lean_Syntax_node1(v_a_665_, v___y_656_, v___x_791_);
lean_inc(v___x_780_);
v___x_793_ = l_Lean_Syntax_node1(v_a_665_, v___x_780_, v___x_792_);
lean_inc(v___x_778_);
v___x_794_ = l_Lean_Syntax_node1(v_a_665_, v___x_778_, v___x_793_);
v___x_795_ = l_Lean_Syntax_node2(v_a_665_, v___x_784_, v___x_786_, v___x_794_);
v___x_796_ = l_Lean_Syntax_node2(v_a_665_, v___x_782_, v___x_795_, v___x_701_);
v___x_797_ = l_Lean_Syntax_node1(v_a_665_, v___y_656_, v___x_796_);
v___x_798_ = l_Lean_Syntax_node1(v_a_665_, v___x_780_, v___x_797_);
v___x_799_ = l_Lean_Syntax_node1(v_a_665_, v___x_778_, v___x_798_);
v___x_800_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__42));
v___x_801_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_801_, 0, v_a_665_);
lean_ctor_set(v___x_801_, 1, v___x_800_);
v___x_802_ = l_Lean_Syntax_node3(v_a_665_, v___x_774_, v___x_776_, v___x_799_, v___x_801_);
v___x_803_ = l_Lean_Syntax_node1(v_a_665_, v___x_771_, v___x_802_);
v___x_804_ = l_Lean_Syntax_node2(v_a_665_, v___y_656_, v___x_769_, v___x_803_);
v___x_805_ = l_Lean_Syntax_node8(v_a_665_, v___x_756_, v___x_757_, v___x_760_, v___x_767_, v___x_701_, v___x_701_, v___x_701_, v___x_701_, v___x_804_);
v___x_806_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__39));
v___x_807_ = l_Lean_Name_mkStr4(v___y_638_, v___y_643_, v___x_750_, v___x_806_);
v___x_808_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_808_, 0, v_a_665_);
lean_ctor_set(v___x_808_, 1, v___x_806_);
v___x_809_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__41));
v___x_810_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__42));
v___x_811_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_811_, 0, v_a_665_);
lean_ctor_set(v___x_811_, 1, v___x_810_);
v___x_812_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__43));
v___x_813_ = l_Lean_Name_mkStr4(v___y_638_, v___y_643_, v___x_750_, v___x_812_);
v___x_814_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_814_, 0, v_a_665_);
lean_ctor_set(v___x_814_, 1, v___x_812_);
v___x_815_ = l_Lean_Syntax_node1(v_a_665_, v___x_813_, v___x_814_);
v___x_816_ = l_Lean_Syntax_node1(v_a_665_, v___y_656_, v___x_815_);
lean_inc_n(v___x_754_, 2);
v___x_817_ = l_Lean_Syntax_node1(v_a_665_, v___x_754_, v___x_816_);
lean_inc_n(v___x_752_, 2);
v___x_818_ = l_Lean_Syntax_node1(v_a_665_, v___x_752_, v___x_817_);
lean_inc_ref(v___x_811_);
v___x_819_ = l_Lean_Syntax_node2(v_a_665_, v___x_809_, v___x_811_, v___x_818_);
v___x_820_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__44));
v___x_821_ = l_Lean_Name_mkStr4(v___y_638_, v___y_643_, v___x_750_, v___x_820_);
v___x_822_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_822_, 0, v_a_665_);
lean_ctor_set(v___x_822_, 1, v___x_820_);
v___x_823_ = l_Lean_Syntax_node1(v_a_665_, v___y_656_, v___y_642_);
v___x_824_ = l_Lean_Syntax_node2(v_a_665_, v___x_821_, v___x_822_, v___x_823_);
v___x_825_ = l_Lean_Syntax_node1(v_a_665_, v___y_656_, v___x_824_);
v___x_826_ = l_Lean_Syntax_node1(v_a_665_, v___x_754_, v___x_825_);
v___x_827_ = l_Lean_Syntax_node1(v_a_665_, v___x_752_, v___x_826_);
v___x_828_ = l_Lean_Syntax_node2(v_a_665_, v___x_809_, v___x_811_, v___x_827_);
v___x_829_ = l_Lean_Syntax_node2(v_a_665_, v___y_656_, v___x_819_, v___x_828_);
v___x_830_ = l_Lean_Syntax_node2(v_a_665_, v___x_807_, v___x_808_, v___x_829_);
v___x_831_ = l_Lean_Syntax_node5(v_a_665_, v___y_656_, v___x_805_, v___x_701_, v_specTac_658_, v___x_701_, v___x_830_);
v___x_832_ = l_Lean_Syntax_node1(v_a_665_, v___x_754_, v___x_831_);
v___x_833_ = l_Lean_Syntax_node1(v_a_665_, v___x_752_, v___x_832_);
v___x_834_ = l_Lean_Syntax_node2(v_a_665_, v___x_747_, v___x_749_, v___x_833_);
v___x_835_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__45));
v___x_836_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__46));
v___x_837_ = l_Lean_Name_mkStr4(v___y_638_, v___y_643_, v___x_835_, v___x_836_);
v___x_838_ = l_Lean_Syntax_node2(v_a_665_, v___x_837_, v___x_701_, v___x_701_);
v___x_839_ = l_Lean_Syntax_node4(v_a_665_, v___x_743_, v___x_745_, v___x_834_, v___x_838_, v___x_701_);
v___x_840_ = l_Lean_Syntax_node4(v_a_665_, v___x_723_, v___x_724_, v___x_731_, v___x_741_, v___x_839_);
v___x_841_ = l_Lean_Syntax_node2(v_a_665_, v___x_698_, v___x_721_, v___x_840_);
v___x_842_ = l_Lean_Syntax_node3(v_a_665_, v___x_672_, v___x_695_, v___x_696_, v___x_841_);
v___x_843_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice(v___y_645_);
lean_dec(v___y_645_);
v___x_844_ = lean_mk_empty_array_with_capacity(v___y_639_);
v___x_845_ = lean_array_push(v___x_844_, v___x_843_);
v___x_846_ = lean_array_push(v___x_845_, v___y_652_);
v___x_847_ = lean_array_push(v___x_846_, v___x_842_);
v___x_848_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_848_, 0, v___y_653_);
lean_ctor_set(v___x_848_, 1, v___y_656_);
lean_ctor_set(v___x_848_, 2, v___x_847_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 0, v___x_848_);
v___x_850_ = v___x_668_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_848_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v_a_666_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
v___jp_853_:
{
lean_object* v___x_877_; lean_object* v_a_878_; lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_972_; 
v___x_877_ = l_Lean_Elab_Tactic_Do_expandDefContract___lam__0(v___y_873_, v___y_858_, v_a_876_);
v_a_878_ = lean_ctor_get(v___x_877_, 0);
v_a_879_ = lean_ctor_get(v___x_877_, 1);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_972_ == 0)
{
v___x_881_ = v___x_877_;
v_isShared_882_ = v_isSharedCheck_972_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_inc(v_a_878_);
lean_dec(v___x_877_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_972_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_897_; 
v___x_883_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__1));
v___x_884_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__2));
v___x_885_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__47));
lean_inc_ref(v___y_854_);
v___x_886_ = l_Lean_Name_mkStr4(v___y_854_, v___x_883_, v___x_884_, v___x_885_);
v___x_887_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_expandDefContract___closed__49, &l_Lean_Elab_Tactic_Do_expandDefContract___closed__49_once, _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__49);
v___x_888_ = lean_mk_empty_array_with_capacity(v___y_869_);
lean_inc_ref(v___x_888_);
v___x_889_ = lean_array_push(v___x_888_, v___x_887_);
v___x_890_ = lean_array_push(v___x_889_, v_a_875_);
v___x_891_ = lean_box(2);
v___x_892_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
lean_ctor_set(v___x_892_, 1, v___x_886_);
lean_ctor_set(v___x_892_, 2, v___x_890_);
v___x_893_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__50));
lean_inc_ref(v___y_871_);
lean_inc_ref(v___y_866_);
v___x_894_ = l_Lean_Name_mkStr3(v___y_866_, v___y_871_, v___x_893_);
v___x_895_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__51));
lean_inc(v_a_878_);
if (v_isShared_882_ == 0)
{
lean_ctor_set_tag(v___x_881_, 2);
lean_ctor_set(v___x_881_, 1, v___x_895_);
v___x_897_ = v___x_881_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_a_878_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v___x_895_);
v___x_897_ = v_reuseFailAlloc_971_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; size_t v_sz_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_898_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__52));
lean_inc_n(v_a_878_, 5);
v___x_899_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_899_, 0, v_a_878_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
v___x_900_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__2));
v___x_901_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_expandDefContract___closed__53, &l_Lean_Elab_Tactic_Do_expandDefContract___closed__53_once, _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__53);
v___x_902_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_902_, 0, v_a_878_);
lean_ctor_set(v___x_902_, 1, v___x_900_);
lean_ctor_set(v___x_902_, 2, v___x_901_);
v___x_903_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__6));
lean_inc_ref(v___y_854_);
v___x_904_ = l_Lean_Name_mkStr4(v___y_854_, v___x_883_, v___x_884_, v___x_903_);
v_sz_905_ = lean_array_size(v___y_862_);
v___x_906_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__1(v_sz_905_, v___y_874_, v___y_862_);
v___x_907_ = l_Array_append___redArg(v___x_901_, v___x_906_);
lean_dec_ref(v___x_906_);
v___x_908_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_908_, 0, v_a_878_);
lean_ctor_set(v___x_908_, 1, v___x_900_);
lean_ctor_set(v___x_908_, 2, v___x_907_);
lean_inc(v___y_872_);
v___x_909_ = l_Lean_Syntax_node2(v_a_878_, v___x_904_, v___y_872_, v___x_908_);
v___x_910_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__54));
v___x_911_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_911_, 0, v_a_878_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = lean_unsigned_to_nat(10u);
v___x_913_ = lean_mk_empty_array_with_capacity(v___x_912_);
lean_inc_ref(v___x_897_);
v___x_914_ = lean_array_push(v___x_913_, v___x_897_);
v___x_915_ = lean_array_push(v___x_914_, v___y_863_);
lean_inc_ref(v___x_899_);
v___x_916_ = lean_array_push(v___x_915_, v___x_899_);
v___x_917_ = lean_array_push(v___x_916_, v___x_902_);
v___x_918_ = lean_array_push(v___x_917_, v___x_909_);
v___x_919_ = lean_array_push(v___x_918_, v___x_897_);
v___x_920_ = lean_array_push(v___x_919_, v___y_870_);
v___x_921_ = lean_array_push(v___x_920_, v___x_911_);
v___x_922_ = lean_array_push(v___x_921_, v___x_892_);
v___x_923_ = lean_array_push(v___x_922_, v___x_899_);
v___x_924_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_924_, 0, v_a_878_);
lean_ctor_set(v___x_924_, 1, v___x_894_);
lean_ctor_set(v___x_924_, 2, v___x_923_);
if (lean_obj_tag(v___y_860_) == 0)
{
lean_object* v___x_925_; lean_object* v_a_926_; lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_945_; 
v___x_925_ = l_Lean_Elab_Tactic_Do_expandDefContract___lam__0(v___y_873_, v___y_858_, v_a_879_);
v_a_926_ = lean_ctor_get(v___x_925_, 0);
v_a_927_ = lean_ctor_get(v___x_925_, 1);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_945_ == 0)
{
v___x_929_ = v___x_925_;
v_isShared_930_ = v_isSharedCheck_945_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_inc(v_a_926_);
lean_dec(v___x_925_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_945_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_931_; uint8_t v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_942_; 
v___x_931_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__55));
v___x_932_ = 1;
v___x_933_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_857_, v___x_932_);
v___x_934_ = lean_string_append(v___x_931_, v___x_933_);
lean_dec_ref(v___x_933_);
v___x_935_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__56));
v___x_936_ = lean_string_append(v___x_934_, v___x_935_);
v___x_937_ = l_Lean_Syntax_mkStrLit(v___x_936_, v___x_891_);
v___x_938_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__22));
v___x_939_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__57));
lean_inc_ref(v___y_854_);
v___x_940_ = l_Lean_Name_mkStr4(v___y_854_, v___x_883_, v___x_938_, v___x_939_);
lean_inc(v_a_926_);
if (v_isShared_930_ == 0)
{
lean_ctor_set_tag(v___x_929_, 2);
lean_ctor_set(v___x_929_, 1, v___x_939_);
v___x_942_ = v___x_929_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_a_926_);
lean_ctor_set(v_reuseFailAlloc_944_, 1, v___x_939_);
v___x_942_ = v_reuseFailAlloc_944_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_object* v___x_943_; 
v___x_943_ = l_Lean_Syntax_node1(v_a_926_, v___x_940_, v___x_942_);
v___y_638_ = v___y_854_;
v___y_639_ = v___y_855_;
v___y_640_ = v___y_856_;
v___y_641_ = v___x_884_;
v___y_642_ = v___x_937_;
v___y_643_ = v___x_883_;
v___y_644_ = v___x_901_;
v___y_645_ = v___y_859_;
v___y_646_ = v___y_861_;
v___y_647_ = v___y_865_;
v___y_648_ = v___y_864_;
v___y_649_ = v___y_866_;
v___y_650_ = v___x_924_;
v___y_651_ = v___y_867_;
v___y_652_ = v___y_868_;
v___y_653_ = v___x_891_;
v___y_654_ = v___y_872_;
v___y_655_ = v___y_871_;
v___y_656_ = v___x_900_;
v___y_657_ = v___x_888_;
v_specTac_658_ = v___x_943_;
v___y_659_ = v___y_858_;
v___y_660_ = v_a_927_;
goto v___jp_637_;
}
}
}
else
{
lean_object* v_val_946_; lean_object* v___x_947_; lean_object* v_a_948_; lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_970_; 
v_val_946_ = lean_ctor_get(v___y_860_, 0);
lean_inc(v_val_946_);
lean_dec_ref_known(v___y_860_, 1);
v___x_947_ = l_Lean_Elab_Tactic_Do_expandDefContract___lam__0(v___y_873_, v___y_858_, v_a_879_);
v_a_948_ = lean_ctor_get(v___x_947_, 0);
v_a_949_ = lean_ctor_get(v___x_947_, 1);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_970_ == 0)
{
v___x_951_ = v___x_947_;
v_isShared_952_ = v_isSharedCheck_970_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_inc(v_a_948_);
lean_dec(v___x_947_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_970_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
uint8_t v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_965_; 
v___x_953_ = 1;
v___x_954_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__55));
v___x_955_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_857_, v___x_953_);
v___x_956_ = lean_string_append(v___x_954_, v___x_955_);
lean_dec_ref(v___x_955_);
v___x_957_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__58));
v___x_958_ = lean_string_append(v___x_956_, v___x_957_);
v___x_959_ = l_Lean_Syntax_mkStrLit(v___x_958_, v___x_891_);
v___x_960_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__22));
v___x_961_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__12));
lean_inc_ref(v___y_854_);
v___x_962_ = l_Lean_Name_mkStr4(v___y_854_, v___x_883_, v___x_960_, v___x_961_);
v___x_963_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__16));
lean_inc(v_a_948_);
if (v_isShared_952_ == 0)
{
lean_ctor_set_tag(v___x_951_, 2);
lean_ctor_set(v___x_951_, 1, v___x_963_);
v___x_965_ = v___x_951_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_948_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v___x_963_);
v___x_965_ = v_reuseFailAlloc_969_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_966_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__42));
lean_inc(v_a_948_);
v___x_967_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_967_, 0, v_a_948_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
v___x_968_ = l_Lean_Syntax_node3(v_a_948_, v___x_962_, v___x_965_, v_val_946_, v___x_967_);
v___y_638_ = v___y_854_;
v___y_639_ = v___y_855_;
v___y_640_ = v___y_856_;
v___y_641_ = v___x_884_;
v___y_642_ = v___x_959_;
v___y_643_ = v___x_883_;
v___y_644_ = v___x_901_;
v___y_645_ = v___y_859_;
v___y_646_ = v___y_861_;
v___y_647_ = v___y_865_;
v___y_648_ = v___y_864_;
v___y_649_ = v___y_866_;
v___y_650_ = v___x_924_;
v___y_651_ = v___y_867_;
v___y_652_ = v___y_868_;
v___y_653_ = v___x_891_;
v___y_654_ = v___y_872_;
v___y_655_ = v___y_871_;
v___y_656_ = v___x_900_;
v___y_657_ = v___x_888_;
v_specTac_658_ = v___x_968_;
v___y_659_ = v___y_858_;
v___y_660_ = v_a_949_;
goto v___jp_637_;
}
}
}
}
}
}
v___jp_973_:
{
lean_object* v___x_995_; lean_object* v_a_996_; lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1025_; 
v___x_995_ = l_Lean_Elab_Tactic_Do_expandDefContract___lam__0(v_ref_993_, v___y_992_, v___y_994_);
v_a_996_ = lean_ctor_get(v___x_995_, 0);
v_a_997_ = lean_ctor_get(v___x_995_, 1);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_999_ = v___x_995_;
v_isShared_1000_ = v_isSharedCheck_1025_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_inc(v_a_996_);
lean_dec(v___x_995_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1025_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1006_; 
v___x_1001_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_contractBinderIdents___closed__0));
v___x_1002_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__26));
v___x_1003_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__60));
v___x_1004_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__61));
lean_inc(v_a_996_);
if (v_isShared_1000_ == 0)
{
lean_ctor_set_tag(v___x_999_, 2);
lean_ctor_set(v___x_999_, 1, v___x_1004_);
v___x_1006_ = v___x_999_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_996_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v___x_1004_);
v___x_1006_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; uint8_t v___x_1010_; 
v___x_1007_ = l_Lean_Syntax_node1(v_a_996_, v___x_1003_, v___x_1006_);
v___x_1008_ = l_Lean_Syntax_getArgs(v___y_987_);
lean_dec(v___y_987_);
v___x_1009_ = lean_array_get_size(v___x_1008_);
v___x_1010_ = lean_nat_dec_lt(v___y_975_, v___x_1009_);
if (v___x_1010_ == 0)
{
lean_dec_ref(v___x_1008_);
v___y_854_ = v___x_1001_;
v___y_855_ = v___y_974_;
v___y_856_ = v___y_975_;
v___y_857_ = v___y_976_;
v___y_858_ = v___y_992_;
v___y_859_ = v___y_977_;
v___y_860_ = v___y_978_;
v___y_861_ = v___y_979_;
v___y_862_ = v___y_980_;
v___y_863_ = v___y_981_;
v___y_864_ = v___y_982_;
v___y_865_ = v___y_983_;
v___y_866_ = v___y_984_;
v___y_867_ = v___x_1002_;
v___y_868_ = v___y_986_;
v___y_869_ = v___y_985_;
v___y_870_ = v_post_991_;
v___y_871_ = v___y_989_;
v___y_872_ = v___y_988_;
v___y_873_ = v_ref_993_;
v___y_874_ = v___y_990_;
v_a_875_ = v___x_1007_;
v_a_876_ = v_a_997_;
goto v___jp_853_;
}
else
{
size_t v___x_1011_; lean_object* v___x_1012_; 
v___x_1011_ = lean_usize_of_nat(v___x_1009_);
v___x_1012_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2(v___x_1008_, v___x_1011_, v___y_990_, v___x_1007_, v___y_992_, v_a_997_);
lean_dec_ref(v___x_1008_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; lean_object* v_a_1014_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1013_);
v_a_1014_ = lean_ctor_get(v___x_1012_, 1);
lean_inc(v_a_1014_);
lean_dec_ref_known(v___x_1012_, 2);
v___y_854_ = v___x_1001_;
v___y_855_ = v___y_974_;
v___y_856_ = v___y_975_;
v___y_857_ = v___y_976_;
v___y_858_ = v___y_992_;
v___y_859_ = v___y_977_;
v___y_860_ = v___y_978_;
v___y_861_ = v___y_979_;
v___y_862_ = v___y_980_;
v___y_863_ = v___y_981_;
v___y_864_ = v___y_982_;
v___y_865_ = v___y_983_;
v___y_866_ = v___y_984_;
v___y_867_ = v___x_1002_;
v___y_868_ = v___y_986_;
v___y_869_ = v___y_985_;
v___y_870_ = v_post_991_;
v___y_871_ = v___y_989_;
v___y_872_ = v___y_988_;
v___y_873_ = v_ref_993_;
v___y_874_ = v___y_990_;
v_a_875_ = v_a_1013_;
v_a_876_ = v_a_1014_;
goto v___jp_853_;
}
else
{
lean_object* v_a_1015_; lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1023_; 
lean_dec(v_post_991_);
lean_dec(v___y_988_);
lean_dec(v___y_986_);
lean_dec(v___y_982_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec(v___y_977_);
lean_dec(v___y_976_);
v_a_1015_ = lean_ctor_get(v___x_1012_, 0);
v_a_1016_ = lean_ctor_get(v___x_1012_, 1);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1018_ = v___x_1012_;
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_inc(v_a_1015_);
lean_dec(v___x_1012_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1021_; 
if (v_isShared_1019_ == 0)
{
v___x_1021_ = v___x_1018_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_a_1015_);
lean_ctor_set(v_reuseFailAlloc_1022_, 1, v_a_1016_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
}
}
}
v___jp_1026_:
{
lean_object* v_ref_1047_; 
v_ref_1047_ = lean_ctor_get(v___y_1045_, 5);
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
v___y_985_ = v___y_1038_;
v___y_986_ = v___y_1039_;
v___y_987_ = v___y_1040_;
v___y_988_ = v___y_1041_;
v___y_989_ = v___y_1042_;
v___y_990_ = v___y_1043_;
v_post_991_ = v_post_1044_;
v___y_992_ = v___y_1045_;
v_ref_993_ = v_ref_1047_;
v___y_994_ = v___y_1046_;
goto v___jp_973_;
}
v___jp_1049_:
{
uint8_t v___x_1071_; 
v___x_1071_ = l_Lean_Syntax_isNone(v___y_1056_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; 
v___x_1072_ = l_Lean_Syntax_getArg(v___y_1056_, v___y_1051_);
lean_dec(v___y_1056_);
v___x_1073_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__63));
lean_inc(v___x_1072_);
v___x_1074_ = l_Lean_Syntax_isOfKind(v___x_1072_, v___x_1073_);
if (v___x_1074_ == 0)
{
lean_object* v___x_1075_; 
lean_dec(v___x_1072_);
v___x_1075_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1070_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; lean_object* v_a_1077_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_a_1076_);
v_a_1077_ = lean_ctor_get(v___x_1075_, 1);
lean_inc(v_a_1077_);
lean_dec_ref_known(v___x_1075_, 2);
v___y_1027_ = v___y_1050_;
v___y_1028_ = v___y_1051_;
v___y_1029_ = v___y_1052_;
v___y_1030_ = v___y_1053_;
v___y_1031_ = v___y_1054_;
v___y_1032_ = v___y_1055_;
v___y_1033_ = v___y_1057_;
v___y_1034_ = v_pre_1068_;
v___y_1035_ = v___y_1059_;
v___y_1036_ = v___y_1060_;
v___y_1037_ = v___y_1061_;
v___y_1038_ = v___y_1062_;
v___y_1039_ = v___y_1063_;
v___y_1040_ = v___y_1064_;
v___y_1041_ = v___y_1066_;
v___y_1042_ = v___y_1065_;
v___y_1043_ = v___y_1067_;
v_post_1044_ = v_a_1076_;
v___y_1045_ = v___y_1069_;
v___y_1046_ = v_a_1077_;
goto v___jp_1026_;
}
else
{
lean_object* v_a_1078_; lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
lean_dec(v_pre_1068_);
lean_dec(v___y_1066_);
lean_dec(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1057_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec(v___y_1052_);
v_a_1078_ = lean_ctor_get(v___x_1075_, 0);
v_a_1079_ = lean_ctor_get(v___x_1075_, 1);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1075_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_inc(v_a_1078_);
lean_dec(v___x_1075_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1078_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v_a_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
else
{
lean_object* v___x_1087_; lean_object* v___x_1088_; uint8_t v___x_1089_; 
v___x_1087_ = l_Lean_Syntax_getArg(v___x_1072_, v___x_1048_);
lean_dec(v___x_1072_);
v___x_1088_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__3));
lean_inc(v___x_1087_);
v___x_1089_ = l_Lean_Syntax_isOfKind(v___x_1087_, v___x_1088_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; 
lean_dec(v___x_1087_);
v___x_1090_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1070_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v_a_1091_; lean_object* v_a_1092_; 
v_a_1091_ = lean_ctor_get(v___x_1090_, 0);
lean_inc(v_a_1091_);
v_a_1092_ = lean_ctor_get(v___x_1090_, 1);
lean_inc(v_a_1092_);
lean_dec_ref_known(v___x_1090_, 2);
v___y_1027_ = v___y_1050_;
v___y_1028_ = v___y_1051_;
v___y_1029_ = v___y_1052_;
v___y_1030_ = v___y_1053_;
v___y_1031_ = v___y_1054_;
v___y_1032_ = v___y_1055_;
v___y_1033_ = v___y_1057_;
v___y_1034_ = v_pre_1068_;
v___y_1035_ = v___y_1059_;
v___y_1036_ = v___y_1060_;
v___y_1037_ = v___y_1061_;
v___y_1038_ = v___y_1062_;
v___y_1039_ = v___y_1063_;
v___y_1040_ = v___y_1064_;
v___y_1041_ = v___y_1066_;
v___y_1042_ = v___y_1065_;
v___y_1043_ = v___y_1067_;
v_post_1044_ = v_a_1091_;
v___y_1045_ = v___y_1069_;
v___y_1046_ = v_a_1092_;
goto v___jp_1026_;
}
else
{
lean_object* v_a_1093_; lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1101_; 
lean_dec(v_pre_1068_);
lean_dec(v___y_1066_);
lean_dec(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1057_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec(v___y_1052_);
v_a_1093_ = lean_ctor_get(v___x_1090_, 0);
v_a_1094_ = lean_ctor_get(v___x_1090_, 1);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1096_ = v___x_1090_;
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_inc(v_a_1093_);
lean_dec(v___x_1090_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1099_; 
if (v_isShared_1097_ == 0)
{
v___x_1099_ = v___x_1096_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_a_1093_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v_a_1094_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
}
else
{
lean_object* v_ref_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v_ref_1102_ = lean_ctor_get(v___y_1069_, 5);
v___x_1103_ = l_Lean_SourceInfo_fromRef(v_ref_1102_, v___x_1071_);
v___x_1104_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__40));
v___x_1105_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__41));
lean_inc(v___x_1103_);
v___x_1106_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1103_);
lean_ctor_set(v___x_1106_, 1, v___x_1104_);
v___x_1107_ = l_Lean_Syntax_node2(v___x_1103_, v___x_1105_, v___x_1106_, v___x_1087_);
v___y_974_ = v___y_1050_;
v___y_975_ = v___y_1051_;
v___y_976_ = v___y_1052_;
v___y_977_ = v___y_1053_;
v___y_978_ = v___y_1054_;
v___y_979_ = v___y_1055_;
v___y_980_ = v___y_1057_;
v___y_981_ = v_pre_1068_;
v___y_982_ = v___y_1059_;
v___y_983_ = v___y_1060_;
v___y_984_ = v___y_1061_;
v___y_985_ = v___y_1062_;
v___y_986_ = v___y_1063_;
v___y_987_ = v___y_1064_;
v___y_988_ = v___y_1066_;
v___y_989_ = v___y_1065_;
v___y_990_ = v___y_1067_;
v_post_991_ = v___x_1107_;
v___y_992_ = v___y_1069_;
v_ref_993_ = v_ref_1102_;
v___y_994_ = v___y_1070_;
goto v___jp_973_;
}
}
}
else
{
lean_object* v_ref_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
lean_dec(v___y_1056_);
v_ref_1108_ = lean_ctor_get(v___y_1069_, 5);
v___x_1109_ = l_Lean_SourceInfo_fromRef(v_ref_1108_, v___y_1058_);
v___x_1110_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__40));
v___x_1111_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__41));
lean_inc_n(v___x_1109_, 9);
v___x_1112_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1109_);
lean_ctor_set(v___x_1112_, 1, v___x_1110_);
v___x_1113_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__3));
v___x_1114_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__2));
v___x_1115_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__65));
v___x_1116_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__66));
v___x_1117_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1109_);
lean_ctor_set(v___x_1117_, 1, v___x_1116_);
v___x_1118_ = l_Lean_Syntax_node1(v___x_1109_, v___x_1115_, v___x_1117_);
v___x_1119_ = l_Lean_Syntax_node1(v___x_1109_, v___x_1114_, v___x_1118_);
v___x_1120_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_expandDefContract___closed__53, &l_Lean_Elab_Tactic_Do_expandDefContract___closed__53_once, _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__53);
v___x_1121_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1109_);
lean_ctor_set(v___x_1121_, 1, v___x_1114_);
lean_ctor_set(v___x_1121_, 2, v___x_1120_);
v___x_1122_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__67));
v___x_1123_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1109_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
v___x_1124_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__69));
v___x_1125_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__70));
v___x_1126_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1109_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
v___x_1127_ = l_Lean_Syntax_node1(v___x_1109_, v___x_1124_, v___x_1126_);
v___x_1128_ = l_Lean_Syntax_node4(v___x_1109_, v___x_1113_, v___x_1119_, v___x_1121_, v___x_1123_, v___x_1127_);
v___x_1129_ = l_Lean_Syntax_node2(v___x_1109_, v___x_1111_, v___x_1112_, v___x_1128_);
v___y_974_ = v___y_1050_;
v___y_975_ = v___y_1051_;
v___y_976_ = v___y_1052_;
v___y_977_ = v___y_1053_;
v___y_978_ = v___y_1054_;
v___y_979_ = v___y_1055_;
v___y_980_ = v___y_1057_;
v___y_981_ = v_pre_1068_;
v___y_982_ = v___y_1059_;
v___y_983_ = v___y_1060_;
v___y_984_ = v___y_1061_;
v___y_985_ = v___y_1062_;
v___y_986_ = v___y_1063_;
v___y_987_ = v___y_1064_;
v___y_988_ = v___y_1066_;
v___y_989_ = v___y_1065_;
v___y_990_ = v___y_1067_;
v_post_991_ = v___x_1129_;
v___y_992_ = v___y_1069_;
v_ref_993_ = v_ref_1108_;
v___y_994_ = v___y_1070_;
goto v___jp_973_;
}
}
v___jp_1130_:
{
uint8_t v___x_1152_; 
v___x_1152_ = l_Lean_Syntax_isNone(v___y_1135_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1153_; lean_object* v___x_1154_; uint8_t v___x_1155_; 
v___x_1153_ = l_Lean_Syntax_getArg(v___y_1135_, v___y_1133_);
lean_dec(v___y_1135_);
v___x_1154_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__72));
lean_inc(v___x_1153_);
v___x_1155_ = l_Lean_Syntax_isOfKind(v___x_1153_, v___x_1154_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; 
lean_dec(v___x_1153_);
v___x_1156_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1131_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v_a_1158_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_a_1157_);
v_a_1158_ = lean_ctor_get(v___x_1156_, 1);
lean_inc(v_a_1158_);
lean_dec_ref_known(v___x_1156_, 2);
v___y_1050_ = v___y_1132_;
v___y_1051_ = v___y_1133_;
v___y_1052_ = v___y_1134_;
v___y_1053_ = v___y_1136_;
v___y_1054_ = v___y_1137_;
v___y_1055_ = v___y_1138_;
v___y_1056_ = v___y_1139_;
v___y_1057_ = v___y_1151_;
v___y_1058_ = v___y_1140_;
v___y_1059_ = v___y_1141_;
v___y_1060_ = v___y_1142_;
v___y_1061_ = v___y_1143_;
v___y_1062_ = v___y_1144_;
v___y_1063_ = v___y_1145_;
v___y_1064_ = v___y_1146_;
v___y_1065_ = v___y_1149_;
v___y_1066_ = v___y_1148_;
v___y_1067_ = v___y_1150_;
v_pre_1068_ = v_a_1157_;
v___y_1069_ = v___y_1147_;
v___y_1070_ = v_a_1158_;
goto v___jp_1049_;
}
else
{
lean_object* v_a_1159_; lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1167_; 
lean_dec_ref(v___y_1151_);
lean_dec(v___y_1148_);
lean_dec(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec(v___y_1141_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec(v___y_1137_);
lean_dec(v___y_1136_);
lean_dec(v___y_1134_);
v_a_1159_ = lean_ctor_get(v___x_1156_, 0);
v_a_1160_ = lean_ctor_get(v___x_1156_, 1);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1162_ = v___x_1156_;
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_inc(v_a_1159_);
lean_dec(v___x_1156_);
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
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1159_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_a_1160_);
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
else
{
lean_object* v___x_1168_; lean_object* v___x_1169_; uint8_t v___x_1170_; 
v___x_1168_ = l_Lean_Syntax_getArg(v___x_1153_, v___x_1048_);
lean_dec(v___x_1153_);
v___x_1169_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__3));
lean_inc(v___x_1168_);
v___x_1170_ = l_Lean_Syntax_isOfKind(v___x_1168_, v___x_1169_);
if (v___x_1170_ == 0)
{
v___y_1050_ = v___y_1132_;
v___y_1051_ = v___y_1133_;
v___y_1052_ = v___y_1134_;
v___y_1053_ = v___y_1136_;
v___y_1054_ = v___y_1137_;
v___y_1055_ = v___y_1138_;
v___y_1056_ = v___y_1139_;
v___y_1057_ = v___y_1151_;
v___y_1058_ = v___y_1140_;
v___y_1059_ = v___y_1141_;
v___y_1060_ = v___y_1142_;
v___y_1061_ = v___y_1143_;
v___y_1062_ = v___y_1144_;
v___y_1063_ = v___y_1145_;
v___y_1064_ = v___y_1146_;
v___y_1065_ = v___y_1149_;
v___y_1066_ = v___y_1148_;
v___y_1067_ = v___y_1150_;
v_pre_1068_ = v___x_1168_;
v___y_1069_ = v___y_1147_;
v___y_1070_ = v___y_1131_;
goto v___jp_1049_;
}
else
{
lean_object* v_ref_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v_ref_1171_ = lean_ctor_get(v___y_1147_, 5);
v___x_1172_ = l_Lean_SourceInfo_fromRef(v_ref_1171_, v___x_1152_);
v___x_1173_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__40));
v___x_1174_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__41));
lean_inc(v___x_1172_);
v___x_1175_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1172_);
lean_ctor_set(v___x_1175_, 1, v___x_1173_);
v___x_1176_ = l_Lean_Syntax_node2(v___x_1172_, v___x_1174_, v___x_1175_, v___x_1168_);
v___y_1050_ = v___y_1132_;
v___y_1051_ = v___y_1133_;
v___y_1052_ = v___y_1134_;
v___y_1053_ = v___y_1136_;
v___y_1054_ = v___y_1137_;
v___y_1055_ = v___y_1138_;
v___y_1056_ = v___y_1139_;
v___y_1057_ = v___y_1151_;
v___y_1058_ = v___y_1140_;
v___y_1059_ = v___y_1141_;
v___y_1060_ = v___y_1142_;
v___y_1061_ = v___y_1143_;
v___y_1062_ = v___y_1144_;
v___y_1063_ = v___y_1145_;
v___y_1064_ = v___y_1146_;
v___y_1065_ = v___y_1149_;
v___y_1066_ = v___y_1148_;
v___y_1067_ = v___y_1150_;
v_pre_1068_ = v___x_1176_;
v___y_1069_ = v___y_1147_;
v___y_1070_ = v___y_1131_;
goto v___jp_1049_;
}
}
}
else
{
lean_object* v_ref_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
lean_dec(v___y_1135_);
v_ref_1177_ = lean_ctor_get(v___y_1147_, 5);
v___x_1178_ = l_Lean_SourceInfo_fromRef(v_ref_1177_, v___y_1140_);
v___x_1179_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__69));
v___x_1180_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__70));
lean_inc(v___x_1178_);
v___x_1181_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1178_);
lean_ctor_set(v___x_1181_, 1, v___x_1180_);
v___x_1182_ = l_Lean_Syntax_node1(v___x_1178_, v___x_1179_, v___x_1181_);
v___y_1050_ = v___y_1132_;
v___y_1051_ = v___y_1133_;
v___y_1052_ = v___y_1134_;
v___y_1053_ = v___y_1136_;
v___y_1054_ = v___y_1137_;
v___y_1055_ = v___y_1138_;
v___y_1056_ = v___y_1139_;
v___y_1057_ = v___y_1151_;
v___y_1058_ = v___y_1140_;
v___y_1059_ = v___y_1141_;
v___y_1060_ = v___y_1142_;
v___y_1061_ = v___y_1143_;
v___y_1062_ = v___y_1144_;
v___y_1063_ = v___y_1145_;
v___y_1064_ = v___y_1146_;
v___y_1065_ = v___y_1149_;
v___y_1066_ = v___y_1148_;
v___y_1067_ = v___y_1150_;
v_pre_1068_ = v___x_1182_;
v___y_1069_ = v___y_1147_;
v___y_1070_ = v___y_1131_;
goto v___jp_1049_;
}
}
v___jp_1183_:
{
lean_object* v___x_1204_; size_t v_sz_1205_; size_t v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; uint8_t v___x_1210_; 
lean_inc_ref(v___y_1202_);
v___x_1204_ = l_Array_append___redArg(v___y_1202_, v___y_1203_);
lean_dec_ref(v___y_1203_);
v_sz_1205_ = lean_array_size(v___x_1204_);
v___x_1206_ = ((size_t)0ULL);
v___x_1207_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__0(v_sz_1205_, v___x_1206_, v___x_1204_);
v___x_1208_ = lean_mk_empty_array_with_capacity(v___y_1186_);
v___x_1209_ = lean_array_get_size(v___y_1202_);
v___x_1210_ = lean_nat_dec_lt(v___y_1186_, v___x_1209_);
if (v___x_1210_ == 0)
{
lean_dec_ref(v___y_1202_);
v___y_1131_ = v___y_1184_;
v___y_1132_ = v___y_1185_;
v___y_1133_ = v___y_1186_;
v___y_1134_ = v___y_1187_;
v___y_1135_ = v___y_1188_;
v___y_1136_ = v___y_1189_;
v___y_1137_ = v___y_1190_;
v___y_1138_ = v___x_1207_;
v___y_1139_ = v___y_1191_;
v___y_1140_ = v___y_1192_;
v___y_1141_ = v___y_1193_;
v___y_1142_ = v___y_1194_;
v___y_1143_ = v___y_1195_;
v___y_1144_ = v___y_1197_;
v___y_1145_ = v___y_1196_;
v___y_1146_ = v___y_1198_;
v___y_1147_ = v___y_1201_;
v___y_1148_ = v___y_1200_;
v___y_1149_ = v___y_1199_;
v___y_1150_ = v___x_1206_;
v___y_1151_ = v___x_1208_;
goto v___jp_1130_;
}
else
{
size_t v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = lean_usize_of_nat(v___x_1209_);
v___x_1212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__3(v___y_1202_, v___x_1206_, v___x_1211_, v___x_1208_);
lean_dec_ref(v___y_1202_);
v___y_1131_ = v___y_1184_;
v___y_1132_ = v___y_1185_;
v___y_1133_ = v___y_1186_;
v___y_1134_ = v___y_1187_;
v___y_1135_ = v___y_1188_;
v___y_1136_ = v___y_1189_;
v___y_1137_ = v___y_1190_;
v___y_1138_ = v___x_1207_;
v___y_1139_ = v___y_1191_;
v___y_1140_ = v___y_1192_;
v___y_1141_ = v___y_1193_;
v___y_1142_ = v___y_1194_;
v___y_1143_ = v___y_1195_;
v___y_1144_ = v___y_1197_;
v___y_1145_ = v___y_1196_;
v___y_1146_ = v___y_1198_;
v___y_1147_ = v___y_1201_;
v___y_1148_ = v___y_1200_;
v___y_1149_ = v___y_1199_;
v___y_1150_ = v___x_1206_;
v___y_1151_ = v___x_1212_;
goto v___jp_1130_;
}
}
v___jp_1214_:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; uint8_t v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; uint8_t v___x_1240_; 
v___x_1229_ = l_Lean_Syntax_getArg(v_decl_1213_, v___y_1218_);
v___x_1230_ = l_Lean_Syntax_getArg(v_decl_1213_, v___x_1048_);
lean_dec(v_decl_1213_);
v___x_1231_ = l_Lean_Syntax_getArg(v___x_1230_, v___y_1219_);
lean_dec(v___x_1230_);
v___x_1232_ = l_Lean_TSyntax_getId(v___x_1231_);
v___x_1233_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0___closed__0));
v___x_1234_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection_spec__0___closed__1));
lean_inc(v___x_1232_);
v___x_1235_ = l_Lean_Name_append(v___x_1232_, v___x_1234_);
v___x_1236_ = 0;
v___x_1237_ = l_Lean_mkIdentFrom(v___x_1231_, v___x_1235_, v___x_1236_);
v___x_1238_ = l_Lean_Syntax_getArg(v___x_1229_, v___y_1219_);
lean_dec(v___x_1229_);
v___x_1239_ = l_Lean_Syntax_getArgs(v___x_1238_);
lean_dec(v___x_1238_);
v___x_1240_ = l_Lean_Syntax_isNone(v___y_1226_);
if (v___x_1240_ == 0)
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1241_ = l_Lean_Syntax_getArg(v___y_1226_, v___y_1219_);
lean_dec(v___y_1226_);
v___x_1242_ = l_Lean_Syntax_getArg(v___x_1241_, v___x_1048_);
lean_dec(v___x_1241_);
v___x_1243_ = l_Lean_Syntax_getArgs(v___x_1242_);
lean_dec(v___x_1242_);
v___y_1184_ = v___y_1228_;
v___y_1185_ = v___y_1217_;
v___y_1186_ = v___y_1219_;
v___y_1187_ = v___x_1232_;
v___y_1188_ = v___y_1223_;
v___y_1189_ = v___y_1222_;
v___y_1190_ = v___y_1224_;
v___y_1191_ = v___y_1225_;
v___y_1192_ = v___x_1236_;
v___y_1193_ = v___x_1237_;
v___y_1194_ = v___x_1233_;
v___y_1195_ = v___y_1215_;
v___y_1196_ = v___y_1216_;
v___y_1197_ = v___y_1218_;
v___y_1198_ = v___y_1220_;
v___y_1199_ = v___y_1221_;
v___y_1200_ = v___x_1231_;
v___y_1201_ = v___y_1227_;
v___y_1202_ = v___x_1239_;
v___y_1203_ = v___x_1243_;
goto v___jp_1183_;
}
else
{
lean_object* v___x_1244_; 
lean_dec(v___y_1226_);
v___x_1244_ = lean_mk_empty_array_with_capacity(v___y_1219_);
v___y_1184_ = v___y_1228_;
v___y_1185_ = v___y_1217_;
v___y_1186_ = v___y_1219_;
v___y_1187_ = v___x_1232_;
v___y_1188_ = v___y_1223_;
v___y_1189_ = v___y_1222_;
v___y_1190_ = v___y_1224_;
v___y_1191_ = v___y_1225_;
v___y_1192_ = v___x_1236_;
v___y_1193_ = v___x_1237_;
v___y_1194_ = v___x_1233_;
v___y_1195_ = v___y_1215_;
v___y_1196_ = v___y_1216_;
v___y_1197_ = v___y_1218_;
v___y_1198_ = v___y_1220_;
v___y_1199_ = v___y_1221_;
v___y_1200_ = v___x_1231_;
v___y_1201_ = v___y_1227_;
v___y_1202_ = v___x_1239_;
v___y_1203_ = v___x_1244_;
goto v___jp_1183_;
}
}
v___jp_1245_:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1261_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__73));
v___x_1262_ = l_Lean_Macro_throwErrorAt___redArg(v___y_1260_, v___x_1261_, v___y_1259_, v___y_1250_);
lean_dec(v___y_1260_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v_a_1263_; 
v_a_1263_ = lean_ctor_get(v___x_1262_, 1);
lean_inc(v_a_1263_);
lean_dec_ref_known(v___x_1262_, 2);
v___y_1215_ = v___y_1254_;
v___y_1216_ = v___y_1255_;
v___y_1217_ = v___y_1246_;
v___y_1218_ = v___y_1256_;
v___y_1219_ = v___y_1247_;
v___y_1220_ = v___y_1257_;
v___y_1221_ = v___y_1258_;
v___y_1222_ = v___y_1248_;
v___y_1223_ = v___y_1249_;
v___y_1224_ = v___y_1251_;
v___y_1225_ = v___y_1252_;
v___y_1226_ = v___y_1253_;
v___y_1227_ = v___y_1259_;
v___y_1228_ = v_a_1263_;
goto v___jp_1214_;
}
else
{
lean_object* v_a_1264_; lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
lean_dec(v___y_1257_);
lean_dec(v___y_1255_);
lean_dec(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec(v_decl_1213_);
v_a_1264_ = lean_ctor_get(v___x_1262_, 0);
v_a_1265_ = lean_ctor_get(v___x_1262_, 1);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1267_ = v___x_1262_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_inc(v_a_1264_);
lean_dec(v___x_1262_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1264_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v_a_1265_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
}
v___jp_1273_:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1284_ = lean_unsigned_to_nat(4u);
v___x_1285_ = l_Lean_Syntax_getArg(v___y_1279_, v___x_1284_);
v___x_1286_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection(v___x_1285_, v___y_1282_, v___y_1283_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; lean_object* v_a_1288_; lean_object* v_fst_1289_; lean_object* v_snd_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_a_1287_);
v_a_1288_ = lean_ctor_get(v___x_1286_, 1);
lean_inc(v_a_1288_);
lean_dec_ref_known(v___x_1286_, 2);
v_fst_1289_ = lean_ctor_get(v_a_1287_, 0);
lean_inc(v_fst_1289_);
v_snd_1290_ = lean_ctor_get(v_a_1287_, 1);
lean_inc(v_snd_1290_);
lean_dec(v_a_1287_);
v___x_1291_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__4));
v___x_1292_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__5));
v___x_1293_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__75));
v___x_1294_ = l_Lean_Macro_hasDecl(v___x_1293_, v___y_1282_, v_a_1288_);
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_object* v_a_1295_; lean_object* v_a_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; uint8_t v___x_1299_; 
v_a_1295_ = lean_ctor_get(v___x_1294_, 0);
lean_inc(v_a_1295_);
v_a_1296_ = lean_ctor_get(v___x_1294_, 1);
lean_inc(v_a_1296_);
lean_dec_ref_known(v___x_1294_, 2);
lean_inc(v_decl_1213_);
v___x_1297_ = l_Lean_Syntax_setArg(v_decl_1213_, v___y_1275_, v_snd_1290_);
v___x_1298_ = l_Lean_Syntax_setArg(v_stx_634_, v___x_1048_, v___x_1297_);
v___x_1299_ = lean_unbox(v_a_1295_);
lean_dec(v_a_1295_);
if (v___x_1299_ == 0)
{
uint8_t v___x_1300_; 
v___x_1300_ = l_Lean_Syntax_isNone(v___y_1281_);
if (v___x_1300_ == 0)
{
lean_inc(v___y_1281_);
v___y_1246_ = v___y_1275_;
v___y_1247_ = v___y_1276_;
v___y_1248_ = v___y_1279_;
v___y_1249_ = v___y_1278_;
v___y_1250_ = v_a_1296_;
v___y_1251_ = v_fst_1289_;
v___y_1252_ = v___y_1280_;
v___y_1253_ = v___y_1281_;
v___y_1254_ = v___x_1291_;
v___y_1255_ = v___x_1298_;
v___y_1256_ = v___y_1274_;
v___y_1257_ = v___y_1277_;
v___y_1258_ = v___x_1292_;
v___y_1259_ = v___y_1282_;
v___y_1260_ = v___y_1281_;
goto v___jp_1245_;
}
else
{
uint8_t v___x_1301_; 
v___x_1301_ = l_Lean_Syntax_isNone(v___y_1278_);
if (v___x_1301_ == 0)
{
lean_inc(v___y_1278_);
v___y_1246_ = v___y_1275_;
v___y_1247_ = v___y_1276_;
v___y_1248_ = v___y_1279_;
v___y_1249_ = v___y_1278_;
v___y_1250_ = v_a_1296_;
v___y_1251_ = v_fst_1289_;
v___y_1252_ = v___y_1280_;
v___y_1253_ = v___y_1281_;
v___y_1254_ = v___x_1291_;
v___y_1255_ = v___x_1298_;
v___y_1256_ = v___y_1274_;
v___y_1257_ = v___y_1277_;
v___y_1258_ = v___x_1292_;
v___y_1259_ = v___y_1282_;
v___y_1260_ = v___y_1278_;
goto v___jp_1245_;
}
else
{
uint8_t v___x_1302_; 
v___x_1302_ = l_Lean_Syntax_isNone(v___y_1280_);
if (v___x_1302_ == 0)
{
lean_inc(v___y_1280_);
v___y_1246_ = v___y_1275_;
v___y_1247_ = v___y_1276_;
v___y_1248_ = v___y_1279_;
v___y_1249_ = v___y_1278_;
v___y_1250_ = v_a_1296_;
v___y_1251_ = v_fst_1289_;
v___y_1252_ = v___y_1280_;
v___y_1253_ = v___y_1281_;
v___y_1254_ = v___x_1291_;
v___y_1255_ = v___x_1298_;
v___y_1256_ = v___y_1274_;
v___y_1257_ = v___y_1277_;
v___y_1258_ = v___x_1292_;
v___y_1259_ = v___y_1282_;
v___y_1260_ = v___y_1280_;
goto v___jp_1245_;
}
else
{
lean_inc(v___y_1277_);
v___y_1246_ = v___y_1275_;
v___y_1247_ = v___y_1276_;
v___y_1248_ = v___y_1279_;
v___y_1249_ = v___y_1278_;
v___y_1250_ = v_a_1296_;
v___y_1251_ = v_fst_1289_;
v___y_1252_ = v___y_1280_;
v___y_1253_ = v___y_1281_;
v___y_1254_ = v___x_1291_;
v___y_1255_ = v___x_1298_;
v___y_1256_ = v___y_1274_;
v___y_1257_ = v___y_1277_;
v___y_1258_ = v___x_1292_;
v___y_1259_ = v___y_1282_;
v___y_1260_ = v___y_1277_;
goto v___jp_1245_;
}
}
}
}
else
{
v___y_1215_ = v___x_1291_;
v___y_1216_ = v___x_1298_;
v___y_1217_ = v___y_1275_;
v___y_1218_ = v___y_1274_;
v___y_1219_ = v___y_1276_;
v___y_1220_ = v___y_1277_;
v___y_1221_ = v___x_1292_;
v___y_1222_ = v___y_1279_;
v___y_1223_ = v___y_1278_;
v___y_1224_ = v_fst_1289_;
v___y_1225_ = v___y_1280_;
v___y_1226_ = v___y_1281_;
v___y_1227_ = v___y_1282_;
v___y_1228_ = v_a_1296_;
goto v___jp_1214_;
}
}
else
{
lean_object* v_a_1303_; lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_dec(v_snd_1290_);
lean_dec(v_fst_1289_);
lean_dec(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec(v_decl_1213_);
lean_dec(v_stx_634_);
v_a_1303_ = lean_ctor_get(v___x_1294_, 0);
v_a_1304_ = lean_ctor_get(v___x_1294_, 1);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1294_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_inc(v_a_1303_);
lean_dec(v___x_1294_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1303_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
else
{
lean_object* v_a_1312_; lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
lean_dec(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec(v_decl_1213_);
lean_dec(v_stx_634_);
v_a_1312_ = lean_ctor_get(v___x_1286_, 0);
v_a_1313_ = lean_ctor_get(v___x_1286_, 1);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v___x_1286_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_inc(v_a_1312_);
lean_dec(v___x_1286_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1320_;
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
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1312_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v_a_1313_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
v___jp_1321_:
{
if (v___y_1332_ == 0)
{
v___y_1274_ = v___y_1323_;
v___y_1275_ = v___y_1322_;
v___y_1276_ = v___y_1324_;
v___y_1277_ = v___y_1325_;
v___y_1278_ = v___y_1327_;
v___y_1279_ = v___y_1326_;
v___y_1280_ = v___y_1329_;
v___y_1281_ = v___y_1331_;
v___y_1282_ = v___y_1330_;
v___y_1283_ = v___y_1328_;
goto v___jp_1273_;
}
else
{
uint8_t v___x_1333_; 
v___x_1333_ = l_Lean_Syntax_isNone(v___y_1329_);
if (v___x_1333_ == 0)
{
v___y_1274_ = v___y_1323_;
v___y_1275_ = v___y_1322_;
v___y_1276_ = v___y_1324_;
v___y_1277_ = v___y_1325_;
v___y_1278_ = v___y_1327_;
v___y_1279_ = v___y_1326_;
v___y_1280_ = v___y_1329_;
v___y_1281_ = v___y_1331_;
v___y_1282_ = v___y_1330_;
v___y_1283_ = v___y_1328_;
goto v___jp_1273_;
}
else
{
lean_object* v___x_1334_; uint8_t v___x_1335_; 
v___x_1334_ = l_Lean_Syntax_getNumArgs(v___y_1325_);
v___x_1335_ = lean_nat_dec_eq(v___x_1334_, v___y_1324_);
lean_dec(v___x_1334_);
if (v___x_1335_ == 0)
{
v___y_1274_ = v___y_1323_;
v___y_1275_ = v___y_1322_;
v___y_1276_ = v___y_1324_;
v___y_1277_ = v___y_1325_;
v___y_1278_ = v___y_1327_;
v___y_1279_ = v___y_1326_;
v___y_1280_ = v___y_1329_;
v___y_1281_ = v___y_1331_;
v___y_1282_ = v___y_1330_;
v___y_1283_ = v___y_1328_;
goto v___jp_1273_;
}
else
{
lean_object* v___x_1336_; 
v___x_1336_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1328_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v_a_1337_; 
v_a_1337_ = lean_ctor_get(v___x_1336_, 1);
lean_inc(v_a_1337_);
lean_dec_ref_known(v___x_1336_, 2);
v___y_1274_ = v___y_1323_;
v___y_1275_ = v___y_1322_;
v___y_1276_ = v___y_1324_;
v___y_1277_ = v___y_1325_;
v___y_1278_ = v___y_1327_;
v___y_1279_ = v___y_1326_;
v___y_1280_ = v___y_1329_;
v___y_1281_ = v___y_1331_;
v___y_1282_ = v___y_1330_;
v___y_1283_ = v_a_1337_;
goto v___jp_1273_;
}
else
{
lean_object* v_a_1338_; lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1346_; 
lean_dec(v___y_1331_);
lean_dec(v___y_1329_);
lean_dec(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec(v___y_1325_);
lean_dec(v_decl_1213_);
lean_dec(v_stx_634_);
v_a_1338_ = lean_ctor_get(v___x_1336_, 0);
v_a_1339_ = lean_ctor_get(v___x_1336_, 1);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1341_ = v___x_1336_;
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_inc(v_a_1338_);
lean_dec(v___x_1336_);
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
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_a_1338_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v_a_1339_);
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
}
}
v___jp_1347_:
{
lean_object* v___x_1352_; lean_object* v_givenStx_1353_; lean_object* v_requiresStx_1354_; lean_object* v___x_1355_; lean_object* v_ensuresStx_1356_; lean_object* v_throwsStx_1357_; uint8_t v___x_1358_; 
v___x_1352_ = lean_unsigned_to_nat(0u);
v_givenStx_1353_ = l_Lean_Syntax_getArg(v___y_1349_, v___x_1352_);
v_requiresStx_1354_ = l_Lean_Syntax_getArg(v___y_1349_, v___x_1048_);
v___x_1355_ = lean_unsigned_to_nat(2u);
v_ensuresStx_1356_ = l_Lean_Syntax_getArg(v___y_1349_, v___x_1355_);
v_throwsStx_1357_ = l_Lean_Syntax_getArg(v___y_1349_, v___y_1348_);
v___x_1358_ = l_Lean_Syntax_isNone(v_givenStx_1353_);
if (v___x_1358_ == 0)
{
v___y_1322_ = v___y_1348_;
v___y_1323_ = v___x_1355_;
v___y_1324_ = v___x_1352_;
v___y_1325_ = v_throwsStx_1357_;
v___y_1326_ = v___y_1349_;
v___y_1327_ = v_requiresStx_1354_;
v___y_1328_ = v___y_1351_;
v___y_1329_ = v_ensuresStx_1356_;
v___y_1330_ = v___y_1350_;
v___y_1331_ = v_givenStx_1353_;
v___y_1332_ = v___x_1358_;
goto v___jp_1321_;
}
else
{
uint8_t v___x_1359_; 
v___x_1359_ = l_Lean_Syntax_isNone(v_requiresStx_1354_);
v___y_1322_ = v___y_1348_;
v___y_1323_ = v___x_1355_;
v___y_1324_ = v___x_1352_;
v___y_1325_ = v_throwsStx_1357_;
v___y_1326_ = v___y_1349_;
v___y_1327_ = v_requiresStx_1354_;
v___y_1328_ = v___y_1351_;
v___y_1329_ = v_ensuresStx_1356_;
v___y_1330_ = v___y_1350_;
v___y_1331_ = v_givenStx_1353_;
v___y_1332_ = v___x_1359_;
goto v___jp_1321_;
}
}
v___jp_1360_:
{
lean_object* v___x_1363_; lean_object* v_val_1364_; lean_object* v___x_1365_; uint8_t v___x_1366_; 
v___x_1363_ = lean_unsigned_to_nat(3u);
v_val_1364_ = l_Lean_Syntax_getArg(v_decl_1213_, v___x_1363_);
v___x_1365_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__1));
lean_inc(v_val_1364_);
v___x_1366_ = l_Lean_Syntax_isOfKind(v_val_1364_, v___x_1365_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1367_; 
v___x_1367_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1362_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v_a_1368_; 
v_a_1368_ = lean_ctor_get(v___x_1367_, 1);
lean_inc(v_a_1368_);
lean_dec_ref_known(v___x_1367_, 2);
v___y_1348_ = v___x_1363_;
v___y_1349_ = v_val_1364_;
v___y_1350_ = v___y_1361_;
v___y_1351_ = v_a_1368_;
goto v___jp_1347_;
}
else
{
lean_object* v_a_1369_; lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec(v_val_1364_);
lean_dec(v_decl_1213_);
lean_dec(v_stx_634_);
v_a_1369_ = lean_ctor_get(v___x_1367_, 0);
v_a_1370_ = lean_ctor_get(v___x_1367_, 1);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1367_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_inc(v_a_1369_);
lean_dec(v___x_1367_);
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
else
{
v___y_1348_ = v___x_1363_;
v___y_1349_ = v_val_1364_;
v___y_1350_ = v___y_1361_;
v___y_1351_ = v___y_1362_;
goto v___jp_1347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_expandDefContract___boxed(lean_object* v_stx_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l_Lean_Elab_Tactic_Do_expandDefContract(v_stx_1391_, v_a_1392_, v_a_1393_);
lean_dec_ref(v_a_1392_);
return v_res_1394_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1(){
_start:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1408_ = l_Lean_Elab_macroAttribute;
v___x_1409_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__0));
v___x_1410_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__2));
v___x_1411_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_expandDefContract___boxed), 3, 0);
v___x_1412_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1408_, v___x_1409_, v___x_1410_, v___x_1411_);
return v___x_1412_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1413_;
v_res_1413_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1();
stack->m_obj
 = v_res_1413_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___boxed(lean_object* v_a_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1();
return v_res_1415_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3(){
_start:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1418_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract__1___closed__2));
v___x_1419_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3___closed__0));
v___x_1420_ = l_Lean_addBuiltinDocString(v___x_1418_, v___x_1419_);
return v___x_1420_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1421_;
v_res_1421_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3();
stack->m_obj
 = v_res_1421_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3___boxed(lean_object* v_a_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_expandDefContract___regBuiltin_Lean_Elab_Tactic_Do_expandDefContract_docString__3();
return v_res_1423_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1424_; 
v___x_1424_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1424_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1425_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0);
v___x_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1425_);
return v___x_1426_;
}
}
lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg(){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__1);
return v___x_1428_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1429_;
v_res_1429_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg();
stack->m_obj
 = v_res_1429_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___boxed(lean_object* v___dummy_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg();
return v_res_1431_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg();
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0(lean_object* v_00_u03b2_1433_){
_start:
{
lean_object* v___x_1434_; 
v___x_1434_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___closed__0);
return v___x_1434_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1435_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0);
v___x_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1435_);
return v___x_1436_;
}
}
lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___redArg(){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___redArg___closed__0);
return v___x_1438_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1439_;
v_res_1439_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___redArg();
stack->m_obj
 = v_res_1439_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___redArg___boxed(lean_object* v___dummy_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___redArg();
return v_res_1441_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___redArg();
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1(lean_object* v_00_u03b2_1443_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___closed__0);
return v___x_1444_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__2___redArg(lean_object* v_as_1445_, size_t v_sz_1446_, size_t v_i_1447_, lean_object* v_b_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
uint8_t v___x_1454_; 
v___x_1454_ = lean_usize_dec_lt(v_i_1447_, v_sz_1446_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; 
v___x_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1455_, 0, v_b_1448_);
return v___x_1455_;
}
else
{
lean_object* v_a_1456_; uint8_t v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v_a_1456_ = lean_array_uget_borrowed(v_as_1445_, v_i_1447_);
v___x_1457_ = 0;
v___x_1458_ = lean_unsigned_to_nat(1000u);
lean_inc(v_a_1456_);
v___x_1459_ = l_Lean_Meta_SimpTheorems_addConst(v_b_1448_, v_a_1456_, v___x_1454_, v___x_1457_, v___x_1458_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; size_t v___x_1461_; size_t v___x_1462_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_a_1460_);
lean_dec_ref_known(v___x_1459_, 1);
v___x_1461_ = ((size_t)1ULL);
v___x_1462_ = lean_usize_add(v_i_1447_, v___x_1461_);
v_i_1447_ = v___x_1462_;
v_b_1448_ = v_a_1460_;
goto _start;
}
else
{
return v___x_1459_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1445_ = stack[0].m_obj;
size_t v_sz_1446_ = stack[1].m_num;
size_t v_i_1447_ = stack[2].m_num;
lean_object* v_b_1448_ = stack[3].m_obj;
lean_object* v___y_1449_ = stack[4].m_obj;
lean_object* v___y_1450_ = stack[5].m_obj;
lean_object* v___y_1451_ = stack[6].m_obj;
lean_object* v___y_1452_ = stack[7].m_obj;
lean_object* v_res_1464_;
v_res_1464_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__2___redArg(v_as_1445_, v_sz_1446_, v_i_1447_, v_b_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
stack->m_obj
 = v_res_1464_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__2___redArg___boxed(lean_object* v_as_1465_, lean_object* v_sz_1466_, lean_object* v_i_1467_, lean_object* v_b_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
size_t v_sz_boxed_1474_; size_t v_i_boxed_1475_; lean_object* v_res_1476_; 
v_sz_boxed_1474_ = lean_unbox_usize(v_sz_1466_);
lean_dec(v_sz_1466_);
v_i_boxed_1475_ = lean_unbox_usize(v_i_1467_);
lean_dec(v_i_1467_);
v_res_1476_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__2___redArg(v_as_1465_, v_sz_boxed_1474_, v_i_boxed_1475_, v_b_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec_ref(v_as_1465_);
return v_res_1476_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__0(void){
_start:
{
lean_object* v___x_1477_; 
v___x_1477_ = l_Lean_Meta_DiscrTree_empty___redArg();
return v___x_1477_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__1(void){
_start:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1478_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0);
v___x_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1478_);
return v___x_1479_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__2(void){
_start:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v_thms_1484_; 
v___x_1480_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__1, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__1);
v___x_1481_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__1___closed__0);
v___x_1482_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___closed__0);
v___x_1483_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__0, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__0);
v_thms_1484_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_thms_1484_, 0, v___x_1483_);
lean_ctor_set(v_thms_1484_, 1, v___x_1483_);
lean_ctor_set(v_thms_1484_, 2, v___x_1482_);
lean_ctor_set(v_thms_1484_, 3, v___x_1481_);
lean_ctor_set(v_thms_1484_, 4, v___x_1482_);
lean_ctor_set(v_thms_1484_, 5, v___x_1480_);
return v_thms_1484_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__5(void){
_start:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1494_ = lean_unsigned_to_nat(0u);
v___x_1495_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__1, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__1);
v___x_1496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1495_);
lean_ctor_set(v___x_1496_, 1, v___x_1494_);
return v___x_1496_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__6(void){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1497_ = lean_unsigned_to_nat(32u);
v___x_1498_ = lean_mk_empty_array_with_capacity(v___x_1497_);
v___x_1499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1498_);
return v___x_1499_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__7(void){
_start:
{
size_t v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1500_ = ((size_t)5ULL);
v___x_1501_ = lean_unsigned_to_nat(0u);
v___x_1502_ = lean_unsigned_to_nat(32u);
v___x_1503_ = lean_mk_empty_array_with_capacity(v___x_1502_);
v___x_1504_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__6, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__6);
v___x_1505_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1505_, 0, v___x_1504_);
lean_ctor_set(v___x_1505_, 1, v___x_1503_);
lean_ctor_set(v___x_1505_, 2, v___x_1501_);
lean_ctor_set(v___x_1505_, 3, v___x_1501_);
lean_ctor_set_usize(v___x_1505_, 4, v___x_1500_);
return v___x_1505_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__8(void){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1506_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__7, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__7);
v___x_1507_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__1, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__1);
v___x_1508_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1507_);
lean_ctor_set(v___x_1508_, 1, v___x_1507_);
lean_ctor_set(v___x_1508_, 2, v___x_1507_);
lean_ctor_set(v___x_1508_, 3, v___x_1506_);
return v___x_1508_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__9(void){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1509_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__8, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__8_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__8);
v___x_1510_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__5, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__5);
v___x_1511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1510_);
lean_ctor_set(v___x_1511_, 1, v___x_1509_);
return v___x_1511_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith(lean_object* v_names_1512_, lean_object* v_e_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_){
_start:
{
lean_object* v_thms_1521_; size_t v_sz_1522_; size_t v___x_1523_; lean_object* v___x_1524_; 
v_thms_1521_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__2, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__2);
v_sz_1522_ = lean_array_size(v_names_1512_);
v___x_1523_ = ((size_t)0ULL);
v___x_1524_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__2___redArg(v_names_1512_, v_sz_1522_, v___x_1523_, v_thms_1521_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v___x_1526_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_a_1525_);
lean_dec_ref_known(v___x_1524_, 1);
v___x_1526_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_1519_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_a_1527_);
lean_dec_ref_known(v___x_1526_, 1);
v___x_1528_ = lean_box(0);
v___x_1529_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__3));
v___x_1530_ = lean_unsigned_to_nat(1u);
v___x_1531_ = lean_mk_empty_array_with_capacity(v___x_1530_);
v___x_1532_ = lean_array_push(v___x_1531_, v_a_1525_);
v___x_1533_ = l_Lean_Options_empty;
v___x_1534_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1529_, v___x_1532_, v_a_1527_, v___x_1533_, v_a_1516_, v_a_1518_, v_a_1519_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v_a_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_a_1535_);
lean_dec_ref_known(v___x_1534_, 1);
v___x_1536_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__4));
v___x_1537_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__9, &l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___closed__9);
v___x_1538_ = l_Lean_Meta_simp(v_e_1513_, v_a_1535_, v___x_1536_, v___x_1528_, v___x_1537_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1548_; 
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1541_ = v___x_1538_;
v_isShared_1542_ = v_isSharedCheck_1548_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1538_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1548_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v_fst_1543_; lean_object* v_expr_1544_; lean_object* v___x_1546_; 
v_fst_1543_ = lean_ctor_get(v_a_1539_, 0);
lean_inc(v_fst_1543_);
lean_dec(v_a_1539_);
v_expr_1544_ = lean_ctor_get(v_fst_1543_, 0);
lean_inc_ref(v_expr_1544_);
lean_dec(v_fst_1543_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 0, v_expr_1544_);
v___x_1546_ = v___x_1541_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_expr_1544_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
else
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1556_; 
v_a_1549_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1551_ = v___x_1538_;
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1538_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1554_; 
if (v_isShared_1552_ == 0)
{
v___x_1554_ = v___x_1551_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_a_1549_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_dec_ref(v_e_1513_);
v_a_1557_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1534_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1534_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
else
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1572_; 
lean_dec(v_a_1525_);
lean_dec_ref(v_e_1513_);
v_a_1565_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v___x_1526_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1526_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1570_; 
if (v_isShared_1568_ == 0)
{
v___x_1570_ = v___x_1567_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1565_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
else
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
lean_dec_ref(v_e_1513_);
v_a_1573_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1524_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1524_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_a_1573_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_0interp(lean_interpreter_value* stack)
{
lean_object* v_names_1512_ = stack[0].m_obj;
lean_object* v_e_1513_ = stack[1].m_obj;
lean_object* v_a_1514_ = stack[2].m_obj;
lean_object* v_a_1515_ = stack[3].m_obj;
lean_object* v_a_1516_ = stack[4].m_obj;
lean_object* v_a_1517_ = stack[5].m_obj;
lean_object* v_a_1518_ = stack[6].m_obj;
lean_object* v_a_1519_ = stack[7].m_obj;
lean_object* v_res_1581_;
v_res_1581_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith(v_names_1512_, v_e_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_);
stack->m_obj
 = v_res_1581_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith___boxed(lean_object* v_names_1582_, lean_object* v_e_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith(v_names_1582_, v_e_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_);
lean_dec(v_a_1589_);
lean_dec_ref(v_a_1588_);
lean_dec(v_a_1587_);
lean_dec_ref(v_a_1586_);
lean_dec(v_a_1585_);
lean_dec_ref(v_a_1584_);
lean_dec_ref(v_names_1582_);
return v_res_1591_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__2(lean_object* v_as_1592_, size_t v_sz_1593_, size_t v_i_1594_, lean_object* v_b_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v___x_1603_; 
v___x_1603_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__2___redArg(v_as_1592_, v_sz_1593_, v_i_1594_, v_b_1595_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
return v___x_1603_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1592_ = stack[0].m_obj;
size_t v_sz_1593_ = stack[1].m_num;
size_t v_i_1594_ = stack[2].m_num;
lean_object* v_b_1595_ = stack[3].m_obj;
lean_object* v___y_1596_ = stack[4].m_obj;
lean_object* v___y_1597_ = stack[5].m_obj;
lean_object* v___y_1598_ = stack[6].m_obj;
lean_object* v___y_1599_ = stack[7].m_obj;
lean_object* v___y_1600_ = stack[8].m_obj;
lean_object* v___y_1601_ = stack[9].m_obj;
lean_object* v_res_1604_;
v_res_1604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__2(v_as_1592_, v_sz_1593_, v_i_1594_, v_b_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
stack->m_obj
 = v_res_1604_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__2___boxed(lean_object* v_as_1605_, lean_object* v_sz_1606_, lean_object* v_i_1607_, lean_object* v_b_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
size_t v_sz_boxed_1616_; size_t v_i_boxed_1617_; lean_object* v_res_1618_; 
v_sz_boxed_1616_ = lean_unbox_usize(v_sz_1606_);
lean_dec(v_sz_1606_);
v_i_boxed_1617_ = lean_unbox_usize(v_i_1607_);
lean_dec(v_i_1607_);
v_res_1618_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__2(v_as_1605_, v_sz_boxed_1616_, v_i_boxed_1617_, v_b_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec_ref(v_as_1605_);
return v_res_1618_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0___redArg(lean_object* v_e_1619_, lean_object* v___y_1620_){
_start:
{
uint8_t v___x_1622_; 
v___x_1622_ = l_Lean_Expr_hasMVar(v_e_1619_);
if (v___x_1622_ == 0)
{
lean_object* v___x_1623_; 
v___x_1623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1623_, 0, v_e_1619_);
return v___x_1623_;
}
else
{
lean_object* v___x_1624_; lean_object* v_mctx_1625_; lean_object* v___x_1626_; lean_object* v_fst_1627_; lean_object* v_snd_1628_; lean_object* v___x_1629_; lean_object* v_cache_1630_; lean_object* v_zetaDeltaFVarIds_1631_; lean_object* v_postponed_1632_; lean_object* v_diag_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1642_; 
v___x_1624_ = lean_st_ref_get(v___y_1620_);
v_mctx_1625_ = lean_ctor_get(v___x_1624_, 0);
lean_inc_ref(v_mctx_1625_);
lean_dec(v___x_1624_);
v___x_1626_ = l_Lean_instantiateMVarsCore(v_mctx_1625_, v_e_1619_);
v_fst_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_fst_1627_);
v_snd_1628_ = lean_ctor_get(v___x_1626_, 1);
lean_inc(v_snd_1628_);
lean_dec_ref(v___x_1626_);
v___x_1629_ = lean_st_ref_take(v___y_1620_);
v_cache_1630_ = lean_ctor_get(v___x_1629_, 1);
v_zetaDeltaFVarIds_1631_ = lean_ctor_get(v___x_1629_, 2);
v_postponed_1632_ = lean_ctor_get(v___x_1629_, 3);
v_diag_1633_ = lean_ctor_get(v___x_1629_, 4);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1642_ == 0)
{
lean_object* v_unused_1643_; 
v_unused_1643_ = lean_ctor_get(v___x_1629_, 0);
lean_dec(v_unused_1643_);
v___x_1635_ = v___x_1629_;
v_isShared_1636_ = v_isSharedCheck_1642_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_diag_1633_);
lean_inc(v_postponed_1632_);
lean_inc(v_zetaDeltaFVarIds_1631_);
lean_inc(v_cache_1630_);
lean_dec(v___x_1629_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1642_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 0, v_snd_1628_);
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_snd_1628_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v_cache_1630_);
lean_ctor_set(v_reuseFailAlloc_1641_, 2, v_zetaDeltaFVarIds_1631_);
lean_ctor_set(v_reuseFailAlloc_1641_, 3, v_postponed_1632_);
lean_ctor_set(v_reuseFailAlloc_1641_, 4, v_diag_1633_);
v___x_1638_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1639_ = lean_st_ref_put(v___y_1620_, v___x_1638_);
v___x_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1640_, 0, v_fst_1627_);
return v___x_1640_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1619_ = stack[0].m_obj;
lean_object* v___y_1620_ = stack[1].m_obj;
lean_object* v_res_1644_;
v_res_1644_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0___redArg(v_e_1619_, v___y_1620_);
stack->m_obj
 = v_res_1644_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0___redArg___boxed(lean_object* v_e_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0___redArg(v_e_1645_, v___y_1646_);
lean_dec(v___y_1646_);
return v_res_1648_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0(lean_object* v_e_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0___redArg(v_e_1649_, v___y_1653_);
return v___x_1657_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1649_ = stack[0].m_obj;
lean_object* v___y_1650_ = stack[1].m_obj;
lean_object* v___y_1651_ = stack[2].m_obj;
lean_object* v___y_1652_ = stack[3].m_obj;
lean_object* v___y_1653_ = stack[4].m_obj;
lean_object* v___y_1654_ = stack[5].m_obj;
lean_object* v___y_1655_ = stack[6].m_obj;
lean_object* v_res_1658_;
v_res_1658_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0(v_e_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_);
stack->m_obj
 = v_res_1658_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0___boxed(lean_object* v_e_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0(v_e_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
return v_res_1667_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__0(lean_object* v_e_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
lean_object* v___x_1681_; uint8_t v___x_1682_; 
v___x_1681_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__10));
v___x_1682_ = l_Lean_Expr_isAppOf(v_e_1670_, v___x_1681_);
if (v___x_1682_ == 0)
{
lean_dec_ref(v_e_1670_);
goto v___jp_1678_;
}
else
{
lean_object* v___x_1683_; 
v___x_1683_ = l_Lean_Meta_unfoldProjInst_x3f(v_e_1670_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1699_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1686_ = v___x_1683_;
v_isShared_1687_ = v_isSharedCheck_1699_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_dec(v___x_1683_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1699_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
if (lean_obj_tag(v_a_1684_) == 1)
{
lean_object* v_val_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1698_; 
v_val_1688_ = lean_ctor_get(v_a_1684_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v_a_1684_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1690_ = v_a_1684_;
v_isShared_1691_ = v_isSharedCheck_1698_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_val_1688_);
lean_dec(v_a_1684_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1698_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_val_1688_);
v___x_1693_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
lean_object* v___x_1695_; 
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 0, v___x_1693_);
v___x_1695_ = v___x_1686_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v___x_1693_);
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
lean_del_object(v___x_1686_);
lean_dec(v_a_1684_);
goto v___jp_1678_;
}
}
}
else
{
lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1707_; 
v_a_1700_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1702_ = v___x_1683_;
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___x_1683_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1705_; 
if (v_isShared_1703_ == 0)
{
v___x_1705_ = v___x_1702_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_a_1700_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
}
v___jp_1678_:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__0___closed__0));
v___x_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
return v___x_1680_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1670_ = stack[0].m_obj;
lean_object* v___y_1671_ = stack[1].m_obj;
lean_object* v___y_1672_ = stack[2].m_obj;
lean_object* v___y_1673_ = stack[3].m_obj;
lean_object* v___y_1674_ = stack[4].m_obj;
lean_object* v___y_1675_ = stack[5].m_obj;
lean_object* v___y_1676_ = stack[6].m_obj;
lean_object* v_res_1708_;
v_res_1708_ = l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__0(v_e_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
stack->m_obj
 = v_res_1708_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__0___boxed(lean_object* v_e_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__0(v_e_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
lean_dec(v___y_1715_);
lean_dec_ref(v___y_1714_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
return v_res_1717_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__1(lean_object* v_x_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1726_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__0___closed__0));
v___x_1727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1726_);
return v___x_1727_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1718_ = stack[0].m_obj;
lean_object* v___y_1719_ = stack[1].m_obj;
lean_object* v___y_1720_ = stack[2].m_obj;
lean_object* v___y_1721_ = stack[3].m_obj;
lean_object* v___y_1722_ = stack[4].m_obj;
lean_object* v___y_1723_ = stack[5].m_obj;
lean_object* v___y_1724_ = stack[6].m_obj;
lean_object* v_res_1728_;
v_res_1728_ = l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__1(v_x_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
stack->m_obj
 = v_res_1728_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__1___boxed(lean_object* v_x_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Lean_Elab_Tactic_Do_elabContractEPosts___lam__1(v_x_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec_ref(v_x_1729_);
return v_res_1737_;
}
}
lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___lam__0(lean_object* v_00_u03b1_1738_, lean_object* v_x_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1747_ = lean_apply_1(v_x_1739_, lean_box(0));
v___x_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1747_);
return v___x_1748_;
}
}
LEAN_EXPORT void l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1739_ = stack[1].m_obj;
lean_object* v___y_1740_ = stack[2].m_obj;
lean_object* v___y_1741_ = stack[3].m_obj;
lean_object* v___y_1742_ = stack[4].m_obj;
lean_object* v___y_1743_ = stack[5].m_obj;
lean_object* v___y_1744_ = stack[6].m_obj;
lean_object* v___y_1745_ = stack[7].m_obj;
lean_object* v_res_1749_;
v_res_1749_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___lam__0(lean_box(0), v_x_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
stack->m_obj
 = v_res_1749_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___lam__0___boxed(lean_object* v_00_u03b1_1750_, lean_object* v_x_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___lam__0(v_00_u03b1_1750_, v_x_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
return v_res_1759_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__3(void){
_start:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1765_ = l_Lean_maxRecDepthErrorMessage;
v___x_1766_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1766_, 0, v___x_1765_);
return v___x_1766_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__4(void){
_start:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1767_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__3);
v___x_1768_ = l_Lean_MessageData_ofFormat(v___x_1767_);
return v___x_1768_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__5(void){
_start:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1769_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__4);
v___x_1770_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__2));
v___x_1771_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1770_);
lean_ctor_set(v___x_1771_, 1, v___x_1769_);
return v___x_1771_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg(lean_object* v_ref_1772_){
_start:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1774_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___closed__5);
v___x_1775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1775_, 0, v_ref_1772_);
lean_ctor_set(v___x_1775_, 1, v___x_1774_);
v___x_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1775_);
return v___x_1776_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1772_ = stack[0].m_obj;
lean_object* v_res_1777_;
v_res_1777_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_1772_);
stack->m_obj
 = v_res_1777_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg___boxed(lean_object* v_ref_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_1778_);
return v_res_1780_;
}
}
lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10___redArg(lean_object* v_x_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v___y_1791_; lean_object* v_toCold_1800_; lean_object* v_currRecDepth_1801_; lean_object* v_ref_1802_; uint16_t v_optionFlags_1803_; uint8_t v_suppressElabErrors_1804_; uint8_t v_isRecordingDeps_1805_; lean_object* v_maxRecDepth_1811_; lean_object* v___x_1812_; uint8_t v___x_1813_; 
v_toCold_1800_ = lean_ctor_get(v___y_1787_, 0);
v_currRecDepth_1801_ = lean_ctor_get(v___y_1787_, 1);
v_ref_1802_ = lean_ctor_get(v___y_1787_, 2);
v_optionFlags_1803_ = lean_ctor_get_uint16(v___y_1787_, sizeof(void*)*3);
v_suppressElabErrors_1804_ = lean_ctor_get_uint8(v___y_1787_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1805_ = lean_ctor_get_uint8(v___y_1787_, sizeof(void*)*3 + 3);
v_maxRecDepth_1811_ = lean_ctor_get(v_toCold_1800_, 3);
v___x_1812_ = lean_unsigned_to_nat(0u);
v___x_1813_ = lean_nat_dec_eq(v_maxRecDepth_1811_, v___x_1812_);
if (v___x_1813_ == 0)
{
uint8_t v___x_1814_; 
v___x_1814_ = lean_nat_dec_eq(v_currRecDepth_1801_, v_maxRecDepth_1811_);
if (v___x_1814_ == 0)
{
goto v___jp_1806_;
}
else
{
lean_object* v___x_1815_; 
lean_dec_ref(v_x_1781_);
lean_inc(v_ref_1802_);
v___x_1815_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_1802_);
v___y_1791_ = v___x_1815_;
goto v___jp_1790_;
}
}
else
{
goto v___jp_1806_;
}
v___jp_1790_:
{
if (lean_obj_tag(v___y_1791_) == 0)
{
return v___y_1791_;
}
else
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1799_; 
v_a_1792_ = lean_ctor_get(v___y_1791_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___y_1791_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1794_ = v___y_1791_;
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___y_1791_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1797_; 
if (v_isShared_1795_ == 0)
{
v___x_1797_ = v___x_1794_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_a_1792_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
v___jp_1806_:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1807_ = lean_unsigned_to_nat(1u);
v___x_1808_ = lean_nat_add(v_currRecDepth_1801_, v___x_1807_);
lean_inc(v_ref_1802_);
lean_inc_ref(v_toCold_1800_);
v___x_1809_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1809_, 0, v_toCold_1800_);
lean_ctor_set(v___x_1809_, 1, v___x_1808_);
lean_ctor_set(v___x_1809_, 2, v_ref_1802_);
lean_ctor_set_uint16(v___x_1809_, sizeof(void*)*3, v_optionFlags_1803_);
lean_ctor_set_uint8(v___x_1809_, sizeof(void*)*3 + 2, v_suppressElabErrors_1804_);
lean_ctor_set_uint8(v___x_1809_, sizeof(void*)*3 + 3, v_isRecordingDeps_1805_);
lean_inc(v___y_1788_);
lean_inc(v___y_1786_);
lean_inc_ref(v___y_1785_);
lean_inc(v___y_1784_);
lean_inc_ref(v___y_1783_);
lean_inc(v___y_1782_);
v___x_1810_ = lean_apply_8(v_x_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___x_1809_, v___y_1788_, lean_box(0));
v___y_1791_ = v___x_1810_;
goto v___jp_1790_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1781_ = stack[0].m_obj;
lean_object* v___y_1782_ = stack[1].m_obj;
lean_object* v___y_1783_ = stack[2].m_obj;
lean_object* v___y_1784_ = stack[3].m_obj;
lean_object* v___y_1785_ = stack[4].m_obj;
lean_object* v___y_1786_ = stack[5].m_obj;
lean_object* v___y_1787_ = stack[6].m_obj;
lean_object* v___y_1788_ = stack[7].m_obj;
lean_object* v_res_1816_;
v_res_1816_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10___redArg(v_x_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
stack->m_obj
 = v_res_1816_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10___redArg___boxed(lean_object* v_x_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10___redArg(v_x_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec(v___y_1818_);
return v_res_1826_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__2(lean_object* v___x_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1827_);
return v___x_1835_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1827_ = stack[0].m_obj;
lean_object* v___y_1828_ = stack[1].m_obj;
lean_object* v___y_1829_ = stack[2].m_obj;
lean_object* v___y_1830_ = stack[3].m_obj;
lean_object* v___y_1831_ = stack[4].m_obj;
lean_object* v___y_1832_ = stack[5].m_obj;
lean_object* v___y_1833_ = stack[6].m_obj;
lean_object* v_res_1836_;
v_res_1836_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__2(v___x_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_);
stack->m_obj
 = v_res_1836_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__2___boxed(lean_object* v___x_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__2(v___x_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
return v_res_1845_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(lean_object* v_k_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v_b_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v___x_1856_; 
lean_inc(v___y_1854_);
lean_inc_ref(v___y_1853_);
lean_inc(v___y_1852_);
lean_inc_ref(v___y_1851_);
lean_inc(v___y_1849_);
lean_inc_ref(v___y_1848_);
lean_inc(v___y_1847_);
v___x_1856_ = lean_apply_9(v_k_1846_, v_b_1850_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, lean_box(0));
return v___x_1856_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1846_ = stack[0].m_obj;
lean_object* v___y_1847_ = stack[1].m_obj;
lean_object* v___y_1848_ = stack[2].m_obj;
lean_object* v___y_1849_ = stack[3].m_obj;
lean_object* v_b_1850_ = stack[4].m_obj;
lean_object* v___y_1851_ = stack[5].m_obj;
lean_object* v___y_1852_ = stack[6].m_obj;
lean_object* v___y_1853_ = stack[7].m_obj;
lean_object* v___y_1854_ = stack[8].m_obj;
lean_object* v_res_1857_;
v_res_1857_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(v_k_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v_b_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
stack->m_obj
 = v_res_1857_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed(lean_object* v_k_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v_b_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(v_k_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v_b_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
return v_res_1868_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg(lean_object* v_name_1869_, uint8_t v_bi_1870_, lean_object* v_type_1871_, lean_object* v_k_1872_, uint8_t v_kind_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v___f_1882_; lean_object* v___x_1883_; 
lean_inc(v___y_1876_);
lean_inc_ref(v___y_1875_);
lean_inc(v___y_1874_);
v___f_1882_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1882_, 0, v_k_1872_);
lean_closure_set(v___f_1882_, 1, v___y_1874_);
lean_closure_set(v___f_1882_, 2, v___y_1875_);
lean_closure_set(v___f_1882_, 3, v___y_1876_);
v___x_1883_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1869_, v_bi_1870_, v_type_1871_, v___f_1882_, v_kind_1873_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
if (lean_obj_tag(v___x_1883_) == 0)
{
return v___x_1883_;
}
else
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1886_ = v___x_1883_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1883_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
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
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1869_ = stack[0].m_obj;
uint8_t v_bi_1870_ = stack[1].m_num;
lean_object* v_type_1871_ = stack[2].m_obj;
lean_object* v_k_1872_ = stack[3].m_obj;
uint8_t v_kind_1873_ = stack[4].m_num;
lean_object* v___y_1874_ = stack[5].m_obj;
lean_object* v___y_1875_ = stack[6].m_obj;
lean_object* v___y_1876_ = stack[7].m_obj;
lean_object* v___y_1877_ = stack[8].m_obj;
lean_object* v___y_1878_ = stack[9].m_obj;
lean_object* v___y_1879_ = stack[10].m_obj;
lean_object* v___y_1880_ = stack[11].m_obj;
lean_object* v_res_1892_;
v_res_1892_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg(v_name_1869_, v_bi_1870_, v_type_1871_, v_k_1872_, v_kind_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
stack->m_obj
 = v_res_1892_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg___boxed(lean_object* v_name_1893_, lean_object* v_bi_1894_, lean_object* v_type_1895_, lean_object* v_k_1896_, lean_object* v_kind_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
uint8_t v_bi_boxed_1906_; uint8_t v_kind_boxed_1907_; lean_object* v_res_1908_; 
v_bi_boxed_1906_ = lean_unbox(v_bi_1894_);
v_kind_boxed_1907_ = lean_unbox(v_kind_1897_);
v_res_1908_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg(v_name_1893_, v_bi_boxed_1906_, v_type_1895_, v_k_1896_, v_kind_boxed_1907_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
return v_res_1908_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11___redArg(lean_object* v_name_1909_, lean_object* v_type_1910_, lean_object* v_val_1911_, lean_object* v_k_1912_, uint8_t v_nondep_1913_, uint8_t v_kind_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v___f_1923_; lean_object* v___x_1924_; 
lean_inc(v___y_1917_);
lean_inc_ref(v___y_1916_);
lean_inc(v___y_1915_);
v___f_1923_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1923_, 0, v_k_1912_);
lean_closure_set(v___f_1923_, 1, v___y_1915_);
lean_closure_set(v___f_1923_, 2, v___y_1916_);
lean_closure_set(v___f_1923_, 3, v___y_1917_);
v___x_1924_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1909_, v_type_1910_, v_val_1911_, v___f_1923_, v_nondep_1913_, v_kind_1914_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
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
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1909_ = stack[0].m_obj;
lean_object* v_type_1910_ = stack[1].m_obj;
lean_object* v_val_1911_ = stack[2].m_obj;
lean_object* v_k_1912_ = stack[3].m_obj;
uint8_t v_nondep_1913_ = stack[4].m_num;
uint8_t v_kind_1914_ = stack[5].m_num;
lean_object* v___y_1915_ = stack[6].m_obj;
lean_object* v___y_1916_ = stack[7].m_obj;
lean_object* v___y_1917_ = stack[8].m_obj;
lean_object* v___y_1918_ = stack[9].m_obj;
lean_object* v___y_1919_ = stack[10].m_obj;
lean_object* v___y_1920_ = stack[11].m_obj;
lean_object* v___y_1921_ = stack[12].m_obj;
lean_object* v_res_1933_;
v_res_1933_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11___redArg(v_name_1909_, v_type_1910_, v_val_1911_, v_k_1912_, v_nondep_1913_, v_kind_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
stack->m_obj
 = v_res_1933_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11___redArg___boxed(lean_object* v_name_1934_, lean_object* v_type_1935_, lean_object* v_val_1936_, lean_object* v_k_1937_, lean_object* v_nondep_1938_, lean_object* v_kind_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
uint8_t v_nondep_boxed_1948_; uint8_t v_kind_boxed_1949_; lean_object* v_res_1950_; 
v_nondep_boxed_1948_ = lean_unbox(v_nondep_1938_);
v_kind_boxed_1949_ = lean_unbox(v_kind_1939_);
v_res_1950_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11___redArg(v_name_1934_, v_type_1935_, v_val_1936_, v_k_1937_, v_nondep_boxed_1948_, v_kind_boxed_1949_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
lean_dec(v___y_1940_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5_spec__6___redArg(lean_object* v_a_1951_, lean_object* v_x_1952_){
_start:
{
if (lean_obj_tag(v_x_1952_) == 0)
{
lean_object* v___x_1953_; 
v___x_1953_ = lean_box(0);
return v___x_1953_;
}
else
{
lean_object* v_key_1954_; lean_object* v_value_1955_; lean_object* v_tail_1956_; uint8_t v___x_1957_; 
v_key_1954_ = lean_ctor_get(v_x_1952_, 0);
v_value_1955_ = lean_ctor_get(v_x_1952_, 1);
v_tail_1956_ = lean_ctor_get(v_x_1952_, 2);
v___x_1957_ = l_Lean_ExprStructEq_beq(v_key_1954_, v_a_1951_);
if (v___x_1957_ == 0)
{
v_x_1952_ = v_tail_1956_;
goto _start;
}
else
{
lean_object* v___x_1959_; 
lean_inc(v_value_1955_);
v___x_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1959_, 0, v_value_1955_);
return v___x_1959_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object* v_a_1960_, lean_object* v_x_1961_){
_start:
{
lean_object* v_res_1962_; 
v_res_1962_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5_spec__6___redArg(v_a_1960_, v_x_1961_);
lean_dec(v_x_1961_);
lean_dec_ref(v_a_1960_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5___redArg(lean_object* v_m_1963_, lean_object* v_a_1964_){
_start:
{
lean_object* v_buckets_1965_; lean_object* v___x_1966_; uint64_t v___x_1967_; uint64_t v___x_1968_; uint64_t v___x_1969_; uint64_t v_fold_1970_; uint64_t v___x_1971_; uint64_t v___x_1972_; uint64_t v___x_1973_; size_t v___x_1974_; size_t v___x_1975_; size_t v___x_1976_; size_t v___x_1977_; size_t v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v_buckets_1965_ = lean_ctor_get(v_m_1963_, 1);
v___x_1966_ = lean_array_get_size(v_buckets_1965_);
v___x_1967_ = l_Lean_ExprStructEq_hash(v_a_1964_);
v___x_1968_ = 32ULL;
v___x_1969_ = lean_uint64_shift_right(v___x_1967_, v___x_1968_);
v_fold_1970_ = lean_uint64_xor(v___x_1967_, v___x_1969_);
v___x_1971_ = 16ULL;
v___x_1972_ = lean_uint64_shift_right(v_fold_1970_, v___x_1971_);
v___x_1973_ = lean_uint64_xor(v_fold_1970_, v___x_1972_);
v___x_1974_ = lean_uint64_to_usize(v___x_1973_);
v___x_1975_ = lean_usize_of_nat(v___x_1966_);
v___x_1976_ = ((size_t)1ULL);
v___x_1977_ = lean_usize_sub(v___x_1975_, v___x_1976_);
v___x_1978_ = lean_usize_land(v___x_1974_, v___x_1977_);
v___x_1979_ = lean_array_uget_borrowed(v_buckets_1965_, v___x_1978_);
v___x_1980_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5_spec__6___redArg(v_a_1964_, v___x_1979_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5___redArg___boxed(lean_object* v_m_1981_, lean_object* v_a_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5___redArg(v_m_1981_, v_a_1982_);
lean_dec_ref(v_a_1982_);
lean_dec_ref(v_m_1981_);
return v_res_1983_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_1984_, lean_object* v_x_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1993_ = lean_apply_1(v_x_1985_, lean_box(0));
v___x_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1993_);
return v___x_1994_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1985_ = stack[1].m_obj;
lean_object* v___y_1986_ = stack[2].m_obj;
lean_object* v___y_1987_ = stack[3].m_obj;
lean_object* v___y_1988_ = stack[4].m_obj;
lean_object* v___y_1989_ = stack[5].m_obj;
lean_object* v___y_1990_ = stack[6].m_obj;
lean_object* v___y_1991_ = stack[7].m_obj;
lean_object* v_res_1995_;
v_res_1995_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__0(lean_box(0), v_x_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
stack->m_obj
 = v_res_1995_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_1996_, lean_object* v_x_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__0(v_00_u03b1_1996_, v_x_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__18___redArg(lean_object* v_a_2006_, lean_object* v_b_2007_, lean_object* v_x_2008_){
_start:
{
if (lean_obj_tag(v_x_2008_) == 0)
{
lean_dec(v_b_2007_);
lean_dec_ref(v_a_2006_);
return v_x_2008_;
}
else
{
lean_object* v_key_2009_; lean_object* v_value_2010_; lean_object* v_tail_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2023_; 
v_key_2009_ = lean_ctor_get(v_x_2008_, 0);
v_value_2010_ = lean_ctor_get(v_x_2008_, 1);
v_tail_2011_ = lean_ctor_get(v_x_2008_, 2);
v_isSharedCheck_2023_ = !lean_is_exclusive(v_x_2008_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2013_ = v_x_2008_;
v_isShared_2014_ = v_isSharedCheck_2023_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_tail_2011_);
lean_inc(v_value_2010_);
lean_inc(v_key_2009_);
lean_dec(v_x_2008_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2023_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
uint8_t v___x_2015_; 
v___x_2015_ = l_Lean_ExprStructEq_beq(v_key_2009_, v_a_2006_);
if (v___x_2015_ == 0)
{
lean_object* v___x_2016_; lean_object* v___x_2018_; 
v___x_2016_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__18___redArg(v_a_2006_, v_b_2007_, v_tail_2011_);
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 2, v___x_2016_);
v___x_2018_ = v___x_2013_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_key_2009_);
lean_ctor_set(v_reuseFailAlloc_2019_, 1, v_value_2010_);
lean_ctor_set(v_reuseFailAlloc_2019_, 2, v___x_2016_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
else
{
lean_object* v___x_2021_; 
lean_dec(v_value_2010_);
lean_dec(v_key_2009_);
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 1, v_b_2007_);
lean_ctor_set(v___x_2013_, 0, v_a_2006_);
v___x_2021_ = v___x_2013_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_2006_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v_b_2007_);
lean_ctor_set(v_reuseFailAlloc_2022_, 2, v_tail_2011_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16___redArg(lean_object* v_a_2024_, lean_object* v_x_2025_){
_start:
{
if (lean_obj_tag(v_x_2025_) == 0)
{
uint8_t v___x_2026_; 
v___x_2026_ = 0;
return v___x_2026_;
}
else
{
lean_object* v_key_2027_; lean_object* v_tail_2028_; uint8_t v___x_2029_; 
v_key_2027_ = lean_ctor_get(v_x_2025_, 0);
v_tail_2028_ = lean_ctor_get(v_x_2025_, 2);
v___x_2029_ = l_Lean_ExprStructEq_beq(v_key_2027_, v_a_2024_);
if (v___x_2029_ == 0)
{
v_x_2025_ = v_tail_2028_;
goto _start;
}
else
{
return v___x_2029_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2024_ = stack[0].m_obj;
lean_object* v_x_2025_ = stack[1].m_obj;
uint8_t v_res_2031_;
v_res_2031_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2024_, v_x_2025_);
stack->m_num = v_res_2031_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16___redArg___boxed(lean_object* v_a_2032_, lean_object* v_x_2033_){
_start:
{
uint8_t v_res_2034_; lean_object* v_r_2035_; 
v_res_2034_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2032_, v_x_2033_);
lean_dec(v_x_2033_);
lean_dec_ref(v_a_2032_);
v_r_2035_ = lean_box(v_res_2034_);
return v_r_2035_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(lean_object* v_x_2036_, lean_object* v_x_2037_){
_start:
{
if (lean_obj_tag(v_x_2037_) == 0)
{
return v_x_2036_;
}
else
{
lean_object* v_key_2038_; lean_object* v_value_2039_; lean_object* v_tail_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2063_; 
v_key_2038_ = lean_ctor_get(v_x_2037_, 0);
v_value_2039_ = lean_ctor_get(v_x_2037_, 1);
v_tail_2040_ = lean_ctor_get(v_x_2037_, 2);
v_isSharedCheck_2063_ = !lean_is_exclusive(v_x_2037_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2042_ = v_x_2037_;
v_isShared_2043_ = v_isSharedCheck_2063_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_tail_2040_);
lean_inc(v_value_2039_);
lean_inc(v_key_2038_);
lean_dec(v_x_2037_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2063_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2044_; uint64_t v___x_2045_; uint64_t v___x_2046_; uint64_t v___x_2047_; uint64_t v_fold_2048_; uint64_t v___x_2049_; uint64_t v___x_2050_; uint64_t v___x_2051_; size_t v___x_2052_; size_t v___x_2053_; size_t v___x_2054_; size_t v___x_2055_; size_t v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2059_; 
v___x_2044_ = lean_array_get_size(v_x_2036_);
v___x_2045_ = l_Lean_ExprStructEq_hash(v_key_2038_);
v___x_2046_ = 32ULL;
v___x_2047_ = lean_uint64_shift_right(v___x_2045_, v___x_2046_);
v_fold_2048_ = lean_uint64_xor(v___x_2045_, v___x_2047_);
v___x_2049_ = 16ULL;
v___x_2050_ = lean_uint64_shift_right(v_fold_2048_, v___x_2049_);
v___x_2051_ = lean_uint64_xor(v_fold_2048_, v___x_2050_);
v___x_2052_ = lean_uint64_to_usize(v___x_2051_);
v___x_2053_ = lean_usize_of_nat(v___x_2044_);
v___x_2054_ = ((size_t)1ULL);
v___x_2055_ = lean_usize_sub(v___x_2053_, v___x_2054_);
v___x_2056_ = lean_usize_land(v___x_2052_, v___x_2055_);
v___x_2057_ = lean_array_uget_borrowed(v_x_2036_, v___x_2056_);
lean_inc(v___x_2057_);
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 2, v___x_2057_);
v___x_2059_ = v___x_2042_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_key_2038_);
lean_ctor_set(v_reuseFailAlloc_2062_, 1, v_value_2039_);
lean_ctor_set(v_reuseFailAlloc_2062_, 2, v___x_2057_);
v___x_2059_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
lean_object* v___x_2060_; 
v___x_2060_ = lean_array_uset(v_x_2036_, v___x_2056_, v___x_2059_);
v_x_2036_ = v___x_2060_;
v_x_2037_ = v_tail_2040_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(lean_object* v_i_2064_, lean_object* v_source_2065_, lean_object* v_target_2066_){
_start:
{
lean_object* v___x_2067_; uint8_t v___x_2068_; 
v___x_2067_ = lean_array_get_size(v_source_2065_);
v___x_2068_ = lean_nat_dec_lt(v_i_2064_, v___x_2067_);
if (v___x_2068_ == 0)
{
lean_dec_ref(v_source_2065_);
lean_dec(v_i_2064_);
return v_target_2066_;
}
else
{
lean_object* v_es_2069_; lean_object* v___x_2070_; lean_object* v_source_2071_; lean_object* v_target_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
v_es_2069_ = lean_array_fget(v_source_2065_, v_i_2064_);
v___x_2070_ = lean_box(0);
v_source_2071_ = lean_array_fset(v_source_2065_, v_i_2064_, v___x_2070_);
v_target_2072_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_target_2066_, v_es_2069_);
v___x_2073_ = lean_unsigned_to_nat(1u);
v___x_2074_ = lean_nat_add(v_i_2064_, v___x_2073_);
lean_dec(v_i_2064_);
v_i_2064_ = v___x_2074_;
v_source_2065_ = v_source_2071_;
v_target_2066_ = v_target_2072_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17___redArg(lean_object* v_data_2076_){
_start:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v_nbuckets_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2077_ = lean_array_get_size(v_data_2076_);
v___x_2078_ = lean_unsigned_to_nat(2u);
v_nbuckets_2079_ = lean_nat_mul(v___x_2077_, v___x_2078_);
v___x_2080_ = lean_unsigned_to_nat(0u);
v___x_2081_ = lean_box(0);
v___x_2082_ = lean_mk_array(v_nbuckets_2079_, v___x_2081_);
v___x_2083_ = lean_array_propagate_mark(v_data_2076_, v___x_2082_);
v___x_2084_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v___x_2080_, v_data_2076_, v___x_2083_);
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11___redArg(lean_object* v_m_2085_, lean_object* v_a_2086_, lean_object* v_b_2087_){
_start:
{
lean_object* v_size_2088_; lean_object* v_buckets_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2132_; 
v_size_2088_ = lean_ctor_get(v_m_2085_, 0);
v_buckets_2089_ = lean_ctor_get(v_m_2085_, 1);
v_isSharedCheck_2132_ = !lean_is_exclusive(v_m_2085_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2091_ = v_m_2085_;
v_isShared_2092_ = v_isSharedCheck_2132_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_buckets_2089_);
lean_inc(v_size_2088_);
lean_dec(v_m_2085_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2132_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2093_; uint64_t v___x_2094_; uint64_t v___x_2095_; uint64_t v___x_2096_; uint64_t v_fold_2097_; uint64_t v___x_2098_; uint64_t v___x_2099_; uint64_t v___x_2100_; size_t v___x_2101_; size_t v___x_2102_; size_t v___x_2103_; size_t v___x_2104_; size_t v___x_2105_; lean_object* v_bkt_2106_; uint8_t v___x_2107_; 
v___x_2093_ = lean_array_get_size(v_buckets_2089_);
v___x_2094_ = l_Lean_ExprStructEq_hash(v_a_2086_);
v___x_2095_ = 32ULL;
v___x_2096_ = lean_uint64_shift_right(v___x_2094_, v___x_2095_);
v_fold_2097_ = lean_uint64_xor(v___x_2094_, v___x_2096_);
v___x_2098_ = 16ULL;
v___x_2099_ = lean_uint64_shift_right(v_fold_2097_, v___x_2098_);
v___x_2100_ = lean_uint64_xor(v_fold_2097_, v___x_2099_);
v___x_2101_ = lean_uint64_to_usize(v___x_2100_);
v___x_2102_ = lean_usize_of_nat(v___x_2093_);
v___x_2103_ = ((size_t)1ULL);
v___x_2104_ = lean_usize_sub(v___x_2102_, v___x_2103_);
v___x_2105_ = lean_usize_land(v___x_2101_, v___x_2104_);
v_bkt_2106_ = lean_array_uget_borrowed(v_buckets_2089_, v___x_2105_);
v___x_2107_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2086_, v_bkt_2106_);
if (v___x_2107_ == 0)
{
lean_object* v___x_2108_; lean_object* v_size_x27_2109_; lean_object* v___x_2110_; lean_object* v_buckets_x27_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; uint8_t v___x_2117_; 
v___x_2108_ = lean_unsigned_to_nat(1u);
v_size_x27_2109_ = lean_nat_add(v_size_2088_, v___x_2108_);
lean_dec(v_size_2088_);
lean_inc(v_bkt_2106_);
v___x_2110_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2110_, 0, v_a_2086_);
lean_ctor_set(v___x_2110_, 1, v_b_2087_);
lean_ctor_set(v___x_2110_, 2, v_bkt_2106_);
v_buckets_x27_2111_ = lean_array_uset(v_buckets_2089_, v___x_2105_, v___x_2110_);
v___x_2112_ = lean_unsigned_to_nat(4u);
v___x_2113_ = lean_nat_mul(v_size_x27_2109_, v___x_2112_);
v___x_2114_ = lean_unsigned_to_nat(3u);
v___x_2115_ = lean_nat_div(v___x_2113_, v___x_2114_);
lean_dec(v___x_2113_);
v___x_2116_ = lean_array_get_size(v_buckets_x27_2111_);
v___x_2117_ = lean_nat_dec_le(v___x_2115_, v___x_2116_);
lean_dec(v___x_2115_);
if (v___x_2117_ == 0)
{
lean_object* v_val_2118_; lean_object* v___x_2120_; 
v_val_2118_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17___redArg(v_buckets_x27_2111_);
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 1, v_val_2118_);
lean_ctor_set(v___x_2091_, 0, v_size_x27_2109_);
v___x_2120_ = v___x_2091_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_size_x27_2109_);
lean_ctor_set(v_reuseFailAlloc_2121_, 1, v_val_2118_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
else
{
lean_object* v___x_2123_; 
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 1, v_buckets_x27_2111_);
lean_ctor_set(v___x_2091_, 0, v_size_x27_2109_);
v___x_2123_ = v___x_2091_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_size_x27_2109_);
lean_ctor_set(v_reuseFailAlloc_2124_, 1, v_buckets_x27_2111_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
}
else
{
lean_object* v___x_2125_; lean_object* v_buckets_x27_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2130_; 
lean_inc(v_bkt_2106_);
v___x_2125_ = lean_box(0);
v_buckets_x27_2126_ = lean_array_uset(v_buckets_2089_, v___x_2105_, v___x_2125_);
v___x_2127_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__18___redArg(v_a_2086_, v_b_2087_, v_bkt_2106_);
v___x_2128_ = lean_array_uset(v_buckets_x27_2126_, v___x_2105_, v___x_2127_);
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 1, v___x_2128_);
v___x_2130_ = v___x_2091_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_size_2088_);
lean_ctor_set(v_reuseFailAlloc_2131_, 1, v___x_2128_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__2(lean_object* v_a_2133_, lean_object* v_e_2134_, lean_object* v_a_2135_){
_start:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2137_ = lean_st_ref_take(v_a_2133_);
v___x_2138_ = lean_box(0);
v___x_2139_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11___redArg(v___x_2137_, v_e_2134_, v_a_2135_);
v___x_2140_ = lean_st_ref_put(v_a_2133_, v___x_2139_);
return v___x_2138_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2133_ = stack[0].m_obj;
lean_object* v_e_2134_ = stack[1].m_obj;
lean_object* v_a_2135_ = stack[2].m_obj;
lean_object* v_res_2141_;
v_res_2141_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__2(v_a_2133_, v_e_2134_, v_a_2135_);
stack->m_obj
 = v_res_2141_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__2___boxed(lean_object* v_a_2142_, lean_object* v_e_2143_, lean_object* v_a_2144_, lean_object* v___y_2145_){
_start:
{
lean_object* v_res_2146_; 
v_res_2146_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__2(v_a_2142_, v_e_2143_, v_a_2144_);
lean_dec(v_a_2142_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6___lam__0___boxed(lean_object* v_fvars_2147_, lean_object* v_pre_2148_, lean_object* v_post_2149_, lean_object* v_usedLetOnly_2150_, lean_object* v_skipConstInApp_2151_, lean_object* v_skipInstances_2152_, lean_object* v_body_2153_, lean_object* v_x_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
uint8_t v_usedLetOnly_boxed_2163_; uint8_t v_skipConstInApp_boxed_2164_; uint8_t v_skipInstances_boxed_2165_; lean_object* v_res_2166_; 
v_usedLetOnly_boxed_2163_ = lean_unbox(v_usedLetOnly_2150_);
v_skipConstInApp_boxed_2164_ = lean_unbox(v_skipConstInApp_2151_);
v_skipInstances_boxed_2165_ = lean_unbox(v_skipInstances_2152_);
v_res_2166_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6___lam__0(v_fvars_2147_, v_pre_2148_, v_post_2149_, v_usedLetOnly_boxed_2163_, v_skipConstInApp_boxed_2164_, v_skipInstances_boxed_2165_, v_body_2153_, v_x_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec(v___y_2155_);
return v_res_2166_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7___lam__0(lean_object* v_fvars_2170_, lean_object* v_pre_2171_, lean_object* v_post_2172_, uint8_t v_usedLetOnly_2173_, uint8_t v_skipConstInApp_2174_, uint8_t v_skipInstances_2175_, lean_object* v_body_2176_, lean_object* v_x_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_){
_start:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2186_ = lean_array_push(v_fvars_2170_, v_x_2177_);
v___x_2187_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7(v_pre_2171_, v_post_2172_, v_usedLetOnly_2173_, v_skipConstInApp_2174_, v_skipInstances_2175_, v___x_2186_, v_body_2176_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_);
return v___x_2187_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_2170_ = stack[0].m_obj;
lean_object* v_pre_2171_ = stack[1].m_obj;
lean_object* v_post_2172_ = stack[2].m_obj;
uint8_t v_usedLetOnly_2173_ = stack[3].m_num;
uint8_t v_skipConstInApp_2174_ = stack[4].m_num;
uint8_t v_skipInstances_2175_ = stack[5].m_num;
lean_object* v_body_2176_ = stack[6].m_obj;
lean_object* v_x_2177_ = stack[7].m_obj;
lean_object* v___y_2178_ = stack[8].m_obj;
lean_object* v___y_2179_ = stack[9].m_obj;
lean_object* v___y_2180_ = stack[10].m_obj;
lean_object* v___y_2181_ = stack[11].m_obj;
lean_object* v___y_2182_ = stack[12].m_obj;
lean_object* v___y_2183_ = stack[13].m_obj;
lean_object* v___y_2184_ = stack[14].m_obj;
lean_object* v_res_2188_;
v_res_2188_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7___lam__0(v_fvars_2170_, v_pre_2171_, v_post_2172_, v_usedLetOnly_2173_, v_skipConstInApp_2174_, v_skipInstances_2175_, v_body_2176_, v_x_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_);
stack->m_obj
 = v_res_2188_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7___lam__0___boxed(lean_object* v_fvars_2189_, lean_object* v_pre_2190_, lean_object* v_post_2191_, lean_object* v_usedLetOnly_2192_, lean_object* v_skipConstInApp_2193_, lean_object* v_skipInstances_2194_, lean_object* v_body_2195_, lean_object* v_x_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_){
_start:
{
uint8_t v_usedLetOnly_boxed_2205_; uint8_t v_skipConstInApp_boxed_2206_; uint8_t v_skipInstances_boxed_2207_; lean_object* v_res_2208_; 
v_usedLetOnly_boxed_2205_ = lean_unbox(v_usedLetOnly_2192_);
v_skipConstInApp_boxed_2206_ = lean_unbox(v_skipConstInApp_2193_);
v_skipInstances_boxed_2207_ = lean_unbox(v_skipInstances_2194_);
v_res_2208_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7___lam__0(v_fvars_2189_, v_pre_2190_, v_post_2191_, v_usedLetOnly_boxed_2205_, v_skipConstInApp_boxed_2206_, v_skipInstances_boxed_2207_, v_body_2195_, v_x_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
lean_dec(v___y_2201_);
lean_dec_ref(v___y_2200_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
lean_dec(v___y_2197_);
return v_res_2208_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(lean_object* v_pre_2209_, lean_object* v_post_2210_, uint8_t v_usedLetOnly_2211_, uint8_t v_skipConstInApp_2212_, uint8_t v_skipInstances_2213_, lean_object* v_e_2214_, lean_object* v_a_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_){
_start:
{
lean_object* v___x_2223_; 
lean_inc_ref(v_post_2210_);
lean_inc(v___y_2221_);
lean_inc_ref(v___y_2220_);
lean_inc(v___y_2219_);
lean_inc_ref(v___y_2218_);
lean_inc(v___y_2217_);
lean_inc_ref(v___y_2216_);
lean_inc_ref(v_e_2214_);
v___x_2223_ = lean_apply_8(v_post_2210_, v_e_2214_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, lean_box(0));
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_object* v_a_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2242_; 
v_a_2224_ = lean_ctor_get(v___x_2223_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2223_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2226_ = v___x_2223_;
v_isShared_2227_ = v_isSharedCheck_2242_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_dec(v___x_2223_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2242_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
switch(lean_obj_tag(v_a_2224_))
{
case 0:
{
lean_object* v_e_2228_; lean_object* v___x_2230_; 
lean_dec_ref(v_e_2214_);
lean_dec_ref(v_post_2210_);
lean_dec_ref(v_pre_2209_);
v_e_2228_ = lean_ctor_get(v_a_2224_, 0);
lean_inc_ref(v_e_2228_);
lean_dec_ref_known(v_a_2224_, 1);
if (v_isShared_2227_ == 0)
{
lean_ctor_set(v___x_2226_, 0, v_e_2228_);
v___x_2230_ = v___x_2226_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_e_2228_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
case 1:
{
lean_object* v_e_2232_; lean_object* v___x_2233_; 
lean_del_object(v___x_2226_);
lean_dec_ref(v_e_2214_);
v_e_2232_ = lean_ctor_get(v_a_2224_, 0);
lean_inc_ref(v_e_2232_);
lean_dec_ref_known(v_a_2224_, 1);
v___x_2233_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2209_, v_post_2210_, v_usedLetOnly_2211_, v_skipConstInApp_2212_, v_skipInstances_2213_, v_e_2232_, v_a_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
return v___x_2233_;
}
default: 
{
lean_object* v_e_x3f_2234_; 
lean_dec_ref(v_post_2210_);
lean_dec_ref(v_pre_2209_);
v_e_x3f_2234_ = lean_ctor_get(v_a_2224_, 0);
lean_inc(v_e_x3f_2234_);
lean_dec_ref_known(v_a_2224_, 1);
if (lean_obj_tag(v_e_x3f_2234_) == 0)
{
lean_object* v___x_2236_; 
if (v_isShared_2227_ == 0)
{
lean_ctor_set(v___x_2226_, 0, v_e_2214_);
v___x_2236_ = v___x_2226_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_e_2214_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
else
{
lean_object* v_val_2238_; lean_object* v___x_2240_; 
lean_dec_ref(v_e_2214_);
v_val_2238_ = lean_ctor_get(v_e_x3f_2234_, 0);
lean_inc(v_val_2238_);
lean_dec_ref_known(v_e_x3f_2234_, 1);
if (v_isShared_2227_ == 0)
{
lean_ctor_set(v___x_2226_, 0, v_val_2238_);
v___x_2240_ = v___x_2226_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_val_2238_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
}
}
}
else
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2250_; 
lean_dec_ref(v_e_2214_);
lean_dec_ref(v_post_2210_);
lean_dec_ref(v_pre_2209_);
v_a_2243_ = lean_ctor_get(v___x_2223_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2223_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2245_ = v___x_2223_;
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2223_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2248_; 
if (v_isShared_2246_ == 0)
{
v___x_2248_ = v___x_2245_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_a_2243_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_2209_ = stack[0].m_obj;
lean_object* v_post_2210_ = stack[1].m_obj;
uint8_t v_usedLetOnly_2211_ = stack[2].m_num;
uint8_t v_skipConstInApp_2212_ = stack[3].m_num;
uint8_t v_skipInstances_2213_ = stack[4].m_num;
lean_object* v_e_2214_ = stack[5].m_obj;
lean_object* v_a_2215_ = stack[6].m_obj;
lean_object* v___y_2216_ = stack[7].m_obj;
lean_object* v___y_2217_ = stack[8].m_obj;
lean_object* v___y_2218_ = stack[9].m_obj;
lean_object* v___y_2219_ = stack[10].m_obj;
lean_object* v___y_2220_ = stack[11].m_obj;
lean_object* v___y_2221_ = stack[12].m_obj;
lean_object* v_res_2251_;
v_res_2251_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2209_, v_post_2210_, v_usedLetOnly_2211_, v_skipConstInApp_2212_, v_skipInstances_2213_, v_e_2214_, v_a_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
stack->m_obj
 = v_res_2251_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7(lean_object* v_pre_2252_, lean_object* v_post_2253_, uint8_t v_usedLetOnly_2254_, uint8_t v_skipConstInApp_2255_, uint8_t v_skipInstances_2256_, lean_object* v_fvars_2257_, lean_object* v_e_2258_, lean_object* v_a_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
if (lean_obj_tag(v_e_2258_) == 6)
{
lean_object* v_binderName_2267_; lean_object* v_binderType_2268_; lean_object* v_body_2269_; uint8_t v_binderInfo_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___f_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v_binderName_2267_ = lean_ctor_get(v_e_2258_, 0);
lean_inc(v_binderName_2267_);
v_binderType_2268_ = lean_ctor_get(v_e_2258_, 1);
lean_inc_ref(v_binderType_2268_);
v_body_2269_ = lean_ctor_get(v_e_2258_, 2);
lean_inc_ref(v_body_2269_);
v_binderInfo_2270_ = lean_ctor_get_uint8(v_e_2258_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2258_, 3);
v___x_2271_ = lean_box(v_usedLetOnly_2254_);
v___x_2272_ = lean_box(v_skipConstInApp_2255_);
v___x_2273_ = lean_box(v_skipInstances_2256_);
lean_inc_ref(v_post_2253_);
lean_inc_ref(v_pre_2252_);
lean_inc_ref(v_fvars_2257_);
v___f_2274_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7___lam__0___boxed), 16, 7);
lean_closure_set(v___f_2274_, 0, v_fvars_2257_);
lean_closure_set(v___f_2274_, 1, v_pre_2252_);
lean_closure_set(v___f_2274_, 2, v_post_2253_);
lean_closure_set(v___f_2274_, 3, v___x_2271_);
lean_closure_set(v___f_2274_, 4, v___x_2272_);
lean_closure_set(v___f_2274_, 5, v___x_2273_);
lean_closure_set(v___f_2274_, 6, v_body_2269_);
v___x_2275_ = lean_expr_instantiate_rev(v_binderType_2268_, v_fvars_2257_);
lean_dec_ref(v_fvars_2257_);
lean_dec_ref(v_binderType_2268_);
v___x_2276_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2252_, v_post_2253_, v_usedLetOnly_2254_, v_skipConstInApp_2255_, v_skipInstances_2256_, v___x_2275_, v_a_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v_a_2277_; uint8_t v___x_2278_; lean_object* v___x_2279_; 
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_a_2277_);
lean_dec_ref_known(v___x_2276_, 1);
v___x_2278_ = 0;
v___x_2279_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_2267_, v_binderInfo_2270_, v_a_2277_, v___f_2274_, v___x_2278_, v_a_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
return v___x_2279_;
}
else
{
lean_dec_ref(v___f_2274_);
lean_dec(v_binderName_2267_);
return v___x_2276_;
}
}
else
{
lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2280_ = lean_expr_instantiate_rev(v_e_2258_, v_fvars_2257_);
lean_dec_ref(v_e_2258_);
lean_inc_ref(v_post_2253_);
lean_inc_ref(v_pre_2252_);
v___x_2281_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2252_, v_post_2253_, v_usedLetOnly_2254_, v_skipConstInApp_2255_, v_skipInstances_2256_, v___x_2280_, v_a_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v_a_2282_; uint8_t v___x_2283_; uint8_t v___x_2284_; uint8_t v___x_2285_; lean_object* v___x_2286_; 
v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_a_2282_);
lean_dec_ref_known(v___x_2281_, 1);
v___x_2283_ = 0;
v___x_2284_ = 1;
v___x_2285_ = 1;
v___x_2286_ = l_Lean_Meta_mkLambdaFVars(v_fvars_2257_, v_a_2282_, v___x_2283_, v_usedLetOnly_2254_, v___x_2283_, v___x_2284_, v___x_2285_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
lean_dec_ref(v_fvars_2257_);
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v_a_2287_; lean_object* v___x_2288_; 
v_a_2287_ = lean_ctor_get(v___x_2286_, 0);
lean_inc(v_a_2287_);
lean_dec_ref_known(v___x_2286_, 1);
v___x_2288_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2252_, v_post_2253_, v_usedLetOnly_2254_, v_skipConstInApp_2255_, v_skipInstances_2256_, v_a_2287_, v_a_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
return v___x_2288_;
}
else
{
lean_dec_ref(v_post_2253_);
lean_dec_ref(v_pre_2252_);
return v___x_2286_;
}
}
else
{
lean_dec_ref(v_fvars_2257_);
lean_dec_ref(v_post_2253_);
lean_dec_ref(v_pre_2252_);
return v___x_2281_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_2252_ = stack[0].m_obj;
lean_object* v_post_2253_ = stack[1].m_obj;
uint8_t v_usedLetOnly_2254_ = stack[2].m_num;
uint8_t v_skipConstInApp_2255_ = stack[3].m_num;
uint8_t v_skipInstances_2256_ = stack[4].m_num;
lean_object* v_fvars_2257_ = stack[5].m_obj;
lean_object* v_e_2258_ = stack[6].m_obj;
lean_object* v_a_2259_ = stack[7].m_obj;
lean_object* v___y_2260_ = stack[8].m_obj;
lean_object* v___y_2261_ = stack[9].m_obj;
lean_object* v___y_2262_ = stack[10].m_obj;
lean_object* v___y_2263_ = stack[11].m_obj;
lean_object* v___y_2264_ = stack[12].m_obj;
lean_object* v___y_2265_ = stack[13].m_obj;
lean_object* v_res_2289_;
v_res_2289_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7(v_pre_2252_, v_post_2253_, v_usedLetOnly_2254_, v_skipConstInApp_2255_, v_skipInstances_2256_, v_fvars_2257_, v_e_2258_, v_a_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
stack->m_obj
 = v_res_2289_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8___lam__0(lean_object* v_fvars_2290_, lean_object* v_pre_2291_, lean_object* v_post_2292_, uint8_t v_usedLetOnly_2293_, uint8_t v_skipConstInApp_2294_, uint8_t v_skipInstances_2295_, lean_object* v_body_2296_, lean_object* v_x_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2306_ = lean_array_push(v_fvars_2290_, v_x_2297_);
v___x_2307_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8(v_pre_2291_, v_post_2292_, v_usedLetOnly_2293_, v_skipConstInApp_2294_, v_skipInstances_2295_, v___x_2306_, v_body_2296_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
return v___x_2307_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_2290_ = stack[0].m_obj;
lean_object* v_pre_2291_ = stack[1].m_obj;
lean_object* v_post_2292_ = stack[2].m_obj;
uint8_t v_usedLetOnly_2293_ = stack[3].m_num;
uint8_t v_skipConstInApp_2294_ = stack[4].m_num;
uint8_t v_skipInstances_2295_ = stack[5].m_num;
lean_object* v_body_2296_ = stack[6].m_obj;
lean_object* v_x_2297_ = stack[7].m_obj;
lean_object* v___y_2298_ = stack[8].m_obj;
lean_object* v___y_2299_ = stack[9].m_obj;
lean_object* v___y_2300_ = stack[10].m_obj;
lean_object* v___y_2301_ = stack[11].m_obj;
lean_object* v___y_2302_ = stack[12].m_obj;
lean_object* v___y_2303_ = stack[13].m_obj;
lean_object* v___y_2304_ = stack[14].m_obj;
lean_object* v_res_2308_;
v_res_2308_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8___lam__0(v_fvars_2290_, v_pre_2291_, v_post_2292_, v_usedLetOnly_2293_, v_skipConstInApp_2294_, v_skipInstances_2295_, v_body_2296_, v_x_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
stack->m_obj
 = v_res_2308_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8___lam__0___boxed(lean_object* v_fvars_2309_, lean_object* v_pre_2310_, lean_object* v_post_2311_, lean_object* v_usedLetOnly_2312_, lean_object* v_skipConstInApp_2313_, lean_object* v_skipInstances_2314_, lean_object* v_body_2315_, lean_object* v_x_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_){
_start:
{
uint8_t v_usedLetOnly_boxed_2325_; uint8_t v_skipConstInApp_boxed_2326_; uint8_t v_skipInstances_boxed_2327_; lean_object* v_res_2328_; 
v_usedLetOnly_boxed_2325_ = lean_unbox(v_usedLetOnly_2312_);
v_skipConstInApp_boxed_2326_ = lean_unbox(v_skipConstInApp_2313_);
v_skipInstances_boxed_2327_ = lean_unbox(v_skipInstances_2314_);
v_res_2328_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8___lam__0(v_fvars_2309_, v_pre_2310_, v_post_2311_, v_usedLetOnly_boxed_2325_, v_skipConstInApp_boxed_2326_, v_skipInstances_boxed_2327_, v_body_2315_, v_x_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2317_);
return v_res_2328_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8(lean_object* v_pre_2329_, lean_object* v_post_2330_, uint8_t v_usedLetOnly_2331_, uint8_t v_skipConstInApp_2332_, uint8_t v_skipInstances_2333_, lean_object* v_fvars_2334_, lean_object* v_e_2335_, lean_object* v_a_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_){
_start:
{
if (lean_obj_tag(v_e_2335_) == 8)
{
lean_object* v_declName_2344_; lean_object* v_type_2345_; lean_object* v_value_2346_; lean_object* v_body_2347_; uint8_t v_nondep_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___f_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; 
v_declName_2344_ = lean_ctor_get(v_e_2335_, 0);
lean_inc(v_declName_2344_);
v_type_2345_ = lean_ctor_get(v_e_2335_, 1);
lean_inc_ref(v_type_2345_);
v_value_2346_ = lean_ctor_get(v_e_2335_, 2);
lean_inc_ref(v_value_2346_);
v_body_2347_ = lean_ctor_get(v_e_2335_, 3);
lean_inc_ref(v_body_2347_);
v_nondep_2348_ = lean_ctor_get_uint8(v_e_2335_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2335_, 4);
v___x_2349_ = lean_box(v_usedLetOnly_2331_);
v___x_2350_ = lean_box(v_skipConstInApp_2332_);
v___x_2351_ = lean_box(v_skipInstances_2333_);
lean_inc_ref_n(v_post_2330_, 2);
lean_inc_ref_n(v_pre_2329_, 2);
lean_inc_ref(v_fvars_2334_);
v___f_2352_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8___lam__0___boxed), 16, 7);
lean_closure_set(v___f_2352_, 0, v_fvars_2334_);
lean_closure_set(v___f_2352_, 1, v_pre_2329_);
lean_closure_set(v___f_2352_, 2, v_post_2330_);
lean_closure_set(v___f_2352_, 3, v___x_2349_);
lean_closure_set(v___f_2352_, 4, v___x_2350_);
lean_closure_set(v___f_2352_, 5, v___x_2351_);
lean_closure_set(v___f_2352_, 6, v_body_2347_);
v___x_2353_ = lean_expr_instantiate_rev(v_type_2345_, v_fvars_2334_);
lean_dec_ref(v_type_2345_);
v___x_2354_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2329_, v_post_2330_, v_usedLetOnly_2331_, v_skipConstInApp_2332_, v_skipInstances_2333_, v___x_2353_, v_a_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
if (lean_obj_tag(v___x_2354_) == 0)
{
lean_object* v_a_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v_a_2355_ = lean_ctor_get(v___x_2354_, 0);
lean_inc(v_a_2355_);
lean_dec_ref_known(v___x_2354_, 1);
v___x_2356_ = lean_expr_instantiate_rev(v_value_2346_, v_fvars_2334_);
lean_dec_ref(v_fvars_2334_);
lean_dec_ref(v_value_2346_);
v___x_2357_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2329_, v_post_2330_, v_usedLetOnly_2331_, v_skipConstInApp_2332_, v_skipInstances_2333_, v___x_2356_, v_a_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
if (lean_obj_tag(v___x_2357_) == 0)
{
lean_object* v_a_2358_; uint8_t v___x_2359_; lean_object* v___x_2360_; 
v_a_2358_ = lean_ctor_get(v___x_2357_, 0);
lean_inc(v_a_2358_);
lean_dec_ref_known(v___x_2357_, 1);
v___x_2359_ = 0;
v___x_2360_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11___redArg(v_declName_2344_, v_a_2355_, v_a_2358_, v___f_2352_, v_nondep_2348_, v___x_2359_, v_a_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
return v___x_2360_;
}
else
{
lean_dec(v_a_2355_);
lean_dec_ref(v___f_2352_);
lean_dec(v_declName_2344_);
return v___x_2357_;
}
}
else
{
lean_dec_ref(v___f_2352_);
lean_dec_ref(v_value_2346_);
lean_dec(v_declName_2344_);
lean_dec_ref(v_fvars_2334_);
lean_dec_ref(v_post_2330_);
lean_dec_ref(v_pre_2329_);
return v___x_2354_;
}
}
else
{
lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2361_ = lean_expr_instantiate_rev(v_e_2335_, v_fvars_2334_);
lean_dec_ref(v_e_2335_);
lean_inc_ref(v_post_2330_);
lean_inc_ref(v_pre_2329_);
v___x_2362_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2329_, v_post_2330_, v_usedLetOnly_2331_, v_skipConstInApp_2332_, v_skipInstances_2333_, v___x_2361_, v_a_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v_a_2363_; uint8_t v___x_2364_; uint8_t v___x_2365_; lean_object* v___x_2366_; 
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
lean_inc(v_a_2363_);
lean_dec_ref_known(v___x_2362_, 1);
v___x_2364_ = 0;
v___x_2365_ = 1;
v___x_2366_ = l_Lean_Meta_mkLetFVars(v_fvars_2334_, v_a_2363_, v_usedLetOnly_2331_, v___x_2364_, v___x_2365_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
lean_dec_ref(v_fvars_2334_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; lean_object* v___x_2368_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_a_2367_);
lean_dec_ref_known(v___x_2366_, 1);
v___x_2368_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2329_, v_post_2330_, v_usedLetOnly_2331_, v_skipConstInApp_2332_, v_skipInstances_2333_, v_a_2367_, v_a_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
return v___x_2368_;
}
else
{
lean_dec_ref(v_post_2330_);
lean_dec_ref(v_pre_2329_);
return v___x_2366_;
}
}
else
{
lean_dec_ref(v_fvars_2334_);
lean_dec_ref(v_post_2330_);
lean_dec_ref(v_pre_2329_);
return v___x_2362_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_2329_ = stack[0].m_obj;
lean_object* v_post_2330_ = stack[1].m_obj;
uint8_t v_usedLetOnly_2331_ = stack[2].m_num;
uint8_t v_skipConstInApp_2332_ = stack[3].m_num;
uint8_t v_skipInstances_2333_ = stack[4].m_num;
lean_object* v_fvars_2334_ = stack[5].m_obj;
lean_object* v_e_2335_ = stack[6].m_obj;
lean_object* v_a_2336_ = stack[7].m_obj;
lean_object* v___y_2337_ = stack[8].m_obj;
lean_object* v___y_2338_ = stack[9].m_obj;
lean_object* v___y_2339_ = stack[10].m_obj;
lean_object* v___y_2340_ = stack[11].m_obj;
lean_object* v___y_2341_ = stack[12].m_obj;
lean_object* v___y_2342_ = stack[13].m_obj;
lean_object* v_res_2369_;
v_res_2369_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8(v_pre_2329_, v_post_2330_, v_usedLetOnly_2331_, v_skipConstInApp_2332_, v_skipInstances_2333_, v_fvars_2334_, v_e_2335_, v_a_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
stack->m_obj
 = v_res_2369_;
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2370_; lean_object* v_dummy_2371_; 
v___x_2370_ = lean_box(0);
v_dummy_2371_ = l_Lean_Expr_sort___override(v___x_2370_);
return v_dummy_2371_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__2(lean_object* v_pre_2372_, lean_object* v_post_2373_, uint8_t v_usedLetOnly_2374_, uint8_t v_skipConstInApp_2375_, uint8_t v_skipInstances_2376_, size_t v_sz_2377_, size_t v_i_2378_, lean_object* v_bs_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
uint8_t v___x_2388_; 
v___x_2388_ = lean_usize_dec_lt(v_i_2378_, v_sz_2377_);
if (v___x_2388_ == 0)
{
lean_object* v___x_2389_; 
lean_dec_ref(v_post_2373_);
lean_dec_ref(v_pre_2372_);
v___x_2389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2389_, 0, v_bs_2379_);
return v___x_2389_;
}
else
{
lean_object* v_v_2390_; lean_object* v___x_2391_; lean_object* v_bs_x27_2392_; lean_object* v___x_2393_; 
v_v_2390_ = lean_array_uget(v_bs_2379_, v_i_2378_);
v___x_2391_ = lean_unsigned_to_nat(0u);
v_bs_x27_2392_ = lean_array_uset(v_bs_2379_, v_i_2378_, v___x_2391_);
lean_inc_ref(v_post_2373_);
lean_inc_ref(v_pre_2372_);
v___x_2393_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2372_, v_post_2373_, v_usedLetOnly_2374_, v_skipConstInApp_2375_, v_skipInstances_2376_, v_v_2390_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v_a_2394_; size_t v___x_2395_; size_t v___x_2396_; lean_object* v___x_2397_; 
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_a_2394_);
lean_dec_ref_known(v___x_2393_, 1);
v___x_2395_ = ((size_t)1ULL);
v___x_2396_ = lean_usize_add(v_i_2378_, v___x_2395_);
v___x_2397_ = lean_array_uset(v_bs_x27_2392_, v_i_2378_, v_a_2394_);
v_i_2378_ = v___x_2396_;
v_bs_2379_ = v___x_2397_;
goto _start;
}
else
{
lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2406_; 
lean_dec_ref(v_bs_x27_2392_);
lean_dec_ref(v_post_2373_);
lean_dec_ref(v_pre_2372_);
v_a_2399_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2401_ = v___x_2393_;
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v___x_2393_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2404_; 
if (v_isShared_2402_ == 0)
{
v___x_2404_ = v___x_2401_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_a_2399_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_2372_ = stack[0].m_obj;
lean_object* v_post_2373_ = stack[1].m_obj;
uint8_t v_usedLetOnly_2374_ = stack[2].m_num;
uint8_t v_skipConstInApp_2375_ = stack[3].m_num;
uint8_t v_skipInstances_2376_ = stack[4].m_num;
size_t v_sz_2377_ = stack[5].m_num;
size_t v_i_2378_ = stack[6].m_num;
lean_object* v_bs_2379_ = stack[7].m_obj;
lean_object* v___y_2380_ = stack[8].m_obj;
lean_object* v___y_2381_ = stack[9].m_obj;
lean_object* v___y_2382_ = stack[10].m_obj;
lean_object* v___y_2383_ = stack[11].m_obj;
lean_object* v___y_2384_ = stack[12].m_obj;
lean_object* v___y_2385_ = stack[13].m_obj;
lean_object* v___y_2386_ = stack[14].m_obj;
lean_object* v_res_2407_;
v_res_2407_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__2(v_pre_2372_, v_post_2373_, v_usedLetOnly_2374_, v_skipConstInApp_2375_, v_skipInstances_2376_, v_sz_2377_, v_i_2378_, v_bs_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
stack->m_obj
 = v_res_2407_;
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__0(lean_object* v_pre_2408_, lean_object* v_post_2409_, uint8_t v_usedLetOnly_2410_, uint8_t v_skipConstInApp_2411_, uint8_t v_skipInstances_2412_, lean_object* v___x_2413_, lean_object* v___y_2414_, lean_object* v_b_2415_, lean_object* v_a_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
lean_object* v___x_2424_; 
v___x_2424_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2408_, v_post_2409_, v_usedLetOnly_2410_, v_skipConstInApp_2411_, v_skipInstances_2412_, v___x_2413_, v___y_2414_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2434_; 
v_a_2425_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2427_ = v___x_2424_;
v_isShared_2428_ = v_isSharedCheck_2434_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2424_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2434_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2432_; 
v___x_2429_ = lean_array_fset(v_b_2415_, v_a_2416_, v_a_2425_);
v___x_2430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2429_);
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 0, v___x_2430_);
v___x_2432_ = v___x_2427_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v___x_2430_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
else
{
lean_object* v_a_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2442_; 
lean_dec_ref(v_b_2415_);
v_a_2435_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2437_ = v___x_2424_;
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v___x_2424_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2440_; 
if (v_isShared_2438_ == 0)
{
v___x_2440_ = v___x_2437_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_a_2435_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_2408_ = stack[0].m_obj;
lean_object* v_post_2409_ = stack[1].m_obj;
uint8_t v_usedLetOnly_2410_ = stack[2].m_num;
uint8_t v_skipConstInApp_2411_ = stack[3].m_num;
uint8_t v_skipInstances_2412_ = stack[4].m_num;
lean_object* v___x_2413_ = stack[5].m_obj;
lean_object* v___y_2414_ = stack[6].m_obj;
lean_object* v_b_2415_ = stack[7].m_obj;
lean_object* v_a_2416_ = stack[8].m_obj;
lean_object* v___y_2417_ = stack[9].m_obj;
lean_object* v___y_2418_ = stack[10].m_obj;
lean_object* v___y_2419_ = stack[11].m_obj;
lean_object* v___y_2420_ = stack[12].m_obj;
lean_object* v___y_2421_ = stack[13].m_obj;
lean_object* v___y_2422_ = stack[14].m_obj;
lean_object* v_res_2443_;
v_res_2443_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__0(v_pre_2408_, v_post_2409_, v_usedLetOnly_2410_, v_skipConstInApp_2411_, v_skipInstances_2412_, v___x_2413_, v___y_2414_, v_b_2415_, v_a_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
stack->m_obj
 = v_res_2443_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__0___boxed(lean_object* v_pre_2444_, lean_object* v_post_2445_, lean_object* v_usedLetOnly_2446_, lean_object* v_skipConstInApp_2447_, lean_object* v_skipInstances_2448_, lean_object* v___x_2449_, lean_object* v___y_2450_, lean_object* v_b_2451_, lean_object* v_a_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_){
_start:
{
uint8_t v_usedLetOnly_boxed_2460_; uint8_t v_skipConstInApp_boxed_2461_; uint8_t v_skipInstances_boxed_2462_; lean_object* v_res_2463_; 
v_usedLetOnly_boxed_2460_ = lean_unbox(v_usedLetOnly_2446_);
v_skipConstInApp_boxed_2461_ = lean_unbox(v_skipConstInApp_2447_);
v_skipInstances_boxed_2462_ = lean_unbox(v_skipInstances_2448_);
v_res_2463_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__0(v_pre_2444_, v_post_2445_, v_usedLetOnly_boxed_2460_, v_skipConstInApp_boxed_2461_, v_skipInstances_boxed_2462_, v___x_2449_, v___y_2450_, v_b_2451_, v_a_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
lean_dec(v___y_2456_);
lean_dec_ref(v___y_2455_);
lean_dec(v___y_2454_);
lean_dec_ref(v___y_2453_);
lean_dec(v_a_2452_);
lean_dec(v___y_2450_);
return v_res_2463_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg(lean_object* v_upperBound_2464_, lean_object* v___x_2465_, lean_object* v_pre_2466_, lean_object* v_post_2467_, uint8_t v_usedLetOnly_2468_, uint8_t v_skipConstInApp_2469_, uint8_t v_skipInstances_2470_, lean_object* v_a_2471_, lean_object* v_b_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v___y_2482_; uint8_t v___x_2505_; 
v___x_2505_ = lean_nat_dec_lt(v_a_2471_, v_upperBound_2464_);
if (v___x_2505_ == 0)
{
lean_object* v___x_2506_; 
lean_dec(v_a_2471_);
lean_dec_ref(v_post_2467_);
lean_dec_ref(v_pre_2466_);
v___x_2506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2506_, 0, v_b_2472_);
return v___x_2506_;
}
else
{
lean_object* v___x_2507_; lean_object* v___x_2508_; uint8_t v___x_2509_; 
v___x_2507_ = lean_array_fget_borrowed(v_b_2472_, v_a_2471_);
v___x_2508_ = lean_array_get_size(v___x_2465_);
v___x_2509_ = lean_nat_dec_lt(v_a_2471_, v___x_2508_);
if (v___x_2509_ == 0)
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___f_2513_; 
lean_inc(v___x_2507_);
v___x_2510_ = lean_box(v_usedLetOnly_2468_);
v___x_2511_ = lean_box(v_skipConstInApp_2469_);
v___x_2512_ = lean_box(v_skipInstances_2470_);
lean_inc(v_a_2471_);
lean_inc(v___y_2473_);
lean_inc_ref(v_post_2467_);
lean_inc_ref(v_pre_2466_);
v___f_2513_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 16, 9);
lean_closure_set(v___f_2513_, 0, v_pre_2466_);
lean_closure_set(v___f_2513_, 1, v_post_2467_);
lean_closure_set(v___f_2513_, 2, v___x_2510_);
lean_closure_set(v___f_2513_, 3, v___x_2511_);
lean_closure_set(v___f_2513_, 4, v___x_2512_);
lean_closure_set(v___f_2513_, 5, v___x_2507_);
lean_closure_set(v___f_2513_, 6, v___y_2473_);
lean_closure_set(v___f_2513_, 7, v_b_2472_);
lean_closure_set(v___f_2513_, 8, v_a_2471_);
v___y_2482_ = v___f_2513_;
goto v___jp_2481_;
}
else
{
lean_object* v___x_2514_; uint8_t v_isInstance_2515_; 
v___x_2514_ = lean_array_fget_borrowed(v___x_2465_, v_a_2471_);
v_isInstance_2515_ = lean_ctor_get_uint8(v___x_2514_, sizeof(void*)*1 + 4);
if (v_isInstance_2515_ == 0)
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___f_2519_; 
lean_inc(v___x_2507_);
v___x_2516_ = lean_box(v_usedLetOnly_2468_);
v___x_2517_ = lean_box(v_skipConstInApp_2469_);
v___x_2518_ = lean_box(v_skipInstances_2470_);
lean_inc(v_a_2471_);
lean_inc(v___y_2473_);
lean_inc_ref(v_post_2467_);
lean_inc_ref(v_pre_2466_);
v___f_2519_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 16, 9);
lean_closure_set(v___f_2519_, 0, v_pre_2466_);
lean_closure_set(v___f_2519_, 1, v_post_2467_);
lean_closure_set(v___f_2519_, 2, v___x_2516_);
lean_closure_set(v___f_2519_, 3, v___x_2517_);
lean_closure_set(v___f_2519_, 4, v___x_2518_);
lean_closure_set(v___f_2519_, 5, v___x_2507_);
lean_closure_set(v___f_2519_, 6, v___y_2473_);
lean_closure_set(v___f_2519_, 7, v_b_2472_);
lean_closure_set(v___f_2519_, 8, v_a_2471_);
v___y_2482_ = v___f_2519_;
goto v___jp_2481_;
}
else
{
lean_object* v___x_2520_; lean_object* v___f_2521_; 
v___x_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2520_, 0, v_b_2472_);
v___f_2521_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___lam__2___boxed), 8, 1);
lean_closure_set(v___f_2521_, 0, v___x_2520_);
v___y_2482_ = v___f_2521_;
goto v___jp_2481_;
}
}
}
v___jp_2481_:
{
lean_object* v___x_2483_; 
lean_inc(v___y_2479_);
lean_inc_ref(v___y_2478_);
lean_inc(v___y_2477_);
lean_inc_ref(v___y_2476_);
lean_inc(v___y_2475_);
lean_inc_ref(v___y_2474_);
v___x_2483_ = lean_apply_7(v___y_2482_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, lean_box(0));
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2496_; 
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2486_ = v___x_2483_;
v_isShared_2487_ = v_isSharedCheck_2496_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2483_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2496_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
if (lean_obj_tag(v_a_2484_) == 0)
{
lean_object* v_a_2488_; lean_object* v___x_2490_; 
lean_dec(v_a_2471_);
lean_dec_ref(v_post_2467_);
lean_dec_ref(v_pre_2466_);
v_a_2488_ = lean_ctor_get(v_a_2484_, 0);
lean_inc(v_a_2488_);
lean_dec_ref_known(v_a_2484_, 1);
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 0, v_a_2488_);
v___x_2490_ = v___x_2486_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_a_2488_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
else
{
lean_object* v_a_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; 
lean_del_object(v___x_2486_);
v_a_2492_ = lean_ctor_get(v_a_2484_, 0);
lean_inc(v_a_2492_);
lean_dec_ref_known(v_a_2484_, 1);
v___x_2493_ = lean_unsigned_to_nat(1u);
v___x_2494_ = lean_nat_add(v_a_2471_, v___x_2493_);
lean_dec(v_a_2471_);
v_a_2471_ = v___x_2494_;
v_b_2472_ = v_a_2492_;
goto _start;
}
}
}
else
{
lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2504_; 
lean_dec(v_a_2471_);
lean_dec_ref(v_post_2467_);
lean_dec_ref(v_pre_2466_);
v_a_2497_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2499_ = v___x_2483_;
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v___x_2483_);
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
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2464_ = stack[0].m_obj;
lean_object* v___x_2465_ = stack[1].m_obj;
lean_object* v_pre_2466_ = stack[2].m_obj;
lean_object* v_post_2467_ = stack[3].m_obj;
uint8_t v_usedLetOnly_2468_ = stack[4].m_num;
uint8_t v_skipConstInApp_2469_ = stack[5].m_num;
uint8_t v_skipInstances_2470_ = stack[6].m_num;
lean_object* v_a_2471_ = stack[7].m_obj;
lean_object* v_b_2472_ = stack[8].m_obj;
lean_object* v___y_2473_ = stack[9].m_obj;
lean_object* v___y_2474_ = stack[10].m_obj;
lean_object* v___y_2475_ = stack[11].m_obj;
lean_object* v___y_2476_ = stack[12].m_obj;
lean_object* v___y_2477_ = stack[13].m_obj;
lean_object* v___y_2478_ = stack[14].m_obj;
lean_object* v___y_2479_ = stack[15].m_obj;
lean_object* v_res_2522_;
v_res_2522_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg(v_upperBound_2464_, v___x_2465_, v_pre_2466_, v_post_2467_, v_usedLetOnly_2468_, v_skipConstInApp_2469_, v_skipInstances_2470_, v_a_2471_, v_b_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
stack->m_obj
 = v_res_2522_;
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__9(uint8_t v_skipInstances_2523_, lean_object* v_pre_2524_, lean_object* v_post_2525_, uint8_t v_usedLetOnly_2526_, uint8_t v_skipConstInApp_2527_, lean_object* v_x_2528_, lean_object* v_x_2529_, lean_object* v_x_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_){
_start:
{
lean_object* v_f_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; 
if (lean_obj_tag(v_x_2528_) == 5)
{
lean_object* v_fn_2590_; lean_object* v_arg_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
v_fn_2590_ = lean_ctor_get(v_x_2528_, 0);
lean_inc_ref(v_fn_2590_);
v_arg_2591_ = lean_ctor_get(v_x_2528_, 1);
lean_inc_ref(v_arg_2591_);
lean_dec_ref_known(v_x_2528_, 2);
v___x_2592_ = lean_array_set(v_x_2529_, v_x_2530_, v_arg_2591_);
v___x_2593_ = lean_unsigned_to_nat(1u);
v___x_2594_ = lean_nat_sub(v_x_2530_, v___x_2593_);
lean_dec(v_x_2530_);
v_x_2528_ = v_fn_2590_;
v_x_2529_ = v___x_2592_;
v_x_2530_ = v___x_2594_;
goto _start;
}
else
{
lean_dec(v_x_2530_);
if (v_skipConstInApp_2527_ == 0)
{
goto v___jp_2587_;
}
else
{
uint8_t v___x_2596_; 
v___x_2596_ = l_Lean_Expr_isConst(v_x_2528_);
if (v___x_2596_ == 0)
{
goto v___jp_2587_;
}
else
{
v_f_2540_ = v_x_2528_;
v___y_2541_ = v___y_2531_;
v___y_2542_ = v___y_2532_;
v___y_2543_ = v___y_2533_;
v___y_2544_ = v___y_2534_;
v___y_2545_ = v___y_2535_;
v___y_2546_ = v___y_2536_;
v___y_2547_ = v___y_2537_;
goto v___jp_2539_;
}
}
}
v___jp_2539_:
{
if (v_skipInstances_2523_ == 0)
{
size_t v_sz_2548_; size_t v___x_2549_; lean_object* v___x_2550_; 
v_sz_2548_ = lean_array_size(v_x_2529_);
v___x_2549_ = ((size_t)0ULL);
lean_inc_ref(v_post_2525_);
lean_inc_ref(v_pre_2524_);
v___x_2550_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__2(v_pre_2524_, v_post_2525_, v_usedLetOnly_2526_, v_skipConstInApp_2527_, v_skipInstances_2523_, v_sz_2548_, v___x_2549_, v_x_2529_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_);
if (lean_obj_tag(v___x_2550_) == 0)
{
lean_object* v_a_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; 
v_a_2551_ = lean_ctor_get(v___x_2550_, 0);
lean_inc(v_a_2551_);
lean_dec_ref_known(v___x_2550_, 1);
v___x_2552_ = l_Lean_mkAppN(v_f_2540_, v_a_2551_);
lean_dec(v_a_2551_);
v___x_2553_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2524_, v_post_2525_, v_usedLetOnly_2526_, v_skipConstInApp_2527_, v_skipInstances_2523_, v___x_2552_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_);
return v___x_2553_;
}
else
{
lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2561_; 
lean_dec_ref(v_f_2540_);
lean_dec_ref(v_post_2525_);
lean_dec_ref(v_pre_2524_);
v_a_2554_ = lean_ctor_get(v___x_2550_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2550_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2556_ = v___x_2550_;
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v___x_2550_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2559_; 
if (v_isShared_2557_ == 0)
{
v___x_2559_ = v___x_2556_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_a_2554_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
}
else
{
lean_object* v___x_2562_; lean_object* v___x_2563_; 
v___x_2562_ = lean_array_get_size(v_x_2529_);
lean_inc_ref(v_f_2540_);
v___x_2563_ = l_Lean_Meta_getFunInfoNArgs(v_f_2540_, v___x_2562_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v_a_2564_; lean_object* v_paramInfo_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
lean_inc(v_a_2564_);
lean_dec_ref_known(v___x_2563_, 1);
v_paramInfo_2565_ = lean_ctor_get(v_a_2564_, 0);
lean_inc_ref(v_paramInfo_2565_);
lean_dec(v_a_2564_);
v___x_2566_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_2525_);
lean_inc_ref(v_pre_2524_);
v___x_2567_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg(v___x_2562_, v_paramInfo_2565_, v_pre_2524_, v_post_2525_, v_usedLetOnly_2526_, v_skipConstInApp_2527_, v_skipInstances_2523_, v___x_2566_, v_x_2529_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_);
lean_dec_ref(v_paramInfo_2565_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v_a_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
v_a_2568_ = lean_ctor_get(v___x_2567_, 0);
lean_inc(v_a_2568_);
lean_dec_ref_known(v___x_2567_, 1);
v___x_2569_ = l_Lean_mkAppN(v_f_2540_, v_a_2568_);
lean_dec(v_a_2568_);
v___x_2570_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2524_, v_post_2525_, v_usedLetOnly_2526_, v_skipConstInApp_2527_, v_skipInstances_2523_, v___x_2569_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_);
return v___x_2570_;
}
else
{
lean_object* v_a_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2578_; 
lean_dec_ref(v_f_2540_);
lean_dec_ref(v_post_2525_);
lean_dec_ref(v_pre_2524_);
v_a_2571_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2578_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2573_ = v___x_2567_;
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_a_2571_);
lean_dec(v___x_2567_);
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
else
{
lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2586_; 
lean_dec_ref(v_f_2540_);
lean_dec_ref(v_x_2529_);
lean_dec_ref(v_post_2525_);
lean_dec_ref(v_pre_2524_);
v_a_2579_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2581_ = v___x_2563_;
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___x_2563_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2584_; 
if (v_isShared_2582_ == 0)
{
v___x_2584_ = v___x_2581_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_a_2579_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
}
}
v___jp_2587_:
{
lean_object* v___x_2588_; 
lean_inc_ref(v_post_2525_);
lean_inc_ref(v_pre_2524_);
v___x_2588_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2524_, v_post_2525_, v_usedLetOnly_2526_, v_skipConstInApp_2527_, v_skipInstances_2523_, v_x_2528_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_a_2589_);
lean_dec_ref_known(v___x_2588_, 1);
v_f_2540_ = v_a_2589_;
v___y_2541_ = v___y_2531_;
v___y_2542_ = v___y_2532_;
v___y_2543_ = v___y_2533_;
v___y_2544_ = v___y_2534_;
v___y_2545_ = v___y_2535_;
v___y_2546_ = v___y_2536_;
v___y_2547_ = v___y_2537_;
goto v___jp_2539_;
}
else
{
lean_dec_ref(v_x_2529_);
lean_dec_ref(v_post_2525_);
lean_dec_ref(v_pre_2524_);
return v___x_2588_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__9_0interp(lean_interpreter_value* stack)
{
uint8_t v_skipInstances_2523_ = stack[0].m_num;
lean_object* v_pre_2524_ = stack[1].m_obj;
lean_object* v_post_2525_ = stack[2].m_obj;
uint8_t v_usedLetOnly_2526_ = stack[3].m_num;
uint8_t v_skipConstInApp_2527_ = stack[4].m_num;
lean_object* v_x_2528_ = stack[5].m_obj;
lean_object* v_x_2529_ = stack[6].m_obj;
lean_object* v_x_2530_ = stack[7].m_obj;
lean_object* v___y_2531_ = stack[8].m_obj;
lean_object* v___y_2532_ = stack[9].m_obj;
lean_object* v___y_2533_ = stack[10].m_obj;
lean_object* v___y_2534_ = stack[11].m_obj;
lean_object* v___y_2535_ = stack[12].m_obj;
lean_object* v___y_2536_ = stack[13].m_obj;
lean_object* v___y_2537_ = stack[14].m_obj;
lean_object* v_res_2597_;
v_res_2597_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__9(v_skipInstances_2523_, v_pre_2524_, v_post_2525_, v_usedLetOnly_2526_, v_skipConstInApp_2527_, v_x_2528_, v_x_2529_, v_x_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
stack->m_obj
 = v_res_2597_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1(lean_object* v___x_2598_, lean_object* v_pre_2599_, lean_object* v_e_2600_, lean_object* v_post_2601_, uint8_t v_usedLetOnly_2602_, uint8_t v_skipConstInApp_2603_, uint8_t v_skipInstances_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_){
_start:
{
lean_object* v___x_2613_; 
v___x_2613_ = l_Lean_Core_checkSystem(v___x_2598_, v___y_2610_, v___y_2611_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v___x_2614_; 
lean_dec_ref_known(v___x_2613_, 1);
lean_inc_ref(v_pre_2599_);
lean_inc(v___y_2611_);
lean_inc_ref(v___y_2610_);
lean_inc(v___y_2609_);
lean_inc_ref(v___y_2608_);
lean_inc(v___y_2607_);
lean_inc_ref(v___y_2606_);
lean_inc_ref(v_e_2600_);
v___x_2614_ = lean_apply_8(v_pre_2599_, v_e_2600_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, lean_box(0));
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2663_; 
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2617_ = v___x_2614_;
v_isShared_2618_ = v_isSharedCheck_2663_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2614_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2663_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___y_2620_; 
switch(lean_obj_tag(v_a_2615_))
{
case 0:
{
lean_object* v_e_2655_; lean_object* v___x_2657_; 
lean_dec_ref(v_post_2601_);
lean_dec_ref(v_e_2600_);
lean_dec_ref(v_pre_2599_);
v_e_2655_ = lean_ctor_get(v_a_2615_, 0);
lean_inc_ref(v_e_2655_);
lean_dec_ref_known(v_a_2615_, 1);
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 0, v_e_2655_);
v___x_2657_ = v___x_2617_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_e_2655_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
case 1:
{
lean_object* v_e_2659_; lean_object* v___x_2660_; 
lean_del_object(v___x_2617_);
lean_dec_ref(v_e_2600_);
v_e_2659_ = lean_ctor_get(v_a_2615_, 0);
lean_inc_ref(v_e_2659_);
lean_dec_ref_known(v_a_2615_, 1);
v___x_2660_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2599_, v_post_2601_, v_usedLetOnly_2602_, v_skipConstInApp_2603_, v_skipInstances_2604_, v_e_2659_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
return v___x_2660_;
}
default: 
{
lean_object* v_e_x3f_2661_; 
lean_del_object(v___x_2617_);
v_e_x3f_2661_ = lean_ctor_get(v_a_2615_, 0);
lean_inc(v_e_x3f_2661_);
lean_dec_ref_known(v_a_2615_, 1);
if (lean_obj_tag(v_e_x3f_2661_) == 0)
{
v___y_2620_ = v_e_2600_;
goto v___jp_2619_;
}
else
{
lean_object* v_val_2662_; 
lean_dec_ref(v_e_2600_);
v_val_2662_ = lean_ctor_get(v_e_x3f_2661_, 0);
lean_inc(v_val_2662_);
lean_dec_ref_known(v_e_x3f_2661_, 1);
v___y_2620_ = v_val_2662_;
goto v___jp_2619_;
}
}
}
v___jp_2619_:
{
switch(lean_obj_tag(v___y_2620_))
{
case 7:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2621_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___closed__0));
v___x_2622_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6(v_pre_2599_, v_post_2601_, v_usedLetOnly_2602_, v_skipConstInApp_2603_, v_skipInstances_2604_, v___x_2621_, v___y_2620_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
return v___x_2622_;
}
case 6:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2623_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___closed__0));
v___x_2624_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7(v_pre_2599_, v_post_2601_, v_usedLetOnly_2602_, v_skipConstInApp_2603_, v_skipInstances_2604_, v___x_2623_, v___y_2620_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
return v___x_2624_;
}
case 8:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2625_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___closed__0));
v___x_2626_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8(v_pre_2599_, v_post_2601_, v_usedLetOnly_2602_, v_skipConstInApp_2603_, v_skipInstances_2604_, v___x_2625_, v___y_2620_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
return v___x_2626_;
}
case 5:
{
lean_object* v_dummy_2627_; lean_object* v_nargs_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; 
v_dummy_2627_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___closed__1);
v_nargs_2628_ = l_Lean_Expr_getAppNumArgs(v___y_2620_);
lean_inc(v_nargs_2628_);
v___x_2629_ = lean_mk_array(v_nargs_2628_, v_dummy_2627_);
v___x_2630_ = lean_unsigned_to_nat(1u);
v___x_2631_ = lean_nat_sub(v_nargs_2628_, v___x_2630_);
lean_dec(v_nargs_2628_);
v___x_2632_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__9(v_skipInstances_2604_, v_pre_2599_, v_post_2601_, v_usedLetOnly_2602_, v_skipConstInApp_2603_, v___y_2620_, v___x_2629_, v___x_2631_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
return v___x_2632_;
}
case 10:
{
lean_object* v_data_2633_; lean_object* v_expr_2634_; lean_object* v___x_2635_; 
v_data_2633_ = lean_ctor_get(v___y_2620_, 0);
v_expr_2634_ = lean_ctor_get(v___y_2620_, 1);
lean_inc_ref(v_expr_2634_);
lean_inc_ref(v_post_2601_);
lean_inc_ref(v_pre_2599_);
v___x_2635_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2599_, v_post_2601_, v_usedLetOnly_2602_, v_skipConstInApp_2603_, v_skipInstances_2604_, v_expr_2634_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_object* v_a_2636_; size_t v___x_2637_; size_t v___x_2638_; uint8_t v___x_2639_; 
v_a_2636_ = lean_ctor_get(v___x_2635_, 0);
lean_inc(v_a_2636_);
lean_dec_ref_known(v___x_2635_, 1);
v___x_2637_ = lean_ptr_addr(v_expr_2634_);
v___x_2638_ = lean_ptr_addr(v_a_2636_);
v___x_2639_ = lean_usize_dec_eq(v___x_2637_, v___x_2638_);
if (v___x_2639_ == 0)
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
lean_inc(v_data_2633_);
lean_dec_ref_known(v___y_2620_, 2);
v___x_2640_ = l_Lean_Expr_mdata___override(v_data_2633_, v_a_2636_);
v___x_2641_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2599_, v_post_2601_, v_usedLetOnly_2602_, v_skipConstInApp_2603_, v_skipInstances_2604_, v___x_2640_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
return v___x_2641_;
}
else
{
lean_object* v___x_2642_; 
lean_dec(v_a_2636_);
v___x_2642_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2599_, v_post_2601_, v_usedLetOnly_2602_, v_skipConstInApp_2603_, v_skipInstances_2604_, v___y_2620_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
return v___x_2642_;
}
}
else
{
lean_dec_ref_known(v___y_2620_, 2);
lean_dec_ref(v_post_2601_);
lean_dec_ref(v_pre_2599_);
return v___x_2635_;
}
}
case 11:
{
lean_object* v_typeName_2643_; lean_object* v_idx_2644_; lean_object* v_struct_2645_; lean_object* v___x_2646_; 
v_typeName_2643_ = lean_ctor_get(v___y_2620_, 0);
v_idx_2644_ = lean_ctor_get(v___y_2620_, 1);
v_struct_2645_ = lean_ctor_get(v___y_2620_, 2);
lean_inc_ref(v_struct_2645_);
lean_inc_ref(v_post_2601_);
lean_inc_ref(v_pre_2599_);
v___x_2646_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2599_, v_post_2601_, v_usedLetOnly_2602_, v_skipConstInApp_2603_, v_skipInstances_2604_, v_struct_2645_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
if (lean_obj_tag(v___x_2646_) == 0)
{
lean_object* v_a_2647_; size_t v___x_2648_; size_t v___x_2649_; uint8_t v___x_2650_; 
v_a_2647_ = lean_ctor_get(v___x_2646_, 0);
lean_inc(v_a_2647_);
lean_dec_ref_known(v___x_2646_, 1);
v___x_2648_ = lean_ptr_addr(v_struct_2645_);
v___x_2649_ = lean_ptr_addr(v_a_2647_);
v___x_2650_ = lean_usize_dec_eq(v___x_2648_, v___x_2649_);
if (v___x_2650_ == 0)
{
lean_object* v___x_2651_; lean_object* v___x_2652_; 
lean_inc(v_idx_2644_);
lean_inc(v_typeName_2643_);
lean_dec_ref_known(v___y_2620_, 3);
v___x_2651_ = l_Lean_Expr_proj___override(v_typeName_2643_, v_idx_2644_, v_a_2647_);
v___x_2652_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2599_, v_post_2601_, v_usedLetOnly_2602_, v_skipConstInApp_2603_, v_skipInstances_2604_, v___x_2651_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
return v___x_2652_;
}
else
{
lean_object* v___x_2653_; 
lean_dec(v_a_2647_);
v___x_2653_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2599_, v_post_2601_, v_usedLetOnly_2602_, v_skipConstInApp_2603_, v_skipInstances_2604_, v___y_2620_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
return v___x_2653_;
}
}
else
{
lean_dec_ref_known(v___y_2620_, 3);
lean_dec_ref(v_post_2601_);
lean_dec_ref(v_pre_2599_);
return v___x_2646_;
}
}
default: 
{
lean_object* v___x_2654_; 
v___x_2654_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2599_, v_post_2601_, v_usedLetOnly_2602_, v_skipConstInApp_2603_, v_skipInstances_2604_, v___y_2620_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
return v___x_2654_;
}
}
}
}
}
else
{
lean_object* v_a_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2671_; 
lean_dec_ref(v_post_2601_);
lean_dec_ref(v_e_2600_);
lean_dec_ref(v_pre_2599_);
v_a_2664_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2666_ = v___x_2614_;
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_a_2664_);
lean_dec(v___x_2614_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2669_; 
if (v_isShared_2667_ == 0)
{
v___x_2669_ = v___x_2666_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_a_2664_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
}
else
{
lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2679_; 
lean_dec_ref(v_post_2601_);
lean_dec_ref(v_e_2600_);
lean_dec_ref(v_pre_2599_);
v_a_2672_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2674_ = v___x_2613_;
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v___x_2613_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2677_; 
if (v_isShared_2675_ == 0)
{
v___x_2677_ = v___x_2674_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_a_2672_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2598_ = stack[0].m_obj;
lean_object* v_pre_2599_ = stack[1].m_obj;
lean_object* v_e_2600_ = stack[2].m_obj;
lean_object* v_post_2601_ = stack[3].m_obj;
uint8_t v_usedLetOnly_2602_ = stack[4].m_num;
uint8_t v_skipConstInApp_2603_ = stack[5].m_num;
uint8_t v_skipInstances_2604_ = stack[6].m_num;
lean_object* v___y_2605_ = stack[7].m_obj;
lean_object* v___y_2606_ = stack[8].m_obj;
lean_object* v___y_2607_ = stack[9].m_obj;
lean_object* v___y_2608_ = stack[10].m_obj;
lean_object* v___y_2609_ = stack[11].m_obj;
lean_object* v___y_2610_ = stack[12].m_obj;
lean_object* v___y_2611_ = stack[13].m_obj;
lean_object* v_res_2680_;
v_res_2680_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1(v___x_2598_, v_pre_2599_, v_e_2600_, v_post_2601_, v_usedLetOnly_2602_, v_skipConstInApp_2603_, v_skipInstances_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
stack->m_obj
 = v_res_2680_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___boxed(lean_object* v___x_2681_, lean_object* v_pre_2682_, lean_object* v_e_2683_, lean_object* v_post_2684_, lean_object* v_usedLetOnly_2685_, lean_object* v_skipConstInApp_2686_, lean_object* v_skipInstances_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_){
_start:
{
uint8_t v_usedLetOnly_boxed_2696_; uint8_t v_skipConstInApp_boxed_2697_; uint8_t v_skipInstances_boxed_2698_; lean_object* v_res_2699_; 
v_usedLetOnly_boxed_2696_ = lean_unbox(v_usedLetOnly_2685_);
v_skipConstInApp_boxed_2697_ = lean_unbox(v_skipConstInApp_2686_);
v_skipInstances_boxed_2698_ = lean_unbox(v_skipInstances_2687_);
v_res_2699_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1(v___x_2681_, v_pre_2682_, v_e_2683_, v_post_2684_, v_usedLetOnly_boxed_2696_, v_skipConstInApp_boxed_2697_, v_skipInstances_boxed_2698_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
lean_dec(v___y_2688_);
return v_res_2699_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(lean_object* v_pre_2700_, lean_object* v_post_2701_, uint8_t v_usedLetOnly_2702_, uint8_t v_skipConstInApp_2703_, uint8_t v_skipInstances_2704_, lean_object* v_e_2705_, lean_object* v_a_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_){
_start:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; 
lean_inc(v_a_2706_);
v___x_2714_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2714_, 0, lean_box(0));
lean_closure_set(v___x_2714_, 1, lean_box(0));
lean_closure_set(v___x_2714_, 2, v_a_2706_);
v___x_2715_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__0(lean_box(0), v___x_2714_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2750_; 
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2718_ = v___x_2715_;
v_isShared_2719_ = v_isSharedCheck_2750_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2715_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2750_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2720_; 
v___x_2720_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5___redArg(v_a_2716_, v_e_2705_);
lean_dec(v_a_2716_);
if (lean_obj_tag(v___x_2720_) == 0)
{
lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___f_2725_; lean_object* v___x_2726_; 
lean_del_object(v___x_2718_);
v___x_2721_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___closed__0));
v___x_2722_ = lean_box(v_usedLetOnly_2702_);
v___x_2723_ = lean_box(v_skipConstInApp_2703_);
v___x_2724_ = lean_box(v_skipInstances_2704_);
lean_inc_ref(v_e_2705_);
v___f_2725_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__1___boxed), 15, 7);
lean_closure_set(v___f_2725_, 0, v___x_2721_);
lean_closure_set(v___f_2725_, 1, v_pre_2700_);
lean_closure_set(v___f_2725_, 2, v_e_2705_);
lean_closure_set(v___f_2725_, 3, v_post_2701_);
lean_closure_set(v___f_2725_, 4, v___x_2722_);
lean_closure_set(v___f_2725_, 5, v___x_2723_);
lean_closure_set(v___f_2725_, 6, v___x_2724_);
v___x_2726_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10___redArg(v___f_2725_, v_a_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
if (lean_obj_tag(v___x_2726_) == 0)
{
lean_object* v_a_2727_; lean_object* v___f_2728_; lean_object* v___x_2729_; 
v_a_2727_ = lean_ctor_get(v___x_2726_, 0);
lean_inc_n(v_a_2727_, 2);
lean_dec_ref_known(v___x_2726_, 1);
lean_inc(v_a_2706_);
v___f_2728_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2728_, 0, v_a_2706_);
lean_closure_set(v___f_2728_, 1, v_e_2705_);
lean_closure_set(v___f_2728_, 2, v_a_2727_);
v___x_2729_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___lam__0(lean_box(0), v___f_2728_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
if (lean_obj_tag(v___x_2729_) == 0)
{
lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2736_; 
v_isSharedCheck_2736_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2736_ == 0)
{
lean_object* v_unused_2737_; 
v_unused_2737_ = lean_ctor_get(v___x_2729_, 0);
lean_dec(v_unused_2737_);
v___x_2731_ = v___x_2729_;
v_isShared_2732_ = v_isSharedCheck_2736_;
goto v_resetjp_2730_;
}
else
{
lean_dec(v___x_2729_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2736_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v___x_2734_; 
if (v_isShared_2732_ == 0)
{
lean_ctor_set(v___x_2731_, 0, v_a_2727_);
v___x_2734_ = v___x_2731_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_a_2727_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
return v___x_2734_;
}
}
}
else
{
lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2745_; 
lean_dec(v_a_2727_);
v_a_2738_ = lean_ctor_get(v___x_2729_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2740_ = v___x_2729_;
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___x_2729_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2743_; 
if (v_isShared_2741_ == 0)
{
v___x_2743_ = v___x_2740_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_a_2738_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
}
else
{
lean_dec_ref(v_e_2705_);
return v___x_2726_;
}
}
else
{
lean_object* v_val_2746_; lean_object* v___x_2748_; 
lean_dec_ref(v_e_2705_);
lean_dec_ref(v_post_2701_);
lean_dec_ref(v_pre_2700_);
v_val_2746_ = lean_ctor_get(v___x_2720_, 0);
lean_inc(v_val_2746_);
lean_dec_ref_known(v___x_2720_, 1);
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 0, v_val_2746_);
v___x_2748_ = v___x_2718_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_val_2746_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
else
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2758_; 
lean_dec_ref(v_e_2705_);
lean_dec_ref(v_post_2701_);
lean_dec_ref(v_pre_2700_);
v_a_2751_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2753_ = v___x_2715_;
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2715_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2756_; 
if (v_isShared_2754_ == 0)
{
v___x_2756_ = v___x_2753_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_a_2751_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_2700_ = stack[0].m_obj;
lean_object* v_post_2701_ = stack[1].m_obj;
uint8_t v_usedLetOnly_2702_ = stack[2].m_num;
uint8_t v_skipConstInApp_2703_ = stack[3].m_num;
uint8_t v_skipInstances_2704_ = stack[4].m_num;
lean_object* v_e_2705_ = stack[5].m_obj;
lean_object* v_a_2706_ = stack[6].m_obj;
lean_object* v___y_2707_ = stack[7].m_obj;
lean_object* v___y_2708_ = stack[8].m_obj;
lean_object* v___y_2709_ = stack[9].m_obj;
lean_object* v___y_2710_ = stack[10].m_obj;
lean_object* v___y_2711_ = stack[11].m_obj;
lean_object* v___y_2712_ = stack[12].m_obj;
lean_object* v_res_2759_;
v_res_2759_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2700_, v_post_2701_, v_usedLetOnly_2702_, v_skipConstInApp_2703_, v_skipInstances_2704_, v_e_2705_, v_a_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
stack->m_obj
 = v_res_2759_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6(lean_object* v_pre_2760_, lean_object* v_post_2761_, uint8_t v_usedLetOnly_2762_, uint8_t v_skipConstInApp_2763_, uint8_t v_skipInstances_2764_, lean_object* v_fvars_2765_, lean_object* v_e_2766_, lean_object* v_a_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_){
_start:
{
if (lean_obj_tag(v_e_2766_) == 7)
{
lean_object* v_binderName_2775_; lean_object* v_binderType_2776_; lean_object* v_body_2777_; uint8_t v_binderInfo_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___f_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; 
v_binderName_2775_ = lean_ctor_get(v_e_2766_, 0);
lean_inc(v_binderName_2775_);
v_binderType_2776_ = lean_ctor_get(v_e_2766_, 1);
lean_inc_ref(v_binderType_2776_);
v_body_2777_ = lean_ctor_get(v_e_2766_, 2);
lean_inc_ref(v_body_2777_);
v_binderInfo_2778_ = lean_ctor_get_uint8(v_e_2766_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2766_, 3);
v___x_2779_ = lean_box(v_usedLetOnly_2762_);
v___x_2780_ = lean_box(v_skipConstInApp_2763_);
v___x_2781_ = lean_box(v_skipInstances_2764_);
lean_inc_ref(v_post_2761_);
lean_inc_ref(v_pre_2760_);
lean_inc_ref(v_fvars_2765_);
v___f_2782_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6___lam__0___boxed), 16, 7);
lean_closure_set(v___f_2782_, 0, v_fvars_2765_);
lean_closure_set(v___f_2782_, 1, v_pre_2760_);
lean_closure_set(v___f_2782_, 2, v_post_2761_);
lean_closure_set(v___f_2782_, 3, v___x_2779_);
lean_closure_set(v___f_2782_, 4, v___x_2780_);
lean_closure_set(v___f_2782_, 5, v___x_2781_);
lean_closure_set(v___f_2782_, 6, v_body_2777_);
v___x_2783_ = lean_expr_instantiate_rev(v_binderType_2776_, v_fvars_2765_);
lean_dec_ref(v_fvars_2765_);
lean_dec_ref(v_binderType_2776_);
v___x_2784_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2760_, v_post_2761_, v_usedLetOnly_2762_, v_skipConstInApp_2763_, v_skipInstances_2764_, v___x_2783_, v_a_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_object* v_a_2785_; uint8_t v___x_2786_; lean_object* v___x_2787_; 
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_a_2785_);
lean_dec_ref_known(v___x_2784_, 1);
v___x_2786_ = 0;
v___x_2787_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_2775_, v_binderInfo_2778_, v_a_2785_, v___f_2782_, v___x_2786_, v_a_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
return v___x_2787_;
}
else
{
lean_dec_ref(v___f_2782_);
lean_dec(v_binderName_2775_);
return v___x_2784_;
}
}
else
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2788_ = lean_expr_instantiate_rev(v_e_2766_, v_fvars_2765_);
lean_dec_ref(v_e_2766_);
lean_inc_ref(v_post_2761_);
lean_inc_ref(v_pre_2760_);
v___x_2789_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2760_, v_post_2761_, v_usedLetOnly_2762_, v_skipConstInApp_2763_, v_skipInstances_2764_, v___x_2788_, v_a_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_a_2790_; uint8_t v___x_2791_; uint8_t v___x_2792_; uint8_t v___x_2793_; lean_object* v___x_2794_; 
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_a_2790_);
lean_dec_ref_known(v___x_2789_, 1);
v___x_2791_ = 0;
v___x_2792_ = 1;
v___x_2793_ = 1;
v___x_2794_ = l_Lean_Meta_mkForallFVars(v_fvars_2765_, v_a_2790_, v___x_2791_, v_usedLetOnly_2762_, v___x_2792_, v___x_2793_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
lean_dec_ref(v_fvars_2765_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v_a_2795_; lean_object* v___x_2796_; 
v_a_2795_ = lean_ctor_get(v___x_2794_, 0);
lean_inc(v_a_2795_);
lean_dec_ref_known(v___x_2794_, 1);
v___x_2796_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2760_, v_post_2761_, v_usedLetOnly_2762_, v_skipConstInApp_2763_, v_skipInstances_2764_, v_a_2795_, v_a_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
return v___x_2796_;
}
else
{
lean_dec_ref(v_post_2761_);
lean_dec_ref(v_pre_2760_);
return v___x_2794_;
}
}
else
{
lean_dec_ref(v_fvars_2765_);
lean_dec_ref(v_post_2761_);
lean_dec_ref(v_pre_2760_);
return v___x_2789_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_2760_ = stack[0].m_obj;
lean_object* v_post_2761_ = stack[1].m_obj;
uint8_t v_usedLetOnly_2762_ = stack[2].m_num;
uint8_t v_skipConstInApp_2763_ = stack[3].m_num;
uint8_t v_skipInstances_2764_ = stack[4].m_num;
lean_object* v_fvars_2765_ = stack[5].m_obj;
lean_object* v_e_2766_ = stack[6].m_obj;
lean_object* v_a_2767_ = stack[7].m_obj;
lean_object* v___y_2768_ = stack[8].m_obj;
lean_object* v___y_2769_ = stack[9].m_obj;
lean_object* v___y_2770_ = stack[10].m_obj;
lean_object* v___y_2771_ = stack[11].m_obj;
lean_object* v___y_2772_ = stack[12].m_obj;
lean_object* v___y_2773_ = stack[13].m_obj;
lean_object* v_res_2797_;
v_res_2797_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6(v_pre_2760_, v_post_2761_, v_usedLetOnly_2762_, v_skipConstInApp_2763_, v_skipInstances_2764_, v_fvars_2765_, v_e_2766_, v_a_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
stack->m_obj
 = v_res_2797_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6___lam__0(lean_object* v_fvars_2798_, lean_object* v_pre_2799_, lean_object* v_post_2800_, uint8_t v_usedLetOnly_2801_, uint8_t v_skipConstInApp_2802_, uint8_t v_skipInstances_2803_, lean_object* v_body_2804_, lean_object* v_x_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_){
_start:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; 
v___x_2814_ = lean_array_push(v_fvars_2798_, v_x_2805_);
v___x_2815_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6(v_pre_2799_, v_post_2800_, v_usedLetOnly_2801_, v_skipConstInApp_2802_, v_skipInstances_2803_, v___x_2814_, v_body_2804_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_);
return v___x_2815_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_2798_ = stack[0].m_obj;
lean_object* v_pre_2799_ = stack[1].m_obj;
lean_object* v_post_2800_ = stack[2].m_obj;
uint8_t v_usedLetOnly_2801_ = stack[3].m_num;
uint8_t v_skipConstInApp_2802_ = stack[4].m_num;
uint8_t v_skipInstances_2803_ = stack[5].m_num;
lean_object* v_body_2804_ = stack[6].m_obj;
lean_object* v_x_2805_ = stack[7].m_obj;
lean_object* v___y_2806_ = stack[8].m_obj;
lean_object* v___y_2807_ = stack[9].m_obj;
lean_object* v___y_2808_ = stack[10].m_obj;
lean_object* v___y_2809_ = stack[11].m_obj;
lean_object* v___y_2810_ = stack[12].m_obj;
lean_object* v___y_2811_ = stack[13].m_obj;
lean_object* v___y_2812_ = stack[14].m_obj;
lean_object* v_res_2816_;
v_res_2816_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6___lam__0(v_fvars_2798_, v_pre_2799_, v_post_2800_, v_usedLetOnly_2801_, v_skipConstInApp_2802_, v_skipInstances_2803_, v_body_2804_, v_x_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_);
stack->m_obj
 = v_res_2816_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_2817_, lean_object* v_post_2818_, lean_object* v_usedLetOnly_2819_, lean_object* v_skipConstInApp_2820_, lean_object* v_skipInstances_2821_, lean_object* v_e_2822_, lean_object* v_a_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_){
_start:
{
uint8_t v_usedLetOnly_boxed_2831_; uint8_t v_skipConstInApp_boxed_2832_; uint8_t v_skipInstances_boxed_2833_; lean_object* v_res_2834_; 
v_usedLetOnly_boxed_2831_ = lean_unbox(v_usedLetOnly_2819_);
v_skipConstInApp_boxed_2832_ = lean_unbox(v_skipConstInApp_2820_);
v_skipInstances_boxed_2833_ = lean_unbox(v_skipInstances_2821_);
v_res_2834_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__3(v_pre_2817_, v_post_2818_, v_usedLetOnly_boxed_2831_, v_skipConstInApp_boxed_2832_, v_skipInstances_boxed_2833_, v_e_2822_, v_a_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec(v___y_2825_);
lean_dec_ref(v___y_2824_);
lean_dec(v_a_2823_);
return v_res_2834_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_2835_, lean_object* v_post_2836_, lean_object* v_usedLetOnly_2837_, lean_object* v_skipConstInApp_2838_, lean_object* v_skipInstances_2839_, lean_object* v_sz_2840_, lean_object* v_i_2841_, lean_object* v_bs_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_){
_start:
{
uint8_t v_usedLetOnly_boxed_2851_; uint8_t v_skipConstInApp_boxed_2852_; uint8_t v_skipInstances_boxed_2853_; size_t v_sz_boxed_2854_; size_t v_i_boxed_2855_; lean_object* v_res_2856_; 
v_usedLetOnly_boxed_2851_ = lean_unbox(v_usedLetOnly_2837_);
v_skipConstInApp_boxed_2852_ = lean_unbox(v_skipConstInApp_2838_);
v_skipInstances_boxed_2853_ = lean_unbox(v_skipInstances_2839_);
v_sz_boxed_2854_ = lean_unbox_usize(v_sz_2840_);
lean_dec(v_sz_2840_);
v_i_boxed_2855_ = lean_unbox_usize(v_i_2841_);
lean_dec(v_i_2841_);
v_res_2856_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__2(v_pre_2835_, v_post_2836_, v_usedLetOnly_boxed_2851_, v_skipConstInApp_boxed_2852_, v_skipInstances_boxed_2853_, v_sz_boxed_2854_, v_i_boxed_2855_, v_bs_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
return v_res_2856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1___boxed(lean_object* v_pre_2857_, lean_object* v_post_2858_, lean_object* v_usedLetOnly_2859_, lean_object* v_skipConstInApp_2860_, lean_object* v_skipInstances_2861_, lean_object* v_e_2862_, lean_object* v_a_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_){
_start:
{
uint8_t v_usedLetOnly_boxed_2871_; uint8_t v_skipConstInApp_boxed_2872_; uint8_t v_skipInstances_boxed_2873_; lean_object* v_res_2874_; 
v_usedLetOnly_boxed_2871_ = lean_unbox(v_usedLetOnly_2859_);
v_skipConstInApp_boxed_2872_ = lean_unbox(v_skipConstInApp_2860_);
v_skipInstances_boxed_2873_ = lean_unbox(v_skipInstances_2861_);
v_res_2874_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2857_, v_post_2858_, v_usedLetOnly_boxed_2871_, v_skipConstInApp_boxed_2872_, v_skipInstances_boxed_2873_, v_e_2862_, v_a_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec(v_a_2863_);
return v_res_2874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6___boxed(lean_object* v_pre_2875_, lean_object* v_post_2876_, lean_object* v_usedLetOnly_2877_, lean_object* v_skipConstInApp_2878_, lean_object* v_skipInstances_2879_, lean_object* v_fvars_2880_, lean_object* v_e_2881_, lean_object* v_a_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_){
_start:
{
uint8_t v_usedLetOnly_boxed_2890_; uint8_t v_skipConstInApp_boxed_2891_; uint8_t v_skipInstances_boxed_2892_; lean_object* v_res_2893_; 
v_usedLetOnly_boxed_2890_ = lean_unbox(v_usedLetOnly_2877_);
v_skipConstInApp_boxed_2891_ = lean_unbox(v_skipConstInApp_2878_);
v_skipInstances_boxed_2892_ = lean_unbox(v_skipInstances_2879_);
v_res_2893_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6(v_pre_2875_, v_post_2876_, v_usedLetOnly_boxed_2890_, v_skipConstInApp_boxed_2891_, v_skipInstances_boxed_2892_, v_fvars_2880_, v_e_2881_, v_a_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec_ref(v___y_2885_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2883_);
lean_dec(v_a_2882_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7___boxed(lean_object* v_pre_2894_, lean_object* v_post_2895_, lean_object* v_usedLetOnly_2896_, lean_object* v_skipConstInApp_2897_, lean_object* v_skipInstances_2898_, lean_object* v_fvars_2899_, lean_object* v_e_2900_, lean_object* v_a_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_){
_start:
{
uint8_t v_usedLetOnly_boxed_2909_; uint8_t v_skipConstInApp_boxed_2910_; uint8_t v_skipInstances_boxed_2911_; lean_object* v_res_2912_; 
v_usedLetOnly_boxed_2909_ = lean_unbox(v_usedLetOnly_2896_);
v_skipConstInApp_boxed_2910_ = lean_unbox(v_skipConstInApp_2897_);
v_skipInstances_boxed_2911_ = lean_unbox(v_skipInstances_2898_);
v_res_2912_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__7(v_pre_2894_, v_post_2895_, v_usedLetOnly_boxed_2909_, v_skipConstInApp_boxed_2910_, v_skipInstances_boxed_2911_, v_fvars_2899_, v_e_2900_, v_a_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
lean_dec(v_a_2901_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8___boxed(lean_object* v_pre_2913_, lean_object* v_post_2914_, lean_object* v_usedLetOnly_2915_, lean_object* v_skipConstInApp_2916_, lean_object* v_skipInstances_2917_, lean_object* v_fvars_2918_, lean_object* v_e_2919_, lean_object* v_a_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
uint8_t v_usedLetOnly_boxed_2928_; uint8_t v_skipConstInApp_boxed_2929_; uint8_t v_skipInstances_boxed_2930_; lean_object* v_res_2931_; 
v_usedLetOnly_boxed_2928_ = lean_unbox(v_usedLetOnly_2915_);
v_skipConstInApp_boxed_2929_ = lean_unbox(v_skipConstInApp_2916_);
v_skipInstances_boxed_2930_ = lean_unbox(v_skipInstances_2917_);
v_res_2931_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8(v_pre_2913_, v_post_2914_, v_usedLetOnly_boxed_2928_, v_skipConstInApp_boxed_2929_, v_skipInstances_boxed_2930_, v_fvars_2918_, v_e_2919_, v_a_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec(v_a_2920_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_2932_ = _args[0];
lean_object* v___x_2933_ = _args[1];
lean_object* v_pre_2934_ = _args[2];
lean_object* v_post_2935_ = _args[3];
lean_object* v_usedLetOnly_2936_ = _args[4];
lean_object* v_skipConstInApp_2937_ = _args[5];
lean_object* v_skipInstances_2938_ = _args[6];
lean_object* v_a_2939_ = _args[7];
lean_object* v_b_2940_ = _args[8];
lean_object* v___y_2941_ = _args[9];
lean_object* v___y_2942_ = _args[10];
lean_object* v___y_2943_ = _args[11];
lean_object* v___y_2944_ = _args[12];
lean_object* v___y_2945_ = _args[13];
lean_object* v___y_2946_ = _args[14];
lean_object* v___y_2947_ = _args[15];
lean_object* v___y_2948_ = _args[16];
_start:
{
uint8_t v_usedLetOnly_boxed_2949_; uint8_t v_skipConstInApp_boxed_2950_; uint8_t v_skipInstances_boxed_2951_; lean_object* v_res_2952_; 
v_usedLetOnly_boxed_2949_ = lean_unbox(v_usedLetOnly_2936_);
v_skipConstInApp_boxed_2950_ = lean_unbox(v_skipConstInApp_2937_);
v_skipInstances_boxed_2951_ = lean_unbox(v_skipInstances_2938_);
v_res_2952_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg(v_upperBound_2932_, v___x_2933_, v_pre_2934_, v_post_2935_, v_usedLetOnly_boxed_2949_, v_skipConstInApp_boxed_2950_, v_skipInstances_boxed_2951_, v_a_2939_, v_b_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2943_);
lean_dec_ref(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___x_2933_);
lean_dec(v_upperBound_2932_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__9___boxed(lean_object* v_skipInstances_2953_, lean_object* v_pre_2954_, lean_object* v_post_2955_, lean_object* v_usedLetOnly_2956_, lean_object* v_skipConstInApp_2957_, lean_object* v_x_2958_, lean_object* v_x_2959_, lean_object* v_x_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_){
_start:
{
uint8_t v_skipInstances_boxed_2969_; uint8_t v_usedLetOnly_boxed_2970_; uint8_t v_skipConstInApp_boxed_2971_; lean_object* v_res_2972_; 
v_skipInstances_boxed_2969_ = lean_unbox(v_skipInstances_2953_);
v_usedLetOnly_boxed_2970_ = lean_unbox(v_usedLetOnly_2956_);
v_skipConstInApp_boxed_2971_ = lean_unbox(v_skipConstInApp_2957_);
v_res_2972_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__9(v_skipInstances_boxed_2969_, v_pre_2954_, v_post_2955_, v_usedLetOnly_boxed_2970_, v_skipConstInApp_boxed_2971_, v_x_2958_, v_x_2959_, v_x_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
lean_dec(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec(v___y_2965_);
lean_dec_ref(v___y_2964_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec(v___y_2961_);
return v_res_2972_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v___x_2973_ = lean_box(0);
v___x_2974_ = lean_unsigned_to_nat(16u);
v___x_2975_ = lean_mk_array(v___x_2974_, v___x_2973_);
return v___x_2975_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2976_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__0);
v___x_2977_ = lean_unsigned_to_nat(0u);
v___x_2978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2978_, 0, v___x_2977_);
lean_ctor_set(v___x_2978_, 1, v___x_2976_);
return v___x_2978_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__2(void){
_start:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; 
v___x_2979_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__1, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__1);
v___x_2980_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2980_, 0, lean_box(0));
lean_closure_set(v___x_2980_, 1, lean_box(0));
lean_closure_set(v___x_2980_, 2, v___x_2979_);
return v___x_2980_;
}
}
lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1(lean_object* v_input_2981_, lean_object* v_pre_2982_, lean_object* v_post_2983_, uint8_t v_usedLetOnly_2984_, uint8_t v_skipConstInApp_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_){
_start:
{
uint8_t v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v_a_2996_; lean_object* v___x_2997_; 
v___x_2993_ = 0;
v___x_2994_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__2, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___closed__2);
v___x_2995_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___lam__0(lean_box(0), v___x_2994_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
v_a_2996_ = lean_ctor_get(v___x_2995_, 0);
lean_inc(v_a_2996_);
lean_dec_ref(v___x_2995_);
v___x_2997_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1(v_pre_2982_, v_post_2983_, v_usedLetOnly_2984_, v_skipConstInApp_2985_, v___x_2993_, v_input_2981_, v_a_2996_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3007_; 
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_a_2998_);
lean_dec_ref_known(v___x_2997_, 1);
v___x_2999_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2999_, 0, lean_box(0));
lean_closure_set(v___x_2999_, 1, lean_box(0));
lean_closure_set(v___x_2999_, 2, v_a_2996_);
v___x_3000_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___lam__0(lean_box(0), v___x_2999_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
v_isSharedCheck_3007_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3007_ == 0)
{
lean_object* v_unused_3008_; 
v_unused_3008_ = lean_ctor_get(v___x_3000_, 0);
lean_dec(v_unused_3008_);
v___x_3002_ = v___x_3000_;
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
else
{
lean_dec(v___x_3000_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3005_; 
if (v_isShared_3003_ == 0)
{
lean_ctor_set(v___x_3002_, 0, v_a_2998_);
v___x_3005_ = v___x_3002_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_a_2998_);
v___x_3005_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
return v___x_3005_;
}
}
}
else
{
lean_dec(v_a_2996_);
return v___x_2997_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_input_2981_ = stack[0].m_obj;
lean_object* v_pre_2982_ = stack[1].m_obj;
lean_object* v_post_2983_ = stack[2].m_obj;
uint8_t v_usedLetOnly_2984_ = stack[3].m_num;
uint8_t v_skipConstInApp_2985_ = stack[4].m_num;
lean_object* v___y_2986_ = stack[5].m_obj;
lean_object* v___y_2987_ = stack[6].m_obj;
lean_object* v___y_2988_ = stack[7].m_obj;
lean_object* v___y_2989_ = stack[8].m_obj;
lean_object* v___y_2990_ = stack[9].m_obj;
lean_object* v___y_2991_ = stack[10].m_obj;
lean_object* v_res_3009_;
v_res_3009_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1(v_input_2981_, v_pre_2982_, v_post_2983_, v_usedLetOnly_2984_, v_skipConstInApp_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
stack->m_obj
 = v_res_3009_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1___boxed(lean_object* v_input_3010_, lean_object* v_pre_3011_, lean_object* v_post_3012_, lean_object* v_usedLetOnly_3013_, lean_object* v_skipConstInApp_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_){
_start:
{
uint8_t v_usedLetOnly_boxed_3022_; uint8_t v_skipConstInApp_boxed_3023_; lean_object* v_res_3024_; 
v_usedLetOnly_boxed_3022_ = lean_unbox(v_usedLetOnly_3013_);
v_skipConstInApp_boxed_3023_ = lean_unbox(v_skipConstInApp_3014_);
v_res_3024_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1(v_input_3010_, v_pre_3011_, v_post_3012_, v_usedLetOnly_boxed_3022_, v_skipConstInApp_boxed_3023_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_);
lean_dec(v___y_3020_);
lean_dec_ref(v___y_3019_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
return v_res_3024_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts(lean_object* v_stx_3055_, lean_object* v_expectedType_x3f_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_){
_start:
{
lean_object* v___f_3064_; lean_object* v___f_3065_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___x_3097_; 
v___f_3064_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__0));
v___f_3065_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__1));
lean_inc(v_expectedType_x3f_3056_);
v___x_3097_ = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(v_expectedType_x3f_3056_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_);
if (lean_obj_tag(v___x_3097_) == 0)
{
lean_dec_ref_known(v___x_3097_, 1);
if (lean_obj_tag(v_expectedType_x3f_3056_) == 1)
{
lean_object* v_val_3098_; lean_object* v___x_3099_; lean_object* v_a_3100_; uint8_t v___x_3101_; 
v_val_3098_ = lean_ctor_get(v_expectedType_x3f_3056_, 0);
lean_inc(v_val_3098_);
v___x_3099_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0___redArg(v_val_3098_, v_a_3060_);
v_a_3100_ = lean_ctor_get(v___x_3099_, 0);
lean_inc(v_a_3100_);
lean_dec_ref(v___x_3099_);
v___x_3101_ = l_Lean_Expr_hasExprMVar(v_a_3100_);
lean_dec(v_a_3100_);
if (v___x_3101_ == 0)
{
v___y_3067_ = v_a_3057_;
v___y_3068_ = v_a_3058_;
v___y_3069_ = v_a_3059_;
v___y_3070_ = v_a_3060_;
v___y_3071_ = v_a_3061_;
v___y_3072_ = v_a_3062_;
goto v___jp_3066_;
}
else
{
lean_object* v___x_3102_; 
v___x_3102_ = l_Lean_Elab_Term_tryPostpone(v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_);
if (lean_obj_tag(v___x_3102_) == 0)
{
lean_dec_ref_known(v___x_3102_, 1);
v___y_3067_ = v_a_3057_;
v___y_3068_ = v_a_3058_;
v___y_3069_ = v_a_3059_;
v___y_3070_ = v_a_3060_;
v___y_3071_ = v_a_3061_;
v___y_3072_ = v_a_3062_;
goto v___jp_3066_;
}
else
{
lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3110_; 
lean_dec_ref_known(v_expectedType_x3f_3056_, 1);
v_a_3103_ = lean_ctor_get(v___x_3102_, 0);
v_isSharedCheck_3110_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3105_ = v___x_3102_;
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_dec(v___x_3102_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3108_; 
if (v_isShared_3106_ == 0)
{
v___x_3108_ = v___x_3105_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_a_3103_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
}
}
else
{
v___y_3067_ = v_a_3057_;
v___y_3068_ = v_a_3058_;
v___y_3069_ = v_a_3059_;
v___y_3070_ = v_a_3060_;
v___y_3071_ = v_a_3061_;
v___y_3072_ = v_a_3062_;
goto v___jp_3066_;
}
}
else
{
lean_object* v_a_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3118_; 
lean_dec(v_expectedType_x3f_3056_);
v_a_3111_ = lean_ctor_get(v___x_3097_, 0);
v_isSharedCheck_3118_ = !lean_is_exclusive(v___x_3097_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3113_ = v___x_3097_;
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_a_3111_);
lean_dec(v___x_3097_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v___x_3116_; 
if (v_isShared_3114_ == 0)
{
v___x_3116_ = v___x_3113_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v_a_3111_);
v___x_3116_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
return v___x_3116_;
}
}
}
v___jp_3066_:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; uint8_t v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; uint8_t v___x_3079_; lean_object* v___x_3080_; 
v___x_3073_ = lean_unsigned_to_nat(1u);
v___x_3074_ = l_Lean_Syntax_getArg(v_stx_3055_, v___x_3073_);
v___x_3075_ = 1;
v___x_3076_ = lean_box(v___x_3075_);
v___x_3077_ = lean_box(v___x_3075_);
v___x_3078_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(v___x_3078_, 0, v___x_3074_);
lean_closure_set(v___x_3078_, 1, v_expectedType_x3f_3056_);
lean_closure_set(v___x_3078_, 2, v___x_3076_);
lean_closure_set(v___x_3078_, 3, v___x_3077_);
v___x_3079_ = 1;
v___x_3080_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_3078_, v___x_3079_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_object* v_a_3081_; lean_object* v___x_3082_; lean_object* v_a_3083_; uint8_t v___x_3084_; lean_object* v___x_3085_; 
v_a_3081_ = lean_ctor_get(v___x_3080_, 0);
lean_inc(v_a_3081_);
lean_dec_ref_known(v___x_3080_, 1);
v___x_3082_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__0___redArg(v_a_3081_, v___y_3070_);
v_a_3083_ = lean_ctor_get(v___x_3082_, 0);
lean_inc_n(v_a_3083_, 2);
lean_dec_ref(v___x_3082_);
v___x_3084_ = 0;
v___x_3085_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1(v_a_3083_, v___f_3065_, v___f_3064_, v___x_3084_, v___x_3084_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_);
if (lean_obj_tag(v___x_3085_) == 0)
{
lean_object* v_a_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3096_; 
v_a_3086_ = lean_ctor_get(v___x_3085_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3088_ = v___x_3085_;
v_isShared_3089_ = v_isSharedCheck_3096_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_a_3086_);
lean_dec(v___x_3085_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3096_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
uint8_t v___x_3090_; 
v___x_3090_ = lean_expr_eqv(v_a_3086_, v_a_3083_);
if (v___x_3090_ == 0)
{
lean_object* v___x_3091_; lean_object* v___x_3092_; 
lean_del_object(v___x_3088_);
lean_dec(v_a_3083_);
v___x_3091_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabContractEPosts___closed__10));
v___x_3092_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith(v___x_3091_, v_a_3086_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_);
return v___x_3092_;
}
else
{
lean_object* v___x_3094_; 
lean_dec(v_a_3086_);
if (v_isShared_3089_ == 0)
{
lean_ctor_set(v___x_3088_, 0, v_a_3083_);
v___x_3094_ = v___x_3088_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_a_3083_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
}
}
else
{
lean_dec(v_a_3083_);
return v___x_3085_;
}
}
else
{
return v___x_3080_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_elabContractEPosts_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_3055_ = stack[0].m_obj;
lean_object* v_expectedType_x3f_3056_ = stack[1].m_obj;
lean_object* v_a_3057_ = stack[2].m_obj;
lean_object* v_a_3058_ = stack[3].m_obj;
lean_object* v_a_3059_ = stack[4].m_obj;
lean_object* v_a_3060_ = stack[5].m_obj;
lean_object* v_a_3061_ = stack[6].m_obj;
lean_object* v_a_3062_ = stack[7].m_obj;
lean_object* v_res_3119_;
v_res_3119_ = l_Lean_Elab_Tactic_Do_elabContractEPosts(v_stx_3055_, v_expectedType_x3f_3056_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_);
stack->m_obj
 = v_res_3119_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractEPosts___boxed(lean_object* v_stx_3120_, lean_object* v_expectedType_x3f_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_){
_start:
{
lean_object* v_res_3129_; 
v_res_3129_ = l_Lean_Elab_Tactic_Do_elabContractEPosts(v_stx_3120_, v_expectedType_x3f_3121_, v_a_3122_, v_a_3123_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_);
lean_dec(v_a_3127_);
lean_dec_ref(v_a_3126_);
lean_dec(v_a_3125_);
lean_dec_ref(v_a_3124_);
lean_dec(v_a_3123_);
lean_dec_ref(v_a_3122_);
lean_dec(v_stx_3120_);
return v_res_3129_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4(lean_object* v_upperBound_3130_, lean_object* v___x_3131_, lean_object* v_pre_3132_, lean_object* v_post_3133_, uint8_t v_usedLetOnly_3134_, uint8_t v_skipConstInApp_3135_, uint8_t v_skipInstances_3136_, lean_object* v___x_3137_, lean_object* v_inst_3138_, lean_object* v_R_3139_, lean_object* v_a_3140_, lean_object* v_b_3141_, lean_object* v_c_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_){
_start:
{
lean_object* v___x_3151_; 
v___x_3151_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___redArg(v_upperBound_3130_, v___x_3131_, v_pre_3132_, v_post_3133_, v_usedLetOnly_3134_, v_skipConstInApp_3135_, v_skipInstances_3136_, v_a_3140_, v_b_3141_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_);
return v___x_3151_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_3130_ = stack[0].m_obj;
lean_object* v___x_3131_ = stack[1].m_obj;
lean_object* v_pre_3132_ = stack[2].m_obj;
lean_object* v_post_3133_ = stack[3].m_obj;
uint8_t v_usedLetOnly_3134_ = stack[4].m_num;
uint8_t v_skipConstInApp_3135_ = stack[5].m_num;
uint8_t v_skipInstances_3136_ = stack[6].m_num;
lean_object* v___x_3137_ = stack[7].m_obj;
lean_object* v_a_3140_ = stack[10].m_obj;
lean_object* v_b_3141_ = stack[11].m_obj;
lean_object* v___y_3143_ = stack[13].m_obj;
lean_object* v___y_3144_ = stack[14].m_obj;
lean_object* v___y_3145_ = stack[15].m_obj;
lean_object* v___y_3146_ = stack[16].m_obj;
lean_object* v___y_3147_ = stack[17].m_obj;
lean_object* v___y_3148_ = stack[18].m_obj;
lean_object* v___y_3149_ = stack[19].m_obj;
lean_object* v_res_3152_;
v_res_3152_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4(v_upperBound_3130_, v___x_3131_, v_pre_3132_, v_post_3133_, v_usedLetOnly_3134_, v_skipConstInApp_3135_, v_skipInstances_3136_, v___x_3137_, lean_box(0), lean_box(0), v_a_3140_, v_b_3141_, lean_box(0), v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_);
stack->m_obj
 = v_res_3152_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_3153_ = _args[0];
lean_object* v___x_3154_ = _args[1];
lean_object* v_pre_3155_ = _args[2];
lean_object* v_post_3156_ = _args[3];
lean_object* v_usedLetOnly_3157_ = _args[4];
lean_object* v_skipConstInApp_3158_ = _args[5];
lean_object* v_skipInstances_3159_ = _args[6];
lean_object* v___x_3160_ = _args[7];
lean_object* v_inst_3161_ = _args[8];
lean_object* v_R_3162_ = _args[9];
lean_object* v_a_3163_ = _args[10];
lean_object* v_b_3164_ = _args[11];
lean_object* v_c_3165_ = _args[12];
lean_object* v___y_3166_ = _args[13];
lean_object* v___y_3167_ = _args[14];
lean_object* v___y_3168_ = _args[15];
lean_object* v___y_3169_ = _args[16];
lean_object* v___y_3170_ = _args[17];
lean_object* v___y_3171_ = _args[18];
lean_object* v___y_3172_ = _args[19];
lean_object* v___y_3173_ = _args[20];
_start:
{
uint8_t v_usedLetOnly_boxed_3174_; uint8_t v_skipConstInApp_boxed_3175_; uint8_t v_skipInstances_boxed_3176_; lean_object* v_res_3177_; 
v_usedLetOnly_boxed_3174_ = lean_unbox(v_usedLetOnly_3157_);
v_skipConstInApp_boxed_3175_ = lean_unbox(v_skipConstInApp_3158_);
v_skipInstances_boxed_3176_ = lean_unbox(v_skipInstances_3159_);
v_res_3177_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__4(v_upperBound_3153_, v___x_3154_, v_pre_3155_, v_post_3156_, v_usedLetOnly_boxed_3174_, v_skipConstInApp_boxed_3175_, v_skipInstances_boxed_3176_, v___x_3160_, v_inst_3161_, v_R_3162_, v_a_3163_, v_b_3164_, v_c_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
lean_dec(v___y_3166_);
lean_dec(v___x_3160_);
lean_dec_ref(v___x_3154_);
lean_dec(v_upperBound_3153_);
return v_res_3177_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5(lean_object* v_00_u03b2_3178_, lean_object* v_m_3179_, lean_object* v_a_3180_){
_start:
{
lean_object* v___x_3181_; 
v___x_3181_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5___redArg(v_m_3179_, v_a_3180_);
return v___x_3181_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5___boxed(lean_object* v_00_u03b2_3182_, lean_object* v_m_3183_, lean_object* v_a_3184_){
_start:
{
lean_object* v_res_3185_; 
v_res_3185_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5(v_00_u03b2_3182_, v_m_3183_, v_a_3184_);
lean_dec_ref(v_a_3184_);
lean_dec_ref(v_m_3183_);
return v_res_3185_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8(lean_object* v_00_u03b1_3186_, lean_object* v_name_3187_, uint8_t v_bi_3188_, lean_object* v_type_3189_, lean_object* v_k_3190_, uint8_t v_kind_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_){
_start:
{
lean_object* v___x_3200_; 
v___x_3200_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___redArg(v_name_3187_, v_bi_3188_, v_type_3189_, v_k_3190_, v_kind_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_);
return v___x_3200_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_3187_ = stack[1].m_obj;
uint8_t v_bi_3188_ = stack[2].m_num;
lean_object* v_type_3189_ = stack[3].m_obj;
lean_object* v_k_3190_ = stack[4].m_obj;
uint8_t v_kind_3191_ = stack[5].m_num;
lean_object* v___y_3192_ = stack[6].m_obj;
lean_object* v___y_3193_ = stack[7].m_obj;
lean_object* v___y_3194_ = stack[8].m_obj;
lean_object* v___y_3195_ = stack[9].m_obj;
lean_object* v___y_3196_ = stack[10].m_obj;
lean_object* v___y_3197_ = stack[11].m_obj;
lean_object* v___y_3198_ = stack[12].m_obj;
lean_object* v_res_3201_;
v_res_3201_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8(lean_box(0), v_name_3187_, v_bi_3188_, v_type_3189_, v_k_3190_, v_kind_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_);
stack->m_obj
 = v_res_3201_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8___boxed(lean_object* v_00_u03b1_3202_, lean_object* v_name_3203_, lean_object* v_bi_3204_, lean_object* v_type_3205_, lean_object* v_k_3206_, lean_object* v_kind_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_){
_start:
{
uint8_t v_bi_boxed_3216_; uint8_t v_kind_boxed_3217_; lean_object* v_res_3218_; 
v_bi_boxed_3216_ = lean_unbox(v_bi_3204_);
v_kind_boxed_3217_ = lean_unbox(v_kind_3207_);
v_res_3218_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__6_spec__8(v_00_u03b1_3202_, v_name_3203_, v_bi_boxed_3216_, v_type_3205_, v_k_3206_, v_kind_boxed_3217_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
lean_dec(v___y_3214_);
lean_dec_ref(v___y_3213_);
lean_dec(v___y_3212_);
lean_dec_ref(v___y_3211_);
lean_dec(v___y_3210_);
lean_dec_ref(v___y_3209_);
lean_dec(v___y_3208_);
return v_res_3218_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11(lean_object* v_00_u03b1_3219_, lean_object* v_name_3220_, lean_object* v_type_3221_, lean_object* v_val_3222_, lean_object* v_k_3223_, uint8_t v_nondep_3224_, uint8_t v_kind_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
lean_object* v___x_3234_; 
v___x_3234_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11___redArg(v_name_3220_, v_type_3221_, v_val_3222_, v_k_3223_, v_nondep_3224_, v_kind_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
return v___x_3234_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_3220_ = stack[1].m_obj;
lean_object* v_type_3221_ = stack[2].m_obj;
lean_object* v_val_3222_ = stack[3].m_obj;
lean_object* v_k_3223_ = stack[4].m_obj;
uint8_t v_nondep_3224_ = stack[5].m_num;
uint8_t v_kind_3225_ = stack[6].m_num;
lean_object* v___y_3226_ = stack[7].m_obj;
lean_object* v___y_3227_ = stack[8].m_obj;
lean_object* v___y_3228_ = stack[9].m_obj;
lean_object* v___y_3229_ = stack[10].m_obj;
lean_object* v___y_3230_ = stack[11].m_obj;
lean_object* v___y_3231_ = stack[12].m_obj;
lean_object* v___y_3232_ = stack[13].m_obj;
lean_object* v_res_3235_;
v_res_3235_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11(lean_box(0), v_name_3220_, v_type_3221_, v_val_3222_, v_k_3223_, v_nondep_3224_, v_kind_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
stack->m_obj
 = v_res_3235_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11___boxed(lean_object* v_00_u03b1_3236_, lean_object* v_name_3237_, lean_object* v_type_3238_, lean_object* v_val_3239_, lean_object* v_k_3240_, lean_object* v_nondep_3241_, lean_object* v_kind_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_){
_start:
{
uint8_t v_nondep_boxed_3251_; uint8_t v_kind_boxed_3252_; lean_object* v_res_3253_; 
v_nondep_boxed_3251_ = lean_unbox(v_nondep_3241_);
v_kind_boxed_3252_ = lean_unbox(v_kind_3242_);
v_res_3253_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__8_spec__11(v_00_u03b1_3236_, v_name_3237_, v_type_3238_, v_val_3239_, v_k_3240_, v_nondep_boxed_3251_, v_kind_boxed_3252_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
return v_res_3253_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14(lean_object* v_00_u03b1_3254_, lean_object* v_ref_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_){
_start:
{
lean_object* v___x_3261_; 
v___x_3261_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_3255_);
return v___x_3261_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3255_ = stack[1].m_obj;
lean_object* v___y_3256_ = stack[2].m_obj;
lean_object* v___y_3257_ = stack[3].m_obj;
lean_object* v___y_3258_ = stack[4].m_obj;
lean_object* v___y_3259_ = stack[5].m_obj;
lean_object* v_res_3262_;
v_res_3262_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14(lean_box(0), v_ref_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_);
stack->m_obj
 = v_res_3262_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14___boxed(lean_object* v_00_u03b1_3263_, lean_object* v_ref_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_){
_start:
{
lean_object* v_res_3270_; 
v_res_3270_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_spec__14(v_00_u03b1_3263_, v_ref_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_);
lean_dec(v___y_3268_);
lean_dec_ref(v___y_3267_);
lean_dec(v___y_3266_);
lean_dec_ref(v___y_3265_);
return v_res_3270_;
}
}
lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10(lean_object* v_00_u03b1_3271_, lean_object* v_x_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_){
_start:
{
lean_object* v___x_3281_; 
v___x_3281_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10___redArg(v_x_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_);
return v___x_3281_;
}
}
LEAN_EXPORT void l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3272_ = stack[1].m_obj;
lean_object* v___y_3273_ = stack[2].m_obj;
lean_object* v___y_3274_ = stack[3].m_obj;
lean_object* v___y_3275_ = stack[4].m_obj;
lean_object* v___y_3276_ = stack[5].m_obj;
lean_object* v___y_3277_ = stack[6].m_obj;
lean_object* v___y_3278_ = stack[7].m_obj;
lean_object* v___y_3279_ = stack[8].m_obj;
lean_object* v_res_3282_;
v_res_3282_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10(lean_box(0), v_x_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_);
stack->m_obj
 = v_res_3282_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10___boxed(lean_object* v_00_u03b1_3283_, lean_object* v_x_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_){
_start:
{
lean_object* v_res_3293_; 
v_res_3293_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__10(v_00_u03b1_3283_, v_x_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_);
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
lean_dec(v___y_3289_);
lean_dec_ref(v___y_3288_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3286_);
lean_dec(v___y_3285_);
return v_res_3293_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11(lean_object* v_00_u03b2_3294_, lean_object* v_m_3295_, lean_object* v_a_3296_, lean_object* v_b_3297_){
_start:
{
lean_object* v___x_3298_; 
v___x_3298_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11___redArg(v_m_3295_, v_a_3296_, v_b_3297_);
return v___x_3298_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5_spec__6(lean_object* v_00_u03b2_3299_, lean_object* v_a_3300_, lean_object* v_x_3301_){
_start:
{
lean_object* v___x_3302_; 
v___x_3302_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5_spec__6___redArg(v_a_3300_, v_x_3301_);
return v___x_3302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5_spec__6___boxed(lean_object* v_00_u03b2_3303_, lean_object* v_a_3304_, lean_object* v_x_3305_){
_start:
{
lean_object* v_res_3306_; 
v_res_3306_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__5_spec__6(v_00_u03b2_3303_, v_a_3304_, v_x_3305_);
lean_dec(v_x_3305_);
lean_dec_ref(v_a_3304_);
return v_res_3306_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16(lean_object* v_00_u03b2_3307_, lean_object* v_a_3308_, lean_object* v_x_3309_){
_start:
{
uint8_t v___x_3310_; 
v___x_3310_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16___redArg(v_a_3308_, v_x_3309_);
return v___x_3310_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3308_ = stack[1].m_obj;
lean_object* v_x_3309_ = stack[2].m_obj;
uint8_t v_res_3311_;
v_res_3311_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16(lean_box(0), v_a_3308_, v_x_3309_);
stack->m_num = v_res_3311_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16___boxed(lean_object* v_00_u03b2_3312_, lean_object* v_a_3313_, lean_object* v_x_3314_){
_start:
{
uint8_t v_res_3315_; lean_object* v_r_3316_; 
v_res_3315_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__16(v_00_u03b2_3312_, v_a_3313_, v_x_3314_);
lean_dec(v_x_3314_);
lean_dec_ref(v_a_3313_);
v_r_3316_ = lean_box(v_res_3315_);
return v_r_3316_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17(lean_object* v_00_u03b2_3317_, lean_object* v_data_3318_){
_start:
{
lean_object* v___x_3319_; 
v___x_3319_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17___redArg(v_data_3318_);
return v___x_3319_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__18(lean_object* v_00_u03b2_3320_, lean_object* v_a_3321_, lean_object* v_b_3322_, lean_object* v_x_3323_){
_start:
{
lean_object* v___x_3324_; 
v___x_3324_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__18___redArg(v_a_3321_, v_b_3322_, v_x_3323_);
return v___x_3324_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17_spec__18(lean_object* v_00_u03b2_3325_, lean_object* v_i_3326_, lean_object* v_source_3327_, lean_object* v_target_3328_){
_start:
{
lean_object* v___x_3329_; 
v___x_3329_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v_i_3326_, v_source_3327_, v_target_3328_);
return v___x_3329_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19(lean_object* v_00_u03b2_3330_, lean_object* v_x_3331_, lean_object* v_x_3332_){
_start:
{
lean_object* v___x_3333_; 
v___x_3333_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elabContractEPosts_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_x_3331_, v_x_3332_);
return v___x_3333_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1(){
_start:
{
lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3347_ = l_Lean_Elab_Term_termElabAttribute;
v___x_3348_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___closed__0));
v___x_3349_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___closed__2));
v___x_3350_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elabContractEPosts___boxed), 9, 0);
v___x_3351_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3347_, v___x_3348_, v___x_3349_, v___x_3350_);
return v___x_3351_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3352_;
v_res_3352_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1();
stack->m_obj
 = v_res_3352_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___boxed(lean_object* v_a_3353_){
_start:
{
lean_object* v_res_3354_; 
v_res_3354_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1();
return v_res_3354_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts_docString__3(){
_start:
{
lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; 
v___x_3357_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts__1___closed__2));
v___x_3358_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts_docString__3___closed__0));
v___x_3359_ = l_Lean_addBuiltinDocString(v___x_3357_, v___x_3358_);
return v___x_3359_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts_docString__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3360_;
v_res_3360_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts_docString__3();
stack->m_obj
 = v_res_3360_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts_docString__3___boxed(lean_object* v_a_3361_){
_start:
{
lean_object* v_res_3362_; 
v_res_3362_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractEPosts___regBuiltin_Lean_Elab_Tactic_Do_elabContractEPosts_docString__3();
return v_res_3362_;
}
}
uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0(uint8_t v_suppressElabErrors_3364_, uint8_t v___y_3365_, lean_object* v_x_3366_){
_start:
{
if (lean_obj_tag(v_x_3366_) == 1)
{
lean_object* v_pre_3367_; 
v_pre_3367_ = lean_ctor_get(v_x_3366_, 0);
if (lean_obj_tag(v_pre_3367_) == 0)
{
lean_object* v_str_3368_; lean_object* v___x_3369_; uint8_t v___x_3370_; 
v_str_3368_ = lean_ctor_get(v_x_3366_, 1);
v___x_3369_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0___closed__0));
v___x_3370_ = lean_string_dec_eq(v_str_3368_, v___x_3369_);
if (v___x_3370_ == 0)
{
return v___x_3370_;
}
else
{
return v_suppressElabErrors_3364_;
}
}
else
{
return v___y_3365_;
}
}
else
{
return v___y_3365_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_3364_ = stack[0].m_num;
uint8_t v___y_3365_ = stack[1].m_num;
lean_object* v_x_3366_ = stack[2].m_obj;
uint8_t v_res_3371_;
v_res_3371_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0(v_suppressElabErrors_3364_, v___y_3365_, v_x_3366_);
stack->m_num = v_res_3371_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0___boxed(lean_object* v_suppressElabErrors_3372_, lean_object* v___y_3373_, lean_object* v_x_3374_){
_start:
{
uint8_t v_suppressElabErrors_boxed_3375_; uint8_t v___y_3548__boxed_3376_; uint8_t v_res_3377_; lean_object* v_r_3378_; 
v_suppressElabErrors_boxed_3375_ = lean_unbox(v_suppressElabErrors_3372_);
v___y_3548__boxed_3376_ = lean_unbox(v___y_3373_);
v_res_3377_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0(v_suppressElabErrors_boxed_3375_, v___y_3548__boxed_3376_, v_x_3374_);
lean_dec(v_x_3374_);
v_r_3378_ = lean_box(v_res_3377_);
return v_r_3378_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0(lean_object* v_opts_3379_, lean_object* v_opt_3380_){
_start:
{
lean_object* v_name_3381_; lean_object* v_defValue_3382_; lean_object* v_map_3383_; lean_object* v___x_3384_; 
v_name_3381_ = lean_ctor_get(v_opt_3380_, 0);
v_defValue_3382_ = lean_ctor_get(v_opt_3380_, 1);
v_map_3383_ = lean_ctor_get(v_opts_3379_, 0);
v___x_3384_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3383_, v_name_3381_);
if (lean_obj_tag(v___x_3384_) == 0)
{
uint8_t v___x_3385_; 
v___x_3385_ = lean_unbox(v_defValue_3382_);
return v___x_3385_;
}
else
{
lean_object* v_val_3386_; 
v_val_3386_ = lean_ctor_get(v___x_3384_, 0);
lean_inc(v_val_3386_);
lean_dec_ref_known(v___x_3384_, 1);
if (lean_obj_tag(v_val_3386_) == 1)
{
uint8_t v_v_3387_; 
v_v_3387_ = lean_ctor_get_uint8(v_val_3386_, 0);
lean_dec_ref_known(v_val_3386_, 0);
return v_v_3387_;
}
else
{
uint8_t v___x_3388_; 
lean_dec(v_val_3386_);
v___x_3388_ = lean_unbox(v_defValue_3382_);
return v___x_3388_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_3379_ = stack[0].m_obj;
lean_object* v_opt_3380_ = stack[1].m_obj;
uint8_t v_res_3389_;
v_res_3389_ = l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0(v_opts_3379_, v_opt_3380_);
stack->m_num = v_res_3389_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0___boxed(lean_object* v_opts_3390_, lean_object* v_opt_3391_){
_start:
{
uint8_t v_res_3392_; lean_object* v_r_3393_; 
v_res_3392_ = l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0(v_opts_3390_, v_opt_3391_);
lean_dec_ref(v_opt_3391_);
lean_dec_ref(v_opts_3390_);
v_r_3393_ = lean_box(v_res_3392_);
return v_r_3393_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_3394_; lean_object* v___x_3395_; 
v___x_3394_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_simpOnlyWith_spec__0___redArg___closed__0);
v___x_3395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3395_, 0, v___x_3394_);
return v___x_3395_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3396_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_3397_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__0);
v___x_3398_ = lean_unsigned_to_nat(0u);
v___x_3399_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3398_);
lean_ctor_set(v___x_3399_, 1, v___x_3398_);
lean_ctor_set(v___x_3399_, 2, v___x_3398_);
lean_ctor_set(v___x_3399_, 3, v___x_3398_);
lean_ctor_set(v___x_3399_, 4, v___x_3397_);
lean_ctor_set(v___x_3399_, 5, v___x_3397_);
lean_ctor_set(v___x_3399_, 6, v___x_3397_);
lean_ctor_set(v___x_3399_, 7, v___x_3397_);
lean_ctor_set(v___x_3399_, 8, v___x_3397_);
lean_ctor_set(v___x_3399_, 9, v___x_3397_);
lean_ctor_set(v___x_3399_, 10, v___x_3397_);
lean_ctor_set(v___x_3399_, 11, v___x_3396_);
return v___x_3399_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3400_ = lean_unsigned_to_nat(32u);
v___x_3401_ = lean_mk_empty_array_with_capacity(v___x_3400_);
v___x_3402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3401_);
return v___x_3402_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__3(void){
_start:
{
size_t v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; 
v___x_3403_ = ((size_t)5ULL);
v___x_3404_ = lean_unsigned_to_nat(0u);
v___x_3405_ = lean_unsigned_to_nat(32u);
v___x_3406_ = lean_mk_empty_array_with_capacity(v___x_3405_);
v___x_3407_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__2);
v___x_3408_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3408_, 0, v___x_3407_);
lean_ctor_set(v___x_3408_, 1, v___x_3406_);
lean_ctor_set(v___x_3408_, 2, v___x_3404_);
lean_ctor_set(v___x_3408_, 3, v___x_3404_);
lean_ctor_set_usize(v___x_3408_, 4, v___x_3403_);
return v___x_3408_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__4(void){
_start:
{
lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; 
v___x_3409_ = lean_box(1);
v___x_3410_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__3);
v___x_3411_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__0);
v___x_3412_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3412_, 0, v___x_3411_);
lean_ctor_set(v___x_3412_, 1, v___x_3410_);
lean_ctor_set(v___x_3412_, 2, v___x_3409_);
return v___x_3412_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_msgData_3413_, lean_object* v___y_3414_){
_start:
{
lean_object* v___x_3416_; lean_object* v_env_3417_; uint8_t v___x_3418_; lean_object* v_env_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v_scopes_3422_; lean_object* v___x_3423_; lean_object* v_opts_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3416_ = lean_st_ref_get(v___y_3414_);
v_env_3417_ = lean_ctor_get(v___x_3416_, 0);
lean_inc_ref(v_env_3417_);
lean_dec(v___x_3416_);
v___x_3418_ = 0;
v_env_3419_ = l_Lean_Environment_setRecordingDeps(v_env_3417_, v___x_3418_);
v___x_3420_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3421_ = lean_st_ref_get(v___y_3414_);
v_scopes_3422_ = lean_ctor_get(v___x_3421_, 2);
lean_inc(v_scopes_3422_);
lean_dec(v___x_3421_);
v___x_3423_ = l_List_head_x21___redArg(v___x_3420_, v_scopes_3422_);
lean_dec(v_scopes_3422_);
v_opts_3424_ = lean_ctor_get(v___x_3423_, 1);
lean_inc_ref(v_opts_3424_);
lean_dec(v___x_3423_);
v___x_3425_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__1);
v___x_3426_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___closed__4);
v___x_3427_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3427_, 0, v_env_3419_);
lean_ctor_set(v___x_3427_, 1, v___x_3425_);
lean_ctor_set(v___x_3427_, 2, v___x_3426_);
lean_ctor_set(v___x_3427_, 3, v_opts_3424_);
v___x_3428_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3428_, 0, v___x_3427_);
lean_ctor_set(v___x_3428_, 1, v_msgData_3413_);
v___x_3429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3428_);
return v___x_3429_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_3413_ = stack[0].m_obj;
lean_object* v___y_3414_ = stack[1].m_obj;
lean_object* v_res_3430_;
v_res_3430_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg(v_msgData_3413_, v___y_3414_);
stack->m_obj
 = v_res_3430_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_msgData_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_){
_start:
{
lean_object* v_res_3434_; 
v_res_3434_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg(v_msgData_3431_, v___y_3432_);
lean_dec(v___y_3432_);
return v_res_3434_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2(lean_object* v_ref_3435_, lean_object* v_msgData_3436_, uint8_t v_severity_3437_, uint8_t v_isSilent_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_){
_start:
{
lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; uint8_t v___y_3447_; lean_object* v___y_3448_; uint8_t v___y_3449_; lean_object* v___y_3450_; uint8_t v___y_3508_; lean_object* v___y_3509_; uint8_t v___y_3510_; uint8_t v___y_3511_; lean_object* v___y_3512_; uint8_t v___y_3536_; lean_object* v___y_3537_; uint8_t v___y_3538_; uint8_t v___y_3539_; lean_object* v___y_3540_; uint8_t v___y_3544_; uint8_t v___y_3545_; uint8_t v___y_3546_; uint8_t v___x_3561_; uint8_t v___y_3563_; uint8_t v___y_3564_; uint8_t v___y_3565_; uint8_t v___y_3567_; uint8_t v___x_3579_; 
v___x_3561_ = 2;
v___x_3579_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3437_, v___x_3561_);
if (v___x_3579_ == 0)
{
v___y_3567_ = v___x_3579_;
goto v___jp_3566_;
}
else
{
uint8_t v___x_3580_; 
lean_inc_ref(v_msgData_3436_);
v___x_3580_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3436_);
v___y_3567_ = v___x_3580_;
goto v___jp_3566_;
}
v___jp_3442_:
{
lean_object* v___x_3451_; 
v___x_3451_ = l_Lean_Elab_Command_getScope___redArg(v___y_3450_);
if (lean_obj_tag(v___x_3451_) == 0)
{
lean_object* v_a_3452_; lean_object* v_currNamespace_3453_; lean_object* v___x_3454_; 
v_a_3452_ = lean_ctor_get(v___x_3451_, 0);
lean_inc(v_a_3452_);
lean_dec_ref_known(v___x_3451_, 1);
v_currNamespace_3453_ = lean_ctor_get(v_a_3452_, 2);
lean_inc(v_currNamespace_3453_);
lean_dec(v_a_3452_);
v___x_3454_ = l_Lean_Elab_Command_getScope___redArg(v___y_3450_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v_a_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3490_; 
v_a_3455_ = lean_ctor_get(v___x_3454_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3457_ = v___x_3454_;
v_isShared_3458_ = v_isSharedCheck_3490_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_a_3455_);
lean_dec(v___x_3454_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3490_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v_openDecls_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v_env_3464_; lean_object* v_messages_3465_; lean_object* v_scopes_3466_; lean_object* v_usedQuotCtxts_3467_; lean_object* v_nextMacroScope_3468_; lean_object* v_maxRecDepth_3469_; lean_object* v_ngen_3470_; lean_object* v_auxDeclNGen_3471_; lean_object* v_infoState_3472_; lean_object* v_traceState_3473_; lean_object* v_snapshotTasks_3474_; lean_object* v_prevLinterStates_3475_; lean_object* v_codeQualityEntryTasks_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3489_; 
v_openDecls_3459_ = lean_ctor_get(v_a_3455_, 3);
lean_inc(v_openDecls_3459_);
lean_dec(v_a_3455_);
v___x_3460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3460_, 0, v_currNamespace_3453_);
lean_ctor_set(v___x_3460_, 1, v_openDecls_3459_);
v___x_3461_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3461_, 0, v___x_3460_);
lean_ctor_set(v___x_3461_, 1, v___y_3446_);
lean_inc_ref(v___y_3443_);
lean_inc_ref(v___y_3444_);
v___x_3462_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3462_, 0, v___y_3444_);
lean_ctor_set(v___x_3462_, 1, v___y_3445_);
lean_ctor_set(v___x_3462_, 2, v___y_3448_);
lean_ctor_set(v___x_3462_, 3, v___y_3443_);
lean_ctor_set(v___x_3462_, 4, v___x_3461_);
lean_ctor_set_uint8(v___x_3462_, sizeof(void*)*5, v___y_3449_);
lean_ctor_set_uint8(v___x_3462_, sizeof(void*)*5 + 1, v___y_3447_);
lean_ctor_set_uint8(v___x_3462_, sizeof(void*)*5 + 2, v_isSilent_3438_);
v___x_3463_ = lean_st_ref_take(v___y_3450_);
v_env_3464_ = lean_ctor_get(v___x_3463_, 0);
v_messages_3465_ = lean_ctor_get(v___x_3463_, 1);
v_scopes_3466_ = lean_ctor_get(v___x_3463_, 2);
v_usedQuotCtxts_3467_ = lean_ctor_get(v___x_3463_, 3);
v_nextMacroScope_3468_ = lean_ctor_get(v___x_3463_, 4);
v_maxRecDepth_3469_ = lean_ctor_get(v___x_3463_, 5);
v_ngen_3470_ = lean_ctor_get(v___x_3463_, 6);
v_auxDeclNGen_3471_ = lean_ctor_get(v___x_3463_, 7);
v_infoState_3472_ = lean_ctor_get(v___x_3463_, 8);
v_traceState_3473_ = lean_ctor_get(v___x_3463_, 9);
v_snapshotTasks_3474_ = lean_ctor_get(v___x_3463_, 10);
v_prevLinterStates_3475_ = lean_ctor_get(v___x_3463_, 11);
v_codeQualityEntryTasks_3476_ = lean_ctor_get(v___x_3463_, 12);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3478_ = v___x_3463_;
v_isShared_3479_ = v_isSharedCheck_3489_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3476_);
lean_inc(v_prevLinterStates_3475_);
lean_inc(v_snapshotTasks_3474_);
lean_inc(v_traceState_3473_);
lean_inc(v_infoState_3472_);
lean_inc(v_auxDeclNGen_3471_);
lean_inc(v_ngen_3470_);
lean_inc(v_maxRecDepth_3469_);
lean_inc(v_nextMacroScope_3468_);
lean_inc(v_usedQuotCtxts_3467_);
lean_inc(v_scopes_3466_);
lean_inc(v_messages_3465_);
lean_inc(v_env_3464_);
lean_dec(v___x_3463_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3489_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3483_; 
v___x_3480_ = lean_box(0);
v___x_3481_ = l_Lean_MessageLog_add(v___x_3462_, v_messages_3465_);
if (v_isShared_3479_ == 0)
{
lean_ctor_set(v___x_3478_, 1, v___x_3481_);
v___x_3483_ = v___x_3478_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v_env_3464_);
lean_ctor_set(v_reuseFailAlloc_3488_, 1, v___x_3481_);
lean_ctor_set(v_reuseFailAlloc_3488_, 2, v_scopes_3466_);
lean_ctor_set(v_reuseFailAlloc_3488_, 3, v_usedQuotCtxts_3467_);
lean_ctor_set(v_reuseFailAlloc_3488_, 4, v_nextMacroScope_3468_);
lean_ctor_set(v_reuseFailAlloc_3488_, 5, v_maxRecDepth_3469_);
lean_ctor_set(v_reuseFailAlloc_3488_, 6, v_ngen_3470_);
lean_ctor_set(v_reuseFailAlloc_3488_, 7, v_auxDeclNGen_3471_);
lean_ctor_set(v_reuseFailAlloc_3488_, 8, v_infoState_3472_);
lean_ctor_set(v_reuseFailAlloc_3488_, 9, v_traceState_3473_);
lean_ctor_set(v_reuseFailAlloc_3488_, 10, v_snapshotTasks_3474_);
lean_ctor_set(v_reuseFailAlloc_3488_, 11, v_prevLinterStates_3475_);
lean_ctor_set(v_reuseFailAlloc_3488_, 12, v_codeQualityEntryTasks_3476_);
v___x_3483_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
lean_object* v___x_3484_; lean_object* v___x_3486_; 
v___x_3484_ = lean_st_ref_put(v___y_3450_, v___x_3483_);
if (v_isShared_3458_ == 0)
{
lean_ctor_set(v___x_3457_, 0, v___x_3480_);
v___x_3486_ = v___x_3457_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v___x_3480_);
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
}
else
{
lean_object* v_a_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3498_; 
lean_dec(v_currNamespace_3453_);
lean_dec(v___y_3448_);
lean_dec_ref(v___y_3446_);
lean_dec_ref(v___y_3445_);
v_a_3491_ = lean_ctor_get(v___x_3454_, 0);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3493_ = v___x_3454_;
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_a_3491_);
lean_dec(v___x_3454_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3496_; 
if (v_isShared_3494_ == 0)
{
v___x_3496_ = v___x_3493_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v_a_3491_);
v___x_3496_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
return v___x_3496_;
}
}
}
}
else
{
lean_object* v_a_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3506_; 
lean_dec(v___y_3448_);
lean_dec_ref(v___y_3446_);
lean_dec_ref(v___y_3445_);
v_a_3499_ = lean_ctor_get(v___x_3451_, 0);
v_isSharedCheck_3506_ = !lean_is_exclusive(v___x_3451_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3501_ = v___x_3451_;
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_a_3499_);
lean_dec(v___x_3451_);
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
v___jp_3507_:
{
lean_object* v_fileName_3513_; lean_object* v_fileMap_3514_; uint8_t v_suppressElabErrors_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___f_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v_a_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3534_; 
v_fileName_3513_ = lean_ctor_get(v___y_3439_, 0);
v_fileMap_3514_ = lean_ctor_get(v___y_3439_, 1);
v_suppressElabErrors_3515_ = lean_ctor_get_uint8(v___y_3439_, sizeof(void*)*10);
v___x_3516_ = lean_box(v_suppressElabErrors_3515_);
v___x_3517_ = lean_box(v___y_3508_);
v___f_3518_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3518_, 0, v___x_3516_);
lean_closure_set(v___f_3518_, 1, v___x_3517_);
v___x_3519_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3436_);
v___x_3520_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg(v___x_3519_, v___y_3440_);
v_a_3521_ = lean_ctor_get(v___x_3520_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v___x_3520_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3523_ = v___x_3520_;
v_isShared_3524_ = v_isSharedCheck_3534_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_a_3521_);
lean_dec(v___x_3520_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3534_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; 
lean_inc_ref_n(v_fileMap_3514_, 2);
v___x_3525_ = l_Lean_FileMap_toPosition(v_fileMap_3514_, v___y_3509_);
lean_dec(v___y_3509_);
v___x_3526_ = l_Lean_FileMap_toPosition(v_fileMap_3514_, v___y_3512_);
lean_dec(v___y_3512_);
v___x_3527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3527_, 0, v___x_3526_);
v___x_3528_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__19));
if (v_suppressElabErrors_3515_ == 0)
{
lean_del_object(v___x_3523_);
lean_dec_ref(v___f_3518_);
v___y_3443_ = v___x_3528_;
v___y_3444_ = v_fileName_3513_;
v___y_3445_ = v___x_3525_;
v___y_3446_ = v_a_3521_;
v___y_3447_ = v___y_3510_;
v___y_3448_ = v___x_3527_;
v___y_3449_ = v___y_3511_;
v___y_3450_ = v___y_3440_;
goto v___jp_3442_;
}
else
{
uint8_t v___x_3529_; 
lean_inc(v_a_3521_);
v___x_3529_ = l_Lean_MessageData_hasTag(v___f_3518_, v_a_3521_);
if (v___x_3529_ == 0)
{
lean_object* v___x_3530_; lean_object* v___x_3532_; 
lean_dec_ref_known(v___x_3527_, 1);
lean_dec_ref(v___x_3525_);
lean_dec(v_a_3521_);
v___x_3530_ = lean_box(0);
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 0, v___x_3530_);
v___x_3532_ = v___x_3523_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v___x_3530_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
return v___x_3532_;
}
}
else
{
lean_del_object(v___x_3523_);
v___y_3443_ = v___x_3528_;
v___y_3444_ = v_fileName_3513_;
v___y_3445_ = v___x_3525_;
v___y_3446_ = v_a_3521_;
v___y_3447_ = v___y_3510_;
v___y_3448_ = v___x_3527_;
v___y_3449_ = v___y_3511_;
v___y_3450_ = v___y_3440_;
goto v___jp_3442_;
}
}
}
}
v___jp_3535_:
{
lean_object* v___x_3541_; 
v___x_3541_ = l_Lean_Syntax_getTailPos_x3f(v___y_3537_, v___y_3539_);
lean_dec(v___y_3537_);
if (lean_obj_tag(v___x_3541_) == 0)
{
lean_inc(v___y_3540_);
v___y_3508_ = v___y_3536_;
v___y_3509_ = v___y_3540_;
v___y_3510_ = v___y_3538_;
v___y_3511_ = v___y_3539_;
v___y_3512_ = v___y_3540_;
goto v___jp_3507_;
}
else
{
lean_object* v_val_3542_; 
v_val_3542_ = lean_ctor_get(v___x_3541_, 0);
lean_inc(v_val_3542_);
lean_dec_ref_known(v___x_3541_, 1);
v___y_3508_ = v___y_3536_;
v___y_3509_ = v___y_3540_;
v___y_3510_ = v___y_3538_;
v___y_3511_ = v___y_3539_;
v___y_3512_ = v_val_3542_;
goto v___jp_3507_;
}
}
v___jp_3543_:
{
lean_object* v___x_3547_; 
v___x_3547_ = l_Lean_Elab_Command_getRef___redArg(v___y_3439_);
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_object* v_a_3548_; lean_object* v_ref_3549_; lean_object* v___x_3550_; 
v_a_3548_ = lean_ctor_get(v___x_3547_, 0);
lean_inc(v_a_3548_);
lean_dec_ref_known(v___x_3547_, 1);
v_ref_3549_ = l_Lean_replaceRef(v_ref_3435_, v_a_3548_);
lean_dec(v_a_3548_);
v___x_3550_ = l_Lean_Syntax_getPos_x3f(v_ref_3549_, v___y_3545_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v___x_3551_; 
v___x_3551_ = lean_unsigned_to_nat(0u);
v___y_3536_ = v___y_3544_;
v___y_3537_ = v_ref_3549_;
v___y_3538_ = v___y_3546_;
v___y_3539_ = v___y_3545_;
v___y_3540_ = v___x_3551_;
goto v___jp_3535_;
}
else
{
lean_object* v_val_3552_; 
v_val_3552_ = lean_ctor_get(v___x_3550_, 0);
lean_inc(v_val_3552_);
lean_dec_ref_known(v___x_3550_, 1);
v___y_3536_ = v___y_3544_;
v___y_3537_ = v_ref_3549_;
v___y_3538_ = v___y_3546_;
v___y_3539_ = v___y_3545_;
v___y_3540_ = v_val_3552_;
goto v___jp_3535_;
}
}
else
{
lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3560_; 
lean_dec_ref(v_msgData_3436_);
v_a_3553_ = lean_ctor_get(v___x_3547_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3547_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3555_ = v___x_3547_;
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v___x_3547_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3558_; 
if (v_isShared_3556_ == 0)
{
v___x_3558_ = v___x_3555_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_a_3553_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
}
}
v___jp_3562_:
{
if (v___y_3565_ == 0)
{
v___y_3544_ = v___y_3563_;
v___y_3545_ = v___y_3564_;
v___y_3546_ = v_severity_3437_;
goto v___jp_3543_;
}
else
{
v___y_3544_ = v___y_3563_;
v___y_3545_ = v___y_3564_;
v___y_3546_ = v___x_3561_;
goto v___jp_3543_;
}
}
v___jp_3566_:
{
if (v___y_3567_ == 0)
{
lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v_scopes_3570_; lean_object* v___x_3571_; lean_object* v_opts_3572_; uint8_t v___x_3573_; uint8_t v___x_3574_; 
v___x_3568_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3569_ = lean_st_ref_get(v___y_3440_);
v_scopes_3570_ = lean_ctor_get(v___x_3569_, 2);
lean_inc(v_scopes_3570_);
lean_dec(v___x_3569_);
v___x_3571_ = l_List_head_x21___redArg(v___x_3568_, v_scopes_3570_);
lean_dec(v_scopes_3570_);
v_opts_3572_ = lean_ctor_get(v___x_3571_, 1);
lean_inc_ref(v_opts_3572_);
lean_dec(v___x_3571_);
v___x_3573_ = 1;
v___x_3574_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3437_, v___x_3573_);
if (v___x_3574_ == 0)
{
lean_dec_ref(v_opts_3572_);
v___y_3563_ = v___y_3567_;
v___y_3564_ = v___y_3567_;
v___y_3565_ = v___x_3574_;
goto v___jp_3562_;
}
else
{
lean_object* v___x_3575_; uint8_t v___x_3576_; 
v___x_3575_ = l_Lean_warningAsError;
v___x_3576_ = l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0(v_opts_3572_, v___x_3575_);
lean_dec_ref(v_opts_3572_);
v___y_3563_ = v___y_3567_;
v___y_3564_ = v___y_3567_;
v___y_3565_ = v___x_3576_;
goto v___jp_3562_;
}
}
else
{
lean_object* v___x_3577_; lean_object* v___x_3578_; 
lean_dec_ref(v_msgData_3436_);
v___x_3577_ = lean_box(0);
v___x_3578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3577_);
return v___x_3578_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3435_ = stack[0].m_obj;
lean_object* v_msgData_3436_ = stack[1].m_obj;
uint8_t v_severity_3437_ = stack[2].m_num;
uint8_t v_isSilent_3438_ = stack[3].m_num;
lean_object* v___y_3439_ = stack[4].m_obj;
lean_object* v___y_3440_ = stack[5].m_obj;
lean_object* v_res_3581_;
v_res_3581_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2(v_ref_3435_, v_msgData_3436_, v_severity_3437_, v_isSilent_3438_, v___y_3439_, v___y_3440_);
stack->m_obj
 = v_res_3581_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___boxed(lean_object* v_ref_3582_, lean_object* v_msgData_3583_, lean_object* v_severity_3584_, lean_object* v_isSilent_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_){
_start:
{
uint8_t v_severity_boxed_3589_; uint8_t v_isSilent_boxed_3590_; lean_object* v_res_3591_; 
v_severity_boxed_3589_ = lean_unbox(v_severity_3584_);
v_isSilent_boxed_3590_ = lean_unbox(v_isSilent_3585_);
v_res_3591_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2(v_ref_3582_, v_msgData_3583_, v_severity_boxed_3589_, v_isSilent_boxed_3590_, v___y_3586_, v___y_3587_);
lean_dec(v___y_3587_);
lean_dec_ref(v___y_3586_);
lean_dec(v_ref_3582_);
return v_res_3591_;
}
}
lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1(lean_object* v_ref_3592_, lean_object* v_msgData_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_){
_start:
{
uint8_t v___x_3597_; uint8_t v___x_3598_; lean_object* v___x_3599_; 
v___x_3597_ = 1;
v___x_3598_ = 0;
v___x_3599_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2(v_ref_3592_, v_msgData_3593_, v___x_3597_, v___x_3598_, v___y_3594_, v___y_3595_);
return v___x_3599_;
}
}
LEAN_EXPORT void l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3592_ = stack[0].m_obj;
lean_object* v_msgData_3593_ = stack[1].m_obj;
lean_object* v___y_3594_ = stack[2].m_obj;
lean_object* v___y_3595_ = stack[3].m_obj;
lean_object* v_res_3600_;
v_res_3600_ = l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1(v_ref_3592_, v_msgData_3593_, v___y_3594_, v___y_3595_);
stack->m_obj
 = v_res_3600_;
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1___boxed(lean_object* v_ref_3601_, lean_object* v_msgData_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_){
_start:
{
lean_object* v_res_3606_; 
v_res_3606_ = l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1(v_ref_3601_, v_msgData_3602_, v___y_3603_, v___y_3604_);
lean_dec(v___y_3604_);
lean_dec_ref(v___y_3603_);
lean_dec(v_ref_3601_);
return v_res_3606_;
}
}
static lean_object* _init_l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3608_; lean_object* v___x_3609_; 
v___x_3608_ = ((lean_object*)(l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__0));
v___x_3609_ = l_Lean_stringToMessageData(v___x_3608_);
return v___x_3609_;
}
}
static lean_object* _init_l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3611_; lean_object* v___x_3612_; 
v___x_3611_ = ((lean_object*)(l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__2));
v___x_3612_ = l_Lean_stringToMessageData(v___x_3611_);
return v___x_3612_;
}
}
lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0(lean_object* v_kw_3613_, lean_object* v_what_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_){
_start:
{
lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v_scopes_3620_; lean_object* v___x_3621_; lean_object* v_opts_3622_; lean_object* v___x_3623_; uint8_t v___x_3624_; 
v___x_3618_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3619_ = lean_st_ref_get(v___y_3616_);
v_scopes_3620_ = lean_ctor_get(v___x_3619_, 2);
lean_inc(v_scopes_3620_);
lean_dec(v___x_3619_);
v___x_3621_ = l_List_head_x21___redArg(v___x_3618_, v_scopes_3620_);
lean_dec(v_scopes_3620_);
v_opts_3622_ = lean_ctor_get(v___x_3621_, 1);
lean_inc_ref(v_opts_3622_);
lean_dec(v___x_3621_);
v___x_3623_ = l_Lean_Elab_Do_experimental_intrinsic;
v___x_3624_ = l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0(v_opts_3622_, v___x_3623_);
lean_dec_ref(v_opts_3622_);
if (v___x_3624_ == 0)
{
lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; 
v___x_3625_ = lean_obj_once(&l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1, &l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1_once, _init_l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1);
v___x_3626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3626_, 0, v___x_3625_);
lean_ctor_set(v___x_3626_, 1, v_what_3614_);
v___x_3627_ = lean_obj_once(&l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3, &l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3_once, _init_l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3);
v___x_3628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3628_, 0, v___x_3626_);
lean_ctor_set(v___x_3628_, 1, v___x_3627_);
v___x_3629_ = l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1(v_kw_3613_, v___x_3628_, v___y_3615_, v___y_3616_);
return v___x_3629_;
}
else
{
lean_object* v___x_3630_; lean_object* v___x_3631_; 
lean_dec_ref(v_what_3614_);
v___x_3630_ = lean_box(0);
v___x_3631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3631_, 0, v___x_3630_);
return v___x_3631_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_kw_3613_ = stack[0].m_obj;
lean_object* v_what_3614_ = stack[1].m_obj;
lean_object* v___y_3615_ = stack[2].m_obj;
lean_object* v___y_3616_ = stack[3].m_obj;
lean_object* v_res_3632_;
v_res_3632_ = l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0(v_kw_3613_, v_what_3614_, v___y_3615_, v___y_3616_);
stack->m_obj
 = v_res_3632_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___boxed(lean_object* v_kw_3633_, lean_object* v_what_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_){
_start:
{
lean_object* v_res_3638_; 
v_res_3638_ = l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0(v_kw_3633_, v_what_3634_, v___y_3635_, v___y_3636_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec(v_kw_3633_);
return v_res_3638_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3640_; lean_object* v___x_3641_; 
v___x_3640_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__0));
v___x_3641_ = l_Lean_stringToMessageData(v___x_3640_);
return v___x_3641_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__3(void){
_start:
{
lean_object* v___x_3643_; lean_object* v___x_3644_; 
v___x_3643_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__2));
v___x_3644_ = l_Lean_stringToMessageData(v___x_3643_);
return v___x_3644_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1(lean_object* v_as_3645_, size_t v_sz_3646_, size_t v_i_3647_, lean_object* v_b_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_){
_start:
{
uint8_t v___x_3652_; 
v___x_3652_ = lean_usize_dec_lt(v_i_3647_, v_sz_3646_);
if (v___x_3652_ == 0)
{
lean_object* v___x_3653_; 
v___x_3653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3653_, 0, v_b_3648_);
return v___x_3653_;
}
else
{
lean_object* v___x_3654_; lean_object* v_a_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3654_ = lean_box(0);
v_a_3655_ = lean_array_uget_borrowed(v_as_3645_, v_i_3647_);
v___x_3656_ = lean_unsigned_to_nat(0u);
v___x_3657_ = l_Lean_Syntax_getArg(v_a_3655_, v___x_3656_);
v___x_3658_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__1);
v___x_3659_ = l_Lean_Syntax_getAtomVal(v___x_3657_);
v___x_3660_ = l_Lean_stringToMessageData(v___x_3659_);
v___x_3661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3661_, 0, v___x_3658_);
lean_ctor_set(v___x_3661_, 1, v___x_3660_);
v___x_3662_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___closed__3);
v___x_3663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3663_, 0, v___x_3661_);
lean_ctor_set(v___x_3663_, 1, v___x_3662_);
v___x_3664_ = l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0(v___x_3657_, v___x_3663_, v___y_3649_, v___y_3650_);
lean_dec(v___x_3657_);
if (lean_obj_tag(v___x_3664_) == 0)
{
size_t v___x_3665_; size_t v___x_3666_; 
lean_dec_ref_known(v___x_3664_, 1);
v___x_3665_ = ((size_t)1ULL);
v___x_3666_ = lean_usize_add(v_i_3647_, v___x_3665_);
v_i_3647_ = v___x_3666_;
v_b_3648_ = v___x_3654_;
goto _start;
}
else
{
return v___x_3664_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3645_ = stack[0].m_obj;
size_t v_sz_3646_ = stack[1].m_num;
size_t v_i_3647_ = stack[2].m_num;
lean_object* v_b_3648_ = stack[3].m_obj;
lean_object* v___y_3649_ = stack[4].m_obj;
lean_object* v___y_3650_ = stack[5].m_obj;
lean_object* v_res_3668_;
v_res_3668_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1(v_as_3645_, v_sz_3646_, v_i_3647_, v_b_3648_, v___y_3649_, v___y_3650_);
stack->m_obj
 = v_res_3668_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1___boxed(lean_object* v_as_3669_, lean_object* v_sz_3670_, lean_object* v_i_3671_, lean_object* v_b_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_){
_start:
{
size_t v_sz_boxed_3676_; size_t v_i_boxed_3677_; lean_object* v_res_3678_; 
v_sz_boxed_3676_ = lean_unbox_usize(v_sz_3670_);
lean_dec(v_sz_3670_);
v_i_boxed_3677_ = lean_unbox_usize(v_i_3671_);
lean_dec(v_i_3671_);
v_res_3678_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1(v_as_3669_, v_sz_boxed_3676_, v_i_boxed_3677_, v_b_3672_, v___y_3673_, v___y_3674_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
lean_dec_ref(v_as_3669_);
return v_res_3678_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__2(lean_object* v_as_3679_, size_t v_sz_3680_, size_t v_i_3681_, lean_object* v_b_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_){
_start:
{
uint8_t v___x_3686_; 
v___x_3686_ = lean_usize_dec_lt(v_i_3681_, v_sz_3680_);
if (v___x_3686_ == 0)
{
lean_object* v___x_3687_; 
v___x_3687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3687_, 0, v_b_3682_);
return v___x_3687_;
}
else
{
lean_object* v___x_3688_; lean_object* v_a_3689_; lean_object* v___x_3690_; size_t v_sz_3691_; size_t v___x_3692_; lean_object* v___x_3693_; 
v___x_3688_ = lean_box(0);
v_a_3689_ = lean_array_uget_borrowed(v_as_3679_, v_i_3681_);
v___x_3690_ = l_Lean_Syntax_getArgs(v_a_3689_);
v_sz_3691_ = lean_array_size(v___x_3690_);
v___x_3692_ = ((size_t)0ULL);
v___x_3693_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__1(v___x_3690_, v_sz_3691_, v___x_3692_, v___x_3688_, v___y_3683_, v___y_3684_);
lean_dec_ref(v___x_3690_);
if (lean_obj_tag(v___x_3693_) == 0)
{
size_t v___x_3694_; size_t v___x_3695_; 
lean_dec_ref_known(v___x_3693_, 1);
v___x_3694_ = ((size_t)1ULL);
v___x_3695_ = lean_usize_add(v_i_3681_, v___x_3694_);
v_i_3681_ = v___x_3695_;
v_b_3682_ = v___x_3688_;
goto _start;
}
else
{
return v___x_3693_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3679_ = stack[0].m_obj;
size_t v_sz_3680_ = stack[1].m_num;
size_t v_i_3681_ = stack[2].m_num;
lean_object* v_b_3682_ = stack[3].m_obj;
lean_object* v___y_3683_ = stack[4].m_obj;
lean_object* v___y_3684_ = stack[5].m_obj;
lean_object* v_res_3697_;
v_res_3697_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__2(v_as_3679_, v_sz_3680_, v_i_3681_, v_b_3682_, v___y_3683_, v___y_3684_);
stack->m_obj
 = v_res_3697_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__2___boxed(lean_object* v_as_3698_, lean_object* v_sz_3699_, lean_object* v_i_3700_, lean_object* v_b_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_){
_start:
{
size_t v_sz_boxed_3705_; size_t v_i_boxed_3706_; lean_object* v_res_3707_; 
v_sz_boxed_3705_ = lean_unbox_usize(v_sz_3699_);
lean_dec(v_sz_3699_);
v_i_boxed_3706_ = lean_unbox_usize(v_i_3700_);
lean_dec(v_i_3700_);
v_res_3707_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__2(v_as_3698_, v_sz_boxed_3705_, v_i_boxed_3706_, v_b_3701_, v___y_3702_, v___y_3703_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
lean_dec_ref(v_as_3698_);
return v_res_3707_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_elabContractNotice(lean_object* v_stx_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_){
_start:
{
lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; size_t v_sz_3715_; size_t v___x_3716_; lean_object* v___x_3717_; 
v___x_3712_ = l_Lean_Syntax_getArgs(v_stx_3708_);
v___x_3713_ = lean_array_pop(v___x_3712_);
v___x_3714_ = lean_box(0);
v_sz_3715_ = lean_array_size(v___x_3713_);
v___x_3716_ = ((size_t)0ULL);
v___x_3717_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__2(v___x_3713_, v_sz_3715_, v___x_3716_, v___x_3714_, v_a_3709_, v_a_3710_);
lean_dec_ref(v___x_3713_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3724_; 
v_isSharedCheck_3724_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3724_ == 0)
{
lean_object* v_unused_3725_; 
v_unused_3725_ = lean_ctor_get(v___x_3717_, 0);
lean_dec(v_unused_3725_);
v___x_3719_ = v___x_3717_;
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
else
{
lean_dec(v___x_3717_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___x_3722_; 
if (v_isShared_3720_ == 0)
{
lean_ctor_set(v___x_3719_, 0, v___x_3714_);
v___x_3722_ = v___x_3719_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v___x_3714_);
v___x_3722_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
return v___x_3722_;
}
}
}
else
{
return v___x_3717_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_elabContractNotice_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_3708_ = stack[0].m_obj;
lean_object* v_a_3709_ = stack[1].m_obj;
lean_object* v_a_3710_ = stack[2].m_obj;
lean_object* v_res_3726_;
v_res_3726_ = l_Lean_Elab_Tactic_Do_elabContractNotice(v_stx_3708_, v_a_3709_, v_a_3710_);
stack->m_obj
 = v_res_3726_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabContractNotice___boxed(lean_object* v_stx_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_){
_start:
{
lean_object* v_res_3731_; 
v_res_3731_ = l_Lean_Elab_Tactic_Do_elabContractNotice(v_stx_3727_, v_a_3728_, v_a_3729_);
lean_dec(v_a_3729_);
lean_dec_ref(v_a_3728_);
lean_dec(v_stx_3727_);
return v_res_3731_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5(lean_object* v_msgData_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_){
_start:
{
lean_object* v___x_3736_; 
v___x_3736_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___redArg(v_msgData_3732_, v___y_3734_);
return v___x_3736_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_3732_ = stack[0].m_obj;
lean_object* v___y_3733_ = stack[1].m_obj;
lean_object* v___y_3734_ = stack[2].m_obj;
lean_object* v_res_3737_;
v_res_3737_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5(v_msgData_3732_, v___y_3733_, v___y_3734_);
stack->m_obj
 = v_res_3737_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5___boxed(lean_object* v_msgData_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_){
_start:
{
lean_object* v_res_3742_; 
v_res_3742_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2_spec__5(v_msgData_3738_, v___y_3739_, v___y_3740_);
lean_dec(v___y_3740_);
lean_dec_ref(v___y_3739_);
return v_res_3742_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1(){
_start:
{
lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; 
v___x_3751_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3752_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_mkContractNotice___closed__1));
v___x_3753_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__1));
v___x_3754_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elabContractNotice___boxed), 4, 0);
v___x_3755_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3751_, v___x_3752_, v___x_3753_, v___x_3754_);
return v___x_3755_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3756_;
v_res_3756_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1();
stack->m_obj
 = v_res_3756_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___boxed(lean_object* v_a_3757_){
_start:
{
lean_object* v_res_3758_; 
v_res_3758_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1();
return v_res_3758_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice_docString__3(){
_start:
{
lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; 
v___x_3761_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice__1___closed__1));
v___x_3762_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice_docString__3___closed__0));
v___x_3763_ = l_Lean_addBuiltinDocString(v___x_3761_, v___x_3762_);
return v___x_3763_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice_docString__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3764_;
v_res_3764_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice_docString__3();
stack->m_obj
 = v_res_3764_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice_docString__3___boxed(lean_object* v_a_3765_){
_start:
{
lean_object* v_res_3766_; 
v_res_3766_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabContractNotice___regBuiltin_Lean_Elab_Tactic_Do_elabContractNotice_docString__3();
return v_res_3766_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; 
v___x_3767_ = lean_box(0);
v___x_3768_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3769_, 0, v___x_3768_);
lean_ctor_set(v___x_3769_, 1, v___x_3767_);
return v___x_3769_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg(){
_start:
{
lean_object* v___x_3771_; lean_object* v___x_3772_; 
v___x_3771_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg___closed__0);
v___x_3772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3772_, 0, v___x_3771_);
return v___x_3772_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3773_;
v_res_3773_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg();
stack->m_obj
 = v_res_3773_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg___boxed(lean_object* v___y_3774_){
_start:
{
lean_object* v_res_3775_; 
v_res_3775_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg();
return v_res_3775_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2(lean_object* v_00_u03b1_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_){
_start:
{
lean_object* v___x_3785_; 
v___x_3785_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg();
return v___x_3785_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3777_ = stack[1].m_obj;
lean_object* v___y_3778_ = stack[2].m_obj;
lean_object* v___y_3779_ = stack[3].m_obj;
lean_object* v___y_3780_ = stack[4].m_obj;
lean_object* v___y_3781_ = stack[5].m_obj;
lean_object* v___y_3782_ = stack[6].m_obj;
lean_object* v___y_3783_ = stack[7].m_obj;
lean_object* v_res_3786_;
v_res_3786_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2(lean_box(0), v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_);
stack->m_obj
 = v_res_3786_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___boxed(lean_object* v_00_u03b1_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_){
_start:
{
lean_object* v_res_3796_; 
v_res_3796_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2(v_00_u03b1_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_);
lean_dec(v___y_3794_);
lean_dec_ref(v___y_3793_);
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3791_);
lean_dec(v___y_3790_);
lean_dec_ref(v___y_3789_);
lean_dec_ref(v___y_3788_);
return v_res_3796_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2_spec__5(lean_object* v_msgData_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_){
_start:
{
lean_object* v___x_3803_; lean_object* v_env_3804_; uint8_t v___x_3805_; lean_object* v_env_3806_; lean_object* v___x_3807_; lean_object* v_toCold_3808_; lean_object* v_mctx_3809_; lean_object* v_lctx_3810_; lean_object* v_options_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; 
v___x_3803_ = lean_st_ref_get(v___y_3801_);
v_env_3804_ = lean_ctor_get(v___x_3803_, 0);
lean_inc_ref(v_env_3804_);
lean_dec(v___x_3803_);
v___x_3805_ = 0;
v_env_3806_ = l_Lean_Environment_setRecordingDeps(v_env_3804_, v___x_3805_);
v___x_3807_ = lean_st_ref_get(v___y_3799_);
v_toCold_3808_ = lean_ctor_get(v___y_3800_, 0);
v_mctx_3809_ = lean_ctor_get(v___x_3807_, 0);
lean_inc_ref(v_mctx_3809_);
lean_dec(v___x_3807_);
v_lctx_3810_ = lean_ctor_get(v___y_3798_, 2);
v_options_3811_ = lean_ctor_get(v_toCold_3808_, 2);
lean_inc_ref(v_options_3811_);
lean_inc_ref(v_lctx_3810_);
v___x_3812_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3812_, 0, v_env_3806_);
lean_ctor_set(v___x_3812_, 1, v_mctx_3809_);
lean_ctor_set(v___x_3812_, 2, v_lctx_3810_);
lean_ctor_set(v___x_3812_, 3, v_options_3811_);
v___x_3813_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3813_, 0, v___x_3812_);
lean_ctor_set(v___x_3813_, 1, v_msgData_3797_);
v___x_3814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3814_, 0, v___x_3813_);
return v___x_3814_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_3797_ = stack[0].m_obj;
lean_object* v___y_3798_ = stack[1].m_obj;
lean_object* v___y_3799_ = stack[2].m_obj;
lean_object* v___y_3800_ = stack[3].m_obj;
lean_object* v___y_3801_ = stack[4].m_obj;
lean_object* v_res_3815_;
v_res_3815_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2_spec__5(v_msgData_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_);
stack->m_obj
 = v_res_3815_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2_spec__5___boxed(lean_object* v_msgData_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_){
_start:
{
lean_object* v_res_3822_; 
v_res_3822_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2_spec__5(v_msgData_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_);
lean_dec(v___y_3820_);
lean_dec_ref(v___y_3819_);
lean_dec(v___y_3818_);
lean_dec_ref(v___y_3817_);
return v_res_3822_;
}
}
uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0(uint8_t v_suppressElabErrors_3828_, uint8_t v___y_3829_, lean_object* v_x_3830_){
_start:
{
if (lean_obj_tag(v_x_3830_) == 1)
{
lean_object* v_pre_3831_; 
v_pre_3831_ = lean_ctor_get(v_x_3830_, 0);
switch(lean_obj_tag(v_pre_3831_))
{
case 1:
{
lean_object* v_pre_3832_; 
v_pre_3832_ = lean_ctor_get(v_pre_3831_, 0);
switch(lean_obj_tag(v_pre_3832_))
{
case 0:
{
lean_object* v_str_3833_; lean_object* v_str_3834_; lean_object* v___x_3835_; uint8_t v___x_3836_; 
v_str_3833_ = lean_ctor_get(v_x_3830_, 1);
v_str_3834_ = lean_ctor_get(v_pre_3831_, 1);
v___x_3835_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__21));
v___x_3836_ = lean_string_dec_eq(v_str_3834_, v___x_3835_);
if (v___x_3836_ == 0)
{
lean_object* v___x_3837_; uint8_t v___x_3838_; 
v___x_3837_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__22));
v___x_3838_ = lean_string_dec_eq(v_str_3834_, v___x_3837_);
if (v___x_3838_ == 0)
{
return v___x_3838_;
}
else
{
lean_object* v___x_3839_; uint8_t v___x_3840_; 
v___x_3839_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__0));
v___x_3840_ = lean_string_dec_eq(v_str_3833_, v___x_3839_);
if (v___x_3840_ == 0)
{
return v___x_3840_;
}
else
{
return v_suppressElabErrors_3828_;
}
}
}
else
{
lean_object* v___x_3841_; uint8_t v___x_3842_; 
v___x_3841_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__1));
v___x_3842_ = lean_string_dec_eq(v_str_3833_, v___x_3841_);
if (v___x_3842_ == 0)
{
return v___x_3842_;
}
else
{
return v_suppressElabErrors_3828_;
}
}
}
case 1:
{
lean_object* v_pre_3843_; 
v_pre_3843_ = lean_ctor_get(v_pre_3832_, 0);
if (lean_obj_tag(v_pre_3843_) == 0)
{
lean_object* v_str_3844_; lean_object* v_str_3845_; lean_object* v_str_3846_; lean_object* v___x_3847_; uint8_t v___x_3848_; 
v_str_3844_ = lean_ctor_get(v_x_3830_, 1);
v_str_3845_ = lean_ctor_get(v_pre_3831_, 1);
v_str_3846_ = lean_ctor_get(v_pre_3832_, 1);
v___x_3847_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__2));
v___x_3848_ = lean_string_dec_eq(v_str_3846_, v___x_3847_);
if (v___x_3848_ == 0)
{
return v___x_3848_;
}
else
{
lean_object* v___x_3849_; uint8_t v___x_3850_; 
v___x_3849_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__3));
v___x_3850_ = lean_string_dec_eq(v_str_3845_, v___x_3849_);
if (v___x_3850_ == 0)
{
return v___x_3850_;
}
else
{
lean_object* v___x_3851_; uint8_t v___x_3852_; 
v___x_3851_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___closed__4));
v___x_3852_ = lean_string_dec_eq(v_str_3844_, v___x_3851_);
if (v___x_3852_ == 0)
{
return v___x_3852_;
}
else
{
return v_suppressElabErrors_3828_;
}
}
}
}
else
{
return v___y_3829_;
}
}
default: 
{
return v___y_3829_;
}
}
}
case 0:
{
lean_object* v_str_3853_; lean_object* v___x_3854_; uint8_t v___x_3855_; 
v_str_3853_ = lean_ctor_get(v_x_3830_, 1);
v___x_3854_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__1_spec__2___lam__0___closed__0));
v___x_3855_ = lean_string_dec_eq(v_str_3853_, v___x_3854_);
if (v___x_3855_ == 0)
{
return v___x_3855_;
}
else
{
return v_suppressElabErrors_3828_;
}
}
default: 
{
return v___y_3829_;
}
}
}
else
{
return v___y_3829_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_3828_ = stack[0].m_num;
uint8_t v___y_3829_ = stack[1].m_num;
lean_object* v_x_3830_ = stack[2].m_obj;
uint8_t v_res_3856_;
v_res_3856_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0(v_suppressElabErrors_3828_, v___y_3829_, v_x_3830_);
stack->m_num = v_res_3856_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_3857_, lean_object* v___y_3858_, lean_object* v_x_3859_){
_start:
{
uint8_t v_suppressElabErrors_boxed_3860_; uint8_t v___y_16828__boxed_3861_; uint8_t v_res_3862_; lean_object* v_r_3863_; 
v_suppressElabErrors_boxed_3860_ = lean_unbox(v_suppressElabErrors_3857_);
v___y_16828__boxed_3861_ = lean_unbox(v___y_3858_);
v_res_3862_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0(v_suppressElabErrors_boxed_3860_, v___y_16828__boxed_3861_, v_x_3859_);
lean_dec(v_x_3859_);
v_r_3863_ = lean_box(v_res_3862_);
return v_r_3863_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_3864_, lean_object* v_msgData_3865_, uint8_t v_severity_3866_, uint8_t v_isSilent_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_){
_start:
{
lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; uint8_t v___y_3877_; lean_object* v___y_3878_; uint8_t v___y_3879_; lean_object* v___y_3880_; lean_object* v_toCold_3881_; lean_object* v___y_3882_; lean_object* v___y_3911_; lean_object* v___y_3912_; lean_object* v___y_3913_; lean_object* v___y_3914_; uint8_t v___y_3915_; uint8_t v___y_3916_; uint8_t v___y_3917_; lean_object* v___y_3918_; lean_object* v___y_3938_; lean_object* v___y_3939_; uint8_t v___y_3940_; lean_object* v___y_3941_; uint8_t v___y_3942_; uint8_t v___y_3943_; lean_object* v___y_3944_; uint8_t v___y_3948_; uint8_t v___y_3949_; uint8_t v___y_3950_; uint8_t v___x_3961_; uint8_t v___y_3963_; uint8_t v___y_3964_; uint8_t v___y_3965_; uint8_t v___y_3967_; uint8_t v___x_3975_; 
v___x_3961_ = 2;
v___x_3975_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3866_, v___x_3961_);
if (v___x_3975_ == 0)
{
v___y_3967_ = v___x_3975_;
goto v___jp_3966_;
}
else
{
uint8_t v___x_3976_; 
lean_inc_ref(v_msgData_3865_);
v___x_3976_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3865_);
v___y_3967_ = v___x_3976_;
goto v___jp_3966_;
}
v___jp_3873_:
{
lean_object* v_currNamespace_3883_; lean_object* v_openDecls_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v_env_3889_; lean_object* v_nextMacroScope_3890_; lean_object* v_ngen_3891_; lean_object* v_auxDeclNGen_3892_; lean_object* v_traceState_3893_; lean_object* v_cache_3894_; lean_object* v_recordedDeps_3895_; lean_object* v_messages_3896_; lean_object* v_infoState_3897_; lean_object* v_snapshotTasks_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3909_; 
v_currNamespace_3883_ = lean_ctor_get(v_toCold_3881_, 4);
v_openDecls_3884_ = lean_ctor_get(v_toCold_3881_, 5);
lean_inc(v_openDecls_3884_);
lean_inc(v_currNamespace_3883_);
v___x_3885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3885_, 0, v_currNamespace_3883_);
lean_ctor_set(v___x_3885_, 1, v_openDecls_3884_);
v___x_3886_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3886_, 0, v___x_3885_);
lean_ctor_set(v___x_3886_, 1, v___y_3880_);
lean_inc_ref(v___y_3878_);
lean_inc_ref(v___y_3876_);
v___x_3887_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3887_, 0, v___y_3876_);
lean_ctor_set(v___x_3887_, 1, v___y_3874_);
lean_ctor_set(v___x_3887_, 2, v___y_3875_);
lean_ctor_set(v___x_3887_, 3, v___y_3878_);
lean_ctor_set(v___x_3887_, 4, v___x_3886_);
lean_ctor_set_uint8(v___x_3887_, sizeof(void*)*5, v___y_3879_);
lean_ctor_set_uint8(v___x_3887_, sizeof(void*)*5 + 1, v___y_3877_);
lean_ctor_set_uint8(v___x_3887_, sizeof(void*)*5 + 2, v_isSilent_3867_);
v___x_3888_ = lean_st_ref_take(v___y_3882_);
v_env_3889_ = lean_ctor_get(v___x_3888_, 0);
v_nextMacroScope_3890_ = lean_ctor_get(v___x_3888_, 1);
v_ngen_3891_ = lean_ctor_get(v___x_3888_, 2);
v_auxDeclNGen_3892_ = lean_ctor_get(v___x_3888_, 3);
v_traceState_3893_ = lean_ctor_get(v___x_3888_, 4);
v_cache_3894_ = lean_ctor_get(v___x_3888_, 5);
v_recordedDeps_3895_ = lean_ctor_get(v___x_3888_, 6);
v_messages_3896_ = lean_ctor_get(v___x_3888_, 7);
v_infoState_3897_ = lean_ctor_get(v___x_3888_, 8);
v_snapshotTasks_3898_ = lean_ctor_get(v___x_3888_, 9);
v_isSharedCheck_3909_ = !lean_is_exclusive(v___x_3888_);
if (v_isSharedCheck_3909_ == 0)
{
v___x_3900_ = v___x_3888_;
v_isShared_3901_ = v_isSharedCheck_3909_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_snapshotTasks_3898_);
lean_inc(v_infoState_3897_);
lean_inc(v_messages_3896_);
lean_inc(v_recordedDeps_3895_);
lean_inc(v_cache_3894_);
lean_inc(v_traceState_3893_);
lean_inc(v_auxDeclNGen_3892_);
lean_inc(v_ngen_3891_);
lean_inc(v_nextMacroScope_3890_);
lean_inc(v_env_3889_);
lean_dec(v___x_3888_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3909_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3905_; 
v___x_3902_ = lean_box(0);
v___x_3903_ = l_Lean_MessageLog_add(v___x_3887_, v_messages_3896_);
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 7, v___x_3903_);
v___x_3905_ = v___x_3900_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v_env_3889_);
lean_ctor_set(v_reuseFailAlloc_3908_, 1, v_nextMacroScope_3890_);
lean_ctor_set(v_reuseFailAlloc_3908_, 2, v_ngen_3891_);
lean_ctor_set(v_reuseFailAlloc_3908_, 3, v_auxDeclNGen_3892_);
lean_ctor_set(v_reuseFailAlloc_3908_, 4, v_traceState_3893_);
lean_ctor_set(v_reuseFailAlloc_3908_, 5, v_cache_3894_);
lean_ctor_set(v_reuseFailAlloc_3908_, 6, v_recordedDeps_3895_);
lean_ctor_set(v_reuseFailAlloc_3908_, 7, v___x_3903_);
lean_ctor_set(v_reuseFailAlloc_3908_, 8, v_infoState_3897_);
lean_ctor_set(v_reuseFailAlloc_3908_, 9, v_snapshotTasks_3898_);
v___x_3905_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
lean_object* v___x_3906_; lean_object* v___x_3907_; 
v___x_3906_ = lean_st_ref_put(v___y_3882_, v___x_3905_);
v___x_3907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3907_, 0, v___x_3902_);
return v___x_3907_;
}
}
}
v___jp_3910_:
{
lean_object* v_fileName_3919_; lean_object* v_fileMap_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3936_; 
v_fileName_3919_ = lean_ctor_get(v___y_3914_, 0);
v_fileMap_3920_ = lean_ctor_get(v___y_3914_, 1);
v___x_3921_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3865_);
v___x_3922_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2_spec__5(v___x_3921_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
v_a_3923_ = lean_ctor_get(v___x_3922_, 0);
v_isSharedCheck_3936_ = !lean_is_exclusive(v___x_3922_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3925_ = v___x_3922_;
v_isShared_3926_ = v_isSharedCheck_3936_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_a_3923_);
lean_dec(v___x_3922_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3936_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; 
lean_inc_ref_n(v_fileMap_3920_, 2);
v___x_3927_ = l_Lean_FileMap_toPosition(v_fileMap_3920_, v___y_3913_);
lean_dec(v___y_3913_);
v___x_3928_ = l_Lean_FileMap_toPosition(v_fileMap_3920_, v___y_3918_);
lean_dec(v___y_3918_);
v___x_3929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3929_, 0, v___x_3928_);
v___x_3930_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__19));
if (v___y_3916_ == 0)
{
lean_del_object(v___x_3925_);
lean_dec_ref(v___y_3911_);
v___y_3874_ = v___x_3927_;
v___y_3875_ = v___x_3929_;
v___y_3876_ = v_fileName_3919_;
v___y_3877_ = v___y_3915_;
v___y_3878_ = v___x_3930_;
v___y_3879_ = v___y_3917_;
v___y_3880_ = v_a_3923_;
v_toCold_3881_ = v___y_3912_;
v___y_3882_ = v___y_3871_;
goto v___jp_3873_;
}
else
{
uint8_t v___x_3931_; 
lean_inc(v_a_3923_);
v___x_3931_ = l_Lean_MessageData_hasTag(v___y_3911_, v_a_3923_);
if (v___x_3931_ == 0)
{
lean_object* v___x_3932_; lean_object* v___x_3934_; 
lean_dec_ref_known(v___x_3929_, 1);
lean_dec_ref(v___x_3927_);
lean_dec(v_a_3923_);
v___x_3932_ = lean_box(0);
if (v_isShared_3926_ == 0)
{
lean_ctor_set(v___x_3925_, 0, v___x_3932_);
v___x_3934_ = v___x_3925_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v___x_3932_);
v___x_3934_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
return v___x_3934_;
}
}
else
{
lean_del_object(v___x_3925_);
v___y_3874_ = v___x_3927_;
v___y_3875_ = v___x_3929_;
v___y_3876_ = v_fileName_3919_;
v___y_3877_ = v___y_3915_;
v___y_3878_ = v___x_3930_;
v___y_3879_ = v___y_3917_;
v___y_3880_ = v_a_3923_;
v_toCold_3881_ = v___y_3912_;
v___y_3882_ = v___y_3871_;
goto v___jp_3873_;
}
}
}
}
v___jp_3937_:
{
lean_object* v___x_3945_; 
v___x_3945_ = l_Lean_Syntax_getTailPos_x3f(v___y_3941_, v___y_3943_);
lean_dec(v___y_3941_);
if (lean_obj_tag(v___x_3945_) == 0)
{
lean_inc(v___y_3944_);
v___y_3911_ = v___y_3938_;
v___y_3912_ = v___y_3939_;
v___y_3913_ = v___y_3944_;
v___y_3914_ = v___y_3939_;
v___y_3915_ = v___y_3942_;
v___y_3916_ = v___y_3940_;
v___y_3917_ = v___y_3943_;
v___y_3918_ = v___y_3944_;
goto v___jp_3910_;
}
else
{
lean_object* v_val_3946_; 
v_val_3946_ = lean_ctor_get(v___x_3945_, 0);
lean_inc(v_val_3946_);
lean_dec_ref_known(v___x_3945_, 1);
v___y_3911_ = v___y_3938_;
v___y_3912_ = v___y_3939_;
v___y_3913_ = v___y_3944_;
v___y_3914_ = v___y_3939_;
v___y_3915_ = v___y_3942_;
v___y_3916_ = v___y_3940_;
v___y_3917_ = v___y_3943_;
v___y_3918_ = v_val_3946_;
goto v___jp_3910_;
}
}
v___jp_3947_:
{
lean_object* v_toCold_3951_; lean_object* v_ref_3952_; uint8_t v_suppressElabErrors_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___f_3956_; lean_object* v_ref_3957_; lean_object* v___x_3958_; 
v_toCold_3951_ = lean_ctor_get(v___y_3870_, 0);
v_ref_3952_ = lean_ctor_get(v___y_3870_, 2);
v_suppressElabErrors_3953_ = lean_ctor_get_uint8(v___y_3870_, sizeof(void*)*3 + 2);
v___x_3954_ = lean_box(v_suppressElabErrors_3953_);
v___x_3955_ = lean_box(v___y_3948_);
v___f_3956_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3956_, 0, v___x_3954_);
lean_closure_set(v___f_3956_, 1, v___x_3955_);
v_ref_3957_ = l_Lean_replaceRef(v_ref_3864_, v_ref_3952_);
v___x_3958_ = l_Lean_Syntax_getPos_x3f(v_ref_3957_, v___y_3949_);
if (lean_obj_tag(v___x_3958_) == 0)
{
lean_object* v___x_3959_; 
v___x_3959_ = lean_unsigned_to_nat(0u);
v___y_3938_ = v___f_3956_;
v___y_3939_ = v_toCold_3951_;
v___y_3940_ = v_suppressElabErrors_3953_;
v___y_3941_ = v_ref_3957_;
v___y_3942_ = v___y_3950_;
v___y_3943_ = v___y_3949_;
v___y_3944_ = v___x_3959_;
goto v___jp_3937_;
}
else
{
lean_object* v_val_3960_; 
v_val_3960_ = lean_ctor_get(v___x_3958_, 0);
lean_inc(v_val_3960_);
lean_dec_ref_known(v___x_3958_, 1);
v___y_3938_ = v___f_3956_;
v___y_3939_ = v_toCold_3951_;
v___y_3940_ = v_suppressElabErrors_3953_;
v___y_3941_ = v_ref_3957_;
v___y_3942_ = v___y_3950_;
v___y_3943_ = v___y_3949_;
v___y_3944_ = v_val_3960_;
goto v___jp_3937_;
}
}
v___jp_3962_:
{
if (v___y_3965_ == 0)
{
v___y_3948_ = v___y_3963_;
v___y_3949_ = v___y_3964_;
v___y_3950_ = v_severity_3866_;
goto v___jp_3947_;
}
else
{
v___y_3948_ = v___y_3963_;
v___y_3949_ = v___y_3964_;
v___y_3950_ = v___x_3961_;
goto v___jp_3947_;
}
}
v___jp_3966_:
{
if (v___y_3967_ == 0)
{
uint8_t v___x_3968_; uint8_t v___x_3969_; 
v___x_3968_ = 1;
v___x_3969_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3866_, v___x_3968_);
if (v___x_3969_ == 0)
{
v___y_3963_ = v___y_3967_;
v___y_3964_ = v___y_3967_;
v___y_3965_ = v___x_3969_;
goto v___jp_3962_;
}
else
{
lean_object* v___x_3970_; lean_object* v___x_3971_; uint8_t v___x_3972_; 
v___x_3970_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3870_);
v___x_3971_ = l_Lean_warningAsError;
v___x_3972_ = l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0(v___x_3970_, v___x_3971_);
lean_dec_ref(v___x_3970_);
v___y_3963_ = v___y_3967_;
v___y_3964_ = v___y_3967_;
v___y_3965_ = v___x_3972_;
goto v___jp_3962_;
}
}
else
{
lean_object* v___x_3973_; lean_object* v___x_3974_; 
lean_dec_ref(v_msgData_3865_);
v___x_3973_ = lean_box(0);
v___x_3974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3973_);
return v___x_3974_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3864_ = stack[0].m_obj;
lean_object* v_msgData_3865_ = stack[1].m_obj;
uint8_t v_severity_3866_ = stack[2].m_num;
uint8_t v_isSilent_3867_ = stack[3].m_num;
lean_object* v___y_3868_ = stack[4].m_obj;
lean_object* v___y_3869_ = stack[5].m_obj;
lean_object* v___y_3870_ = stack[6].m_obj;
lean_object* v___y_3871_ = stack[7].m_obj;
lean_object* v_res_3977_;
v_res_3977_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg(v_ref_3864_, v_msgData_3865_, v_severity_3866_, v_isSilent_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
stack->m_obj
 = v_res_3977_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_3978_, lean_object* v_msgData_3979_, lean_object* v_severity_3980_, lean_object* v_isSilent_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_){
_start:
{
uint8_t v_severity_boxed_3987_; uint8_t v_isSilent_boxed_3988_; lean_object* v_res_3989_; 
v_severity_boxed_3987_ = lean_unbox(v_severity_3980_);
v_isSilent_boxed_3988_ = lean_unbox(v_isSilent_3981_);
v_res_3989_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg(v_ref_3978_, v_msgData_3979_, v_severity_boxed_3987_, v_isSilent_boxed_3988_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_);
lean_dec(v___y_3985_);
lean_dec_ref(v___y_3984_);
lean_dec(v___y_3983_);
lean_dec_ref(v___y_3982_);
lean_dec(v_ref_3978_);
return v_res_3989_;
}
}
lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0(lean_object* v_ref_3990_, lean_object* v_msgData_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_){
_start:
{
uint8_t v___x_4000_; uint8_t v___x_4001_; lean_object* v___x_4002_; 
v___x_4000_ = 1;
v___x_4001_ = 0;
v___x_4002_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg(v_ref_3990_, v_msgData_3991_, v___x_4000_, v___x_4001_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_);
return v___x_4002_;
}
}
LEAN_EXPORT void l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3990_ = stack[0].m_obj;
lean_object* v_msgData_3991_ = stack[1].m_obj;
lean_object* v___y_3992_ = stack[2].m_obj;
lean_object* v___y_3993_ = stack[3].m_obj;
lean_object* v___y_3994_ = stack[4].m_obj;
lean_object* v___y_3995_ = stack[5].m_obj;
lean_object* v___y_3996_ = stack[6].m_obj;
lean_object* v___y_3997_ = stack[7].m_obj;
lean_object* v___y_3998_ = stack[8].m_obj;
lean_object* v_res_4003_;
v_res_4003_ = l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0(v_ref_3990_, v_msgData_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_);
stack->m_obj
 = v_res_4003_;
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0___boxed(lean_object* v_ref_4004_, lean_object* v_msgData_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_){
_start:
{
lean_object* v_res_4014_; 
v_res_4014_ = l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0(v_ref_4004_, v_msgData_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_);
lean_dec(v___y_4012_);
lean_dec_ref(v___y_4011_);
lean_dec(v___y_4010_);
lean_dec_ref(v___y_4009_);
lean_dec(v___y_4008_);
lean_dec_ref(v___y_4007_);
lean_dec_ref(v___y_4006_);
lean_dec(v_ref_4004_);
return v_res_4014_;
}
}
lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0(lean_object* v_kw_4015_, lean_object* v_what_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_){
_start:
{
lean_object* v___x_4025_; lean_object* v___x_4026_; uint8_t v___x_4027_; 
v___x_4025_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_4022_);
v___x_4026_ = l_Lean_Elab_Do_experimental_intrinsic;
v___x_4027_ = l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0_spec__0(v___x_4025_, v___x_4026_);
lean_dec_ref(v___x_4025_);
if (v___x_4027_ == 0)
{
lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; 
v___x_4028_ = lean_obj_once(&l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1, &l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1_once, _init_l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__1);
v___x_4029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4029_, 0, v___x_4028_);
lean_ctor_set(v___x_4029_, 1, v_what_4016_);
v___x_4030_ = lean_obj_once(&l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3, &l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3_once, _init_l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabContractNotice_spec__0___closed__3);
v___x_4031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4031_, 0, v___x_4029_);
lean_ctor_set(v___x_4031_, 1, v___x_4030_);
v___x_4032_ = l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0(v_kw_4015_, v___x_4031_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_);
return v___x_4032_;
}
else
{
lean_object* v___x_4033_; lean_object* v___x_4034_; 
lean_dec_ref(v_what_4016_);
v___x_4033_ = lean_box(0);
v___x_4034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4034_, 0, v___x_4033_);
return v___x_4034_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_kw_4015_ = stack[0].m_obj;
lean_object* v_what_4016_ = stack[1].m_obj;
lean_object* v___y_4017_ = stack[2].m_obj;
lean_object* v___y_4018_ = stack[3].m_obj;
lean_object* v___y_4019_ = stack[4].m_obj;
lean_object* v___y_4020_ = stack[5].m_obj;
lean_object* v___y_4021_ = stack[6].m_obj;
lean_object* v___y_4022_ = stack[7].m_obj;
lean_object* v___y_4023_ = stack[8].m_obj;
lean_object* v_res_4035_;
v_res_4035_ = l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0(v_kw_4015_, v_what_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_);
stack->m_obj
 = v_res_4035_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0___boxed(lean_object* v_kw_4036_, lean_object* v_what_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_){
_start:
{
lean_object* v_res_4046_; 
v_res_4046_ = l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0(v_kw_4036_, v_what_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_);
lean_dec(v___y_4044_);
lean_dec_ref(v___y_4043_);
lean_dec(v___y_4042_);
lean_dec_ref(v___y_4041_);
lean_dec(v___y_4040_);
lean_dec_ref(v___y_4039_);
lean_dec_ref(v___y_4038_);
lean_dec(v_kw_4036_);
return v_res_4046_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2___redArg(lean_object* v_msg_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_){
_start:
{
lean_object* v_ref_4053_; lean_object* v___x_4054_; lean_object* v_a_4055_; lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4063_; 
v_ref_4053_ = lean_ctor_get(v___y_4050_, 2);
v___x_4054_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2_spec__5(v_msg_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_);
v_a_4055_ = lean_ctor_get(v___x_4054_, 0);
v_isSharedCheck_4063_ = !lean_is_exclusive(v___x_4054_);
if (v_isSharedCheck_4063_ == 0)
{
v___x_4057_ = v___x_4054_;
v_isShared_4058_ = v_isSharedCheck_4063_;
goto v_resetjp_4056_;
}
else
{
lean_inc(v_a_4055_);
lean_dec(v___x_4054_);
v___x_4057_ = lean_box(0);
v_isShared_4058_ = v_isSharedCheck_4063_;
goto v_resetjp_4056_;
}
v_resetjp_4056_:
{
lean_object* v___x_4059_; lean_object* v___x_4061_; 
lean_inc(v_ref_4053_);
v___x_4059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4059_, 0, v_ref_4053_);
lean_ctor_set(v___x_4059_, 1, v_a_4055_);
if (v_isShared_4058_ == 0)
{
lean_ctor_set_tag(v___x_4057_, 1);
lean_ctor_set(v___x_4057_, 0, v___x_4059_);
v___x_4061_ = v___x_4057_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v___x_4059_);
v___x_4061_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
return v___x_4061_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_4047_ = stack[0].m_obj;
lean_object* v___y_4048_ = stack[1].m_obj;
lean_object* v___y_4049_ = stack[2].m_obj;
lean_object* v___y_4050_ = stack[3].m_obj;
lean_object* v___y_4051_ = stack[4].m_obj;
lean_object* v_res_4064_;
v_res_4064_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2___redArg(v_msg_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_);
stack->m_obj
 = v_res_4064_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2___redArg___boxed(lean_object* v_msg_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_){
_start:
{
lean_object* v_res_4071_; 
v_res_4071_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2___redArg(v_msg_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_);
lean_dec(v___y_4069_);
lean_dec_ref(v___y_4068_);
lean_dec(v___y_4067_);
lean_dec_ref(v___y_4066_);
return v_res_4071_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg(lean_object* v_ref_4072_, lean_object* v_msg_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_){
_start:
{
lean_object* v_toCold_4082_; lean_object* v_currRecDepth_4083_; lean_object* v_ref_4084_; uint16_t v_optionFlags_4085_; uint8_t v_suppressElabErrors_4086_; uint8_t v_isRecordingDeps_4087_; lean_object* v_ref_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; 
v_toCold_4082_ = lean_ctor_get(v___y_4079_, 0);
v_currRecDepth_4083_ = lean_ctor_get(v___y_4079_, 1);
v_ref_4084_ = lean_ctor_get(v___y_4079_, 2);
v_optionFlags_4085_ = lean_ctor_get_uint16(v___y_4079_, sizeof(void*)*3);
v_suppressElabErrors_4086_ = lean_ctor_get_uint8(v___y_4079_, sizeof(void*)*3 + 2);
v_isRecordingDeps_4087_ = lean_ctor_get_uint8(v___y_4079_, sizeof(void*)*3 + 3);
v_ref_4088_ = l_Lean_replaceRef(v_ref_4072_, v_ref_4084_);
lean_inc(v_currRecDepth_4083_);
lean_inc_ref(v_toCold_4082_);
v___x_4089_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_4089_, 0, v_toCold_4082_);
lean_ctor_set(v___x_4089_, 1, v_currRecDepth_4083_);
lean_ctor_set(v___x_4089_, 2, v_ref_4088_);
lean_ctor_set_uint16(v___x_4089_, sizeof(void*)*3, v_optionFlags_4085_);
lean_ctor_set_uint8(v___x_4089_, sizeof(void*)*3 + 2, v_suppressElabErrors_4086_);
lean_ctor_set_uint8(v___x_4089_, sizeof(void*)*3 + 3, v_isRecordingDeps_4087_);
v___x_4090_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2___redArg(v_msg_4073_, v___y_4077_, v___y_4078_, v___x_4089_, v___y_4080_);
lean_dec_ref_known(v___x_4089_, 3);
return v___x_4090_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_4072_ = stack[0].m_obj;
lean_object* v_msg_4073_ = stack[1].m_obj;
lean_object* v___y_4074_ = stack[2].m_obj;
lean_object* v___y_4075_ = stack[3].m_obj;
lean_object* v___y_4076_ = stack[4].m_obj;
lean_object* v___y_4077_ = stack[5].m_obj;
lean_object* v___y_4078_ = stack[6].m_obj;
lean_object* v___y_4079_ = stack[7].m_obj;
lean_object* v___y_4080_ = stack[8].m_obj;
lean_object* v_res_4091_;
v_res_4091_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg(v_ref_4072_, v_msg_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
stack->m_obj
 = v_res_4091_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg___boxed(lean_object* v_ref_4092_, lean_object* v_msg_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_){
_start:
{
lean_object* v_res_4102_; 
v_res_4102_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg(v_ref_4092_, v_msg_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
lean_dec(v___y_4100_);
lean_dec_ref(v___y_4099_);
lean_dec(v___y_4098_);
lean_dec_ref(v___y_4097_);
lean_dec(v___y_4096_);
lean_dec_ref(v___y_4095_);
lean_dec_ref(v___y_4094_);
lean_dec(v_ref_4092_);
return v_res_4102_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__1(void){
_start:
{
lean_object* v___x_4104_; lean_object* v___x_4105_; 
v___x_4104_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__0));
v___x_4105_ = l_Lean_stringToMessageData(v___x_4104_);
return v___x_4105_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__9(void){
_start:
{
lean_object* v___x_4129_; lean_object* v___x_4130_; 
v___x_4129_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__8));
v___x_4130_ = l_Lean_mkCIdent(v___x_4129_);
return v___x_4130_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__11(void){
_start:
{
lean_object* v___x_4132_; lean_object* v___x_4133_; 
v___x_4132_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__10));
v___x_4133_ = l_Lean_stringToMessageData(v___x_4132_);
return v___x_4133_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion(lean_object* v_stx_4140_, lean_object* v_dec_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_){
_start:
{
lean_object* v___x_4150_; lean_object* v_tk_4151_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v___y_4156_; lean_object* v___y_4157_; lean_object* v___y_4158_; lean_object* v___y_4159_; lean_object* v___y_4160_; lean_object* v_as_4230_; lean_object* v___y_4231_; lean_object* v___y_4232_; lean_object* v___y_4233_; lean_object* v___y_4234_; lean_object* v___y_4235_; lean_object* v___y_4236_; lean_object* v___y_4237_; lean_object* v___x_4253_; uint8_t v___x_4254_; 
v___x_4150_ = lean_unsigned_to_nat(0u);
v_tk_4151_ = l_Lean_Syntax_getArg(v_stx_4140_, v___x_4150_);
v___x_4253_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__13));
lean_inc(v_stx_4140_);
v___x_4254_ = l_Lean_Syntax_isOfKind(v_stx_4140_, v___x_4253_);
if (v___x_4254_ == 0)
{
lean_object* v___x_4255_; lean_object* v_a_4256_; lean_object* v___x_4258_; uint8_t v_isShared_4259_; uint8_t v_isSharedCheck_4263_; 
lean_dec(v_tk_4151_);
lean_dec_ref(v_dec_4141_);
lean_dec(v_stx_4140_);
v___x_4255_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__2___redArg();
v_a_4256_ = lean_ctor_get(v___x_4255_, 0);
v_isSharedCheck_4263_ = !lean_is_exclusive(v___x_4255_);
if (v_isSharedCheck_4263_ == 0)
{
v___x_4258_ = v___x_4255_;
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
else
{
lean_inc(v_a_4256_);
lean_dec(v___x_4255_);
v___x_4258_ = lean_box(0);
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
v_resetjp_4257_:
{
lean_object* v___x_4261_; 
if (v_isShared_4259_ == 0)
{
v___x_4261_ = v___x_4258_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v_a_4256_);
v___x_4261_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
return v___x_4261_;
}
}
}
else
{
lean_object* v___x_4264_; lean_object* v_p_4265_; lean_object* v___x_4266_; uint8_t v___x_4267_; 
v___x_4264_ = lean_unsigned_to_nat(1u);
v_p_4265_ = l_Lean_Syntax_getArg(v_stx_4140_, v___x_4264_);
lean_dec(v_stx_4140_);
v___x_4266_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__3));
lean_inc(v_p_4265_);
v___x_4267_ = l_Lean_Syntax_isOfKind(v_p_4265_, v___x_4266_);
if (v___x_4267_ == 0)
{
v_as_4230_ = v_p_4265_;
v___y_4231_ = v_a_4142_;
v___y_4232_ = v_a_4143_;
v___y_4233_ = v_a_4144_;
v___y_4234_ = v_a_4145_;
v___y_4235_ = v_a_4146_;
v___y_4236_ = v_a_4147_;
v___y_4237_ = v_a_4148_;
goto v___jp_4229_;
}
else
{
lean_object* v_ref_4268_; uint8_t v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; 
v_ref_4268_ = lean_ctor_get(v_a_4147_, 2);
v___x_4269_ = 0;
v___x_4270_ = l_Lean_SourceInfo_fromRef(v_ref_4268_, v___x_4269_);
v___x_4271_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__40));
v___x_4272_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__41));
lean_inc(v___x_4270_);
v___x_4273_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4273_, 0, v___x_4270_);
lean_ctor_set(v___x_4273_, 1, v___x_4271_);
v___x_4274_ = l_Lean_Syntax_node2(v___x_4270_, v___x_4272_, v___x_4273_, v_p_4265_);
v_as_4230_ = v___x_4274_;
v___y_4231_ = v_a_4142_;
v___y_4232_ = v_a_4143_;
v___y_4233_ = v_a_4144_;
v___y_4234_ = v_a_4145_;
v___y_4235_ = v_a_4146_;
v___y_4236_ = v_a_4147_;
v___y_4237_ = v_a_4148_;
goto v___jp_4229_;
}
}
v___jp_4152_:
{
lean_object* v___x_4161_; lean_object* v___x_4162_; 
v___x_4161_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__1, &l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__1_once, _init_l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__1);
v___x_4162_ = l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0(v_tk_4151_, v___x_4161_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_);
if (lean_obj_tag(v___x_4162_) == 0)
{
lean_object* v___x_4163_; 
lean_dec_ref_known(v___x_4162_, 1);
v___x_4163_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_4141_, v_tk_4151_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_);
lean_dec(v_tk_4151_);
if (lean_obj_tag(v___x_4163_) == 0)
{
lean_object* v_toCold_4164_; lean_object* v_a_4165_; lean_object* v_ref_4166_; lean_object* v_quotContext_4167_; lean_object* v_currMacroScope_4168_; uint8_t v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; 
v_toCold_4164_ = lean_ctor_get(v___y_4159_, 0);
v_a_4165_ = lean_ctor_get(v___x_4163_, 0);
lean_inc(v_a_4165_);
lean_dec_ref_known(v___x_4163_, 1);
v_ref_4166_ = lean_ctor_get(v___y_4159_, 2);
v_quotContext_4167_ = lean_ctor_get(v_toCold_4164_, 8);
v_currMacroScope_4168_ = lean_ctor_get(v_toCold_4164_, 9);
v___x_4169_ = 0;
v___x_4170_ = l_Lean_SourceInfo_fromRef(v_ref_4166_, v___x_4169_);
v___x_4171_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__1));
v___x_4172_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__2));
lean_inc_n(v___x_4170_, 9);
v___x_4173_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4173_, 0, v___x_4170_);
lean_ctor_set(v___x_4173_, 1, v___x_4171_);
v___x_4174_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__3));
v___x_4175_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__3));
v___x_4176_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4176_, 0, v___x_4170_);
lean_ctor_set(v___x_4176_, 1, v___x_4175_);
v___x_4177_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_extractSpecSection___closed__2));
v___x_4178_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_expandDefContract___closed__5, &l_Lean_Elab_Tactic_Do_expandDefContract___closed__5_once, _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__5);
v___x_4179_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__29));
lean_inc_n(v_currMacroScope_4168_, 2);
lean_inc_n(v_quotContext_4167_, 2);
v___x_4180_ = l_Lean_addMacroScope(v_quotContext_4167_, v___x_4179_, v_currMacroScope_4168_);
v___x_4181_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__4));
v___x_4182_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4182_, 0, v___x_4170_);
lean_ctor_set(v___x_4182_, 1, v___x_4178_);
lean_ctor_set(v___x_4182_, 2, v___x_4180_);
lean_ctor_set(v___x_4182_, 3, v___x_4181_);
v___x_4183_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_expandDefContract___closed__7, &l_Lean_Elab_Tactic_Do_expandDefContract___closed__7_once, _init_l_Lean_Elab_Tactic_Do_expandDefContract___closed__7);
v___x_4184_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__27));
v___x_4185_ = l_Lean_addMacroScope(v_quotContext_4167_, v___x_4184_, v_currMacroScope_4168_);
v___x_4186_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__5));
v___x_4187_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4187_, 0, v___x_4170_);
lean_ctor_set(v___x_4187_, 1, v___x_4183_);
lean_ctor_set(v___x_4187_, 2, v___x_4185_);
lean_ctor_set(v___x_4187_, 3, v___x_4186_);
v___x_4188_ = l_Lean_Syntax_node2(v___x_4170_, v___x_4177_, v___x_4182_, v___x_4187_);
v___x_4189_ = l_Lean_Syntax_node2(v___x_4170_, v___x_4174_, v___x_4176_, v___x_4188_);
v___x_4190_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_expandDefContract___closed__0));
v___x_4191_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4191_, 0, v___x_4170_);
lean_ctor_set(v___x_4191_, 1, v___x_4190_);
v___x_4192_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_expandDefContract_spec__2___closed__7));
v___x_4193_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__9, &l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__9_once, _init_l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__9);
v___x_4194_ = l_Lean_Syntax_node1(v___x_4170_, v___x_4177_, v___y_4153_);
v___x_4195_ = l_Lean_Syntax_node2(v___x_4170_, v___x_4192_, v___x_4193_, v___x_4194_);
v___x_4196_ = l_Lean_Syntax_node4(v___x_4170_, v___x_4172_, v___x_4173_, v___x_4189_, v___x_4191_, v___x_4195_);
v___x_4197_ = l_Lean_Elab_Do_mkPUnit___redArg(v___y_4154_);
if (lean_obj_tag(v___x_4197_) == 0)
{
lean_object* v_a_4198_; lean_object* v___x_4199_; 
v_a_4198_ = lean_ctor_get(v___x_4197_, 0);
lean_inc(v_a_4198_);
lean_dec_ref_known(v___x_4197_, 1);
v___x_4199_ = l_Lean_Elab_Do_mkMonadApp(v_a_4198_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_);
if (lean_obj_tag(v___x_4199_) == 0)
{
lean_object* v_a_4200_; lean_object* v___x_4202_; uint8_t v_isShared_4203_; uint8_t v_isSharedCheck_4212_; 
v_a_4200_ = lean_ctor_get(v___x_4199_, 0);
v_isSharedCheck_4212_ = !lean_is_exclusive(v___x_4199_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4202_ = v___x_4199_;
v_isShared_4203_ = v_isSharedCheck_4212_;
goto v_resetjp_4201_;
}
else
{
lean_inc(v_a_4200_);
lean_dec(v___x_4199_);
v___x_4202_ = lean_box(0);
v_isShared_4203_ = v_isSharedCheck_4212_;
goto v_resetjp_4201_;
}
v_resetjp_4201_:
{
lean_object* v___x_4205_; 
if (v_isShared_4203_ == 0)
{
lean_ctor_set_tag(v___x_4202_, 1);
v___x_4205_ = v___x_4202_;
goto v_reusejp_4204_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_a_4200_);
v___x_4205_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4204_;
}
v_reusejp_4204_:
{
uint8_t v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; 
v___x_4206_ = 1;
v___x_4207_ = lean_box(0);
v___x_4208_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_4196_, v___x_4205_, v___x_4206_, v___x_4206_, v___x_4207_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_);
if (lean_obj_tag(v___x_4208_) == 0)
{
lean_object* v_a_4209_; lean_object* v___x_4210_; 
v_a_4209_ = lean_ctor_get(v___x_4208_, 0);
lean_inc(v_a_4209_);
lean_dec_ref_known(v___x_4208_, 1);
v___x_4210_ = l_Lean_Elab_Do_DoElemCont_mkBindUnlessPure(v_a_4165_, v_a_4209_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_);
return v___x_4210_;
}
else
{
lean_dec(v_a_4165_);
return v___x_4208_;
}
}
}
}
else
{
lean_dec(v___x_4196_);
lean_dec(v_a_4165_);
return v___x_4199_;
}
}
else
{
lean_dec(v___x_4196_);
lean_dec(v_a_4165_);
return v___x_4197_;
}
}
else
{
lean_object* v_a_4213_; lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4220_; 
lean_dec(v___y_4153_);
v_a_4213_ = lean_ctor_get(v___x_4163_, 0);
v_isSharedCheck_4220_ = !lean_is_exclusive(v___x_4163_);
if (v_isSharedCheck_4220_ == 0)
{
v___x_4215_ = v___x_4163_;
v_isShared_4216_ = v_isSharedCheck_4220_;
goto v_resetjp_4214_;
}
else
{
lean_inc(v_a_4213_);
lean_dec(v___x_4163_);
v___x_4215_ = lean_box(0);
v_isShared_4216_ = v_isSharedCheck_4220_;
goto v_resetjp_4214_;
}
v_resetjp_4214_:
{
lean_object* v___x_4218_; 
if (v_isShared_4216_ == 0)
{
v___x_4218_ = v___x_4215_;
goto v_reusejp_4217_;
}
else
{
lean_object* v_reuseFailAlloc_4219_; 
v_reuseFailAlloc_4219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4219_, 0, v_a_4213_);
v___x_4218_ = v_reuseFailAlloc_4219_;
goto v_reusejp_4217_;
}
v_reusejp_4217_:
{
return v___x_4218_;
}
}
}
}
else
{
lean_object* v_a_4221_; lean_object* v___x_4223_; uint8_t v_isShared_4224_; uint8_t v_isSharedCheck_4228_; 
lean_dec(v___y_4153_);
lean_dec(v_tk_4151_);
lean_dec_ref(v_dec_4141_);
v_a_4221_ = lean_ctor_get(v___x_4162_, 0);
v_isSharedCheck_4228_ = !lean_is_exclusive(v___x_4162_);
if (v_isSharedCheck_4228_ == 0)
{
v___x_4223_ = v___x_4162_;
v_isShared_4224_ = v_isSharedCheck_4228_;
goto v_resetjp_4222_;
}
else
{
lean_inc(v_a_4221_);
lean_dec(v___x_4162_);
v___x_4223_ = lean_box(0);
v_isShared_4224_ = v_isSharedCheck_4228_;
goto v_resetjp_4222_;
}
v_resetjp_4222_:
{
lean_object* v___x_4226_; 
if (v_isShared_4224_ == 0)
{
v___x_4226_ = v___x_4223_;
goto v_reusejp_4225_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v_a_4221_);
v___x_4226_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4225_;
}
v_reusejp_4225_:
{
return v___x_4226_;
}
}
}
}
v___jp_4229_:
{
lean_object* v___x_4238_; lean_object* v_env_4239_; lean_object* v___x_4240_; uint8_t v___x_4241_; uint8_t v___x_4242_; 
v___x_4238_ = lean_st_ref_get(v___y_4237_);
v_env_4239_ = lean_ctor_get(v___x_4238_, 0);
lean_inc_ref(v_env_4239_);
lean_dec(v___x_4238_);
v___x_4240_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__8));
v___x_4241_ = 1;
v___x_4242_ = l_Lean_Environment_contains(v_env_4239_, v___x_4240_, v___x_4241_);
if (v___x_4242_ == 0)
{
lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v_a_4245_; lean_object* v___x_4247_; uint8_t v_isShared_4248_; uint8_t v_isSharedCheck_4252_; 
lean_dec(v_as_4230_);
lean_dec_ref(v_dec_4141_);
v___x_4243_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__11, &l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__11_once, _init_l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__11);
v___x_4244_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg(v_tk_4151_, v___x_4243_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_);
lean_dec(v_tk_4151_);
v_a_4245_ = lean_ctor_get(v___x_4244_, 0);
v_isSharedCheck_4252_ = !lean_is_exclusive(v___x_4244_);
if (v_isSharedCheck_4252_ == 0)
{
v___x_4247_ = v___x_4244_;
v_isShared_4248_ = v_isSharedCheck_4252_;
goto v_resetjp_4246_;
}
else
{
lean_inc(v_a_4245_);
lean_dec(v___x_4244_);
v___x_4247_ = lean_box(0);
v_isShared_4248_ = v_isSharedCheck_4252_;
goto v_resetjp_4246_;
}
v_resetjp_4246_:
{
lean_object* v___x_4250_; 
if (v_isShared_4248_ == 0)
{
v___x_4250_ = v___x_4247_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4251_; 
v_reuseFailAlloc_4251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4251_, 0, v_a_4245_);
v___x_4250_ = v_reuseFailAlloc_4251_;
goto v_reusejp_4249_;
}
v_reusejp_4249_:
{
return v___x_4250_;
}
}
}
else
{
v___y_4153_ = v_as_4230_;
v___y_4154_ = v___y_4231_;
v___y_4155_ = v___y_4232_;
v___y_4156_ = v___y_4233_;
v___y_4157_ = v___y_4234_;
v___y_4158_ = v___y_4235_;
v___y_4159_ = v___y_4236_;
v___y_4160_ = v___y_4237_;
goto v___jp_4152_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_elabDoAssertion_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_4140_ = stack[0].m_obj;
lean_object* v_dec_4141_ = stack[1].m_obj;
lean_object* v_a_4142_ = stack[2].m_obj;
lean_object* v_a_4143_ = stack[3].m_obj;
lean_object* v_a_4144_ = stack[4].m_obj;
lean_object* v_a_4145_ = stack[5].m_obj;
lean_object* v_a_4146_ = stack[6].m_obj;
lean_object* v_a_4147_ = stack[7].m_obj;
lean_object* v_a_4148_ = stack[8].m_obj;
lean_object* v_res_4275_;
v_res_4275_ = l_Lean_Elab_Tactic_Do_elabDoAssertion(v_stx_4140_, v_dec_4141_, v_a_4142_, v_a_4143_, v_a_4144_, v_a_4145_, v_a_4146_, v_a_4147_, v_a_4148_);
stack->m_obj
 = v_res_4275_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabDoAssertion___boxed(lean_object* v_stx_4276_, lean_object* v_dec_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_){
_start:
{
lean_object* v_res_4286_; 
v_res_4286_ = l_Lean_Elab_Tactic_Do_elabDoAssertion(v_stx_4276_, v_dec_4277_, v_a_4278_, v_a_4279_, v_a_4280_, v_a_4281_, v_a_4282_, v_a_4283_, v_a_4284_);
lean_dec(v_a_4284_);
lean_dec_ref(v_a_4283_);
lean_dec(v_a_4282_);
lean_dec_ref(v_a_4281_);
lean_dec(v_a_4280_);
lean_dec_ref(v_a_4279_);
lean_dec_ref(v_a_4278_);
return v_res_4286_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1(lean_object* v_00_u03b1_4287_, lean_object* v_ref_4288_, lean_object* v_msg_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_){
_start:
{
lean_object* v___x_4298_; 
v___x_4298_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___redArg(v_ref_4288_, v_msg_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_);
return v___x_4298_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_4288_ = stack[1].m_obj;
lean_object* v_msg_4289_ = stack[2].m_obj;
lean_object* v___y_4290_ = stack[3].m_obj;
lean_object* v___y_4291_ = stack[4].m_obj;
lean_object* v___y_4292_ = stack[5].m_obj;
lean_object* v___y_4293_ = stack[6].m_obj;
lean_object* v___y_4294_ = stack[7].m_obj;
lean_object* v___y_4295_ = stack[8].m_obj;
lean_object* v___y_4296_ = stack[9].m_obj;
lean_object* v_res_4299_;
v_res_4299_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1(lean_box(0), v_ref_4288_, v_msg_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_);
stack->m_obj
 = v_res_4299_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1___boxed(lean_object* v_00_u03b1_4300_, lean_object* v_ref_4301_, lean_object* v_msg_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_){
_start:
{
lean_object* v_res_4311_; 
v_res_4311_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1(v_00_u03b1_4300_, v_ref_4301_, v_msg_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_);
lean_dec(v___y_4309_);
lean_dec_ref(v___y_4308_);
lean_dec(v___y_4307_);
lean_dec_ref(v___y_4306_);
lean_dec(v___y_4305_);
lean_dec_ref(v___y_4304_);
lean_dec_ref(v___y_4303_);
lean_dec(v_ref_4301_);
return v_res_4311_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2(lean_object* v_00_u03b1_4312_, lean_object* v_msg_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_){
_start:
{
lean_object* v___x_4322_; 
v___x_4322_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2___redArg(v_msg_4313_, v___y_4317_, v___y_4318_, v___y_4319_, v___y_4320_);
return v___x_4322_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_4313_ = stack[1].m_obj;
lean_object* v___y_4314_ = stack[2].m_obj;
lean_object* v___y_4315_ = stack[3].m_obj;
lean_object* v___y_4316_ = stack[4].m_obj;
lean_object* v___y_4317_ = stack[5].m_obj;
lean_object* v___y_4318_ = stack[6].m_obj;
lean_object* v___y_4319_ = stack[7].m_obj;
lean_object* v___y_4320_ = stack[8].m_obj;
lean_object* v_res_4323_;
v_res_4323_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2(lean_box(0), v_msg_4313_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_, v___y_4320_);
stack->m_obj
 = v_res_4323_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2___boxed(lean_object* v_00_u03b1_4324_, lean_object* v_msg_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_){
_start:
{
lean_object* v_res_4334_; 
v_res_4334_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__1_spec__2(v_00_u03b1_4324_, v_msg_4325_, v___y_4326_, v___y_4327_, v___y_4328_, v___y_4329_, v___y_4330_, v___y_4331_, v___y_4332_);
lean_dec(v___y_4332_);
lean_dec_ref(v___y_4331_);
lean_dec(v___y_4330_);
lean_dec_ref(v___y_4329_);
lean_dec(v___y_4328_);
lean_dec_ref(v___y_4327_);
lean_dec_ref(v___y_4326_);
return v_res_4334_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2(lean_object* v_ref_4335_, lean_object* v_msgData_4336_, uint8_t v_severity_4337_, uint8_t v_isSilent_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_){
_start:
{
lean_object* v___x_4347_; 
v___x_4347_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___redArg(v_ref_4335_, v_msgData_4336_, v_severity_4337_, v_isSilent_4338_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_);
return v___x_4347_;
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_4335_ = stack[0].m_obj;
lean_object* v_msgData_4336_ = stack[1].m_obj;
uint8_t v_severity_4337_ = stack[2].m_num;
uint8_t v_isSilent_4338_ = stack[3].m_num;
lean_object* v___y_4339_ = stack[4].m_obj;
lean_object* v___y_4340_ = stack[5].m_obj;
lean_object* v___y_4341_ = stack[6].m_obj;
lean_object* v___y_4342_ = stack[7].m_obj;
lean_object* v___y_4343_ = stack[8].m_obj;
lean_object* v___y_4344_ = stack[9].m_obj;
lean_object* v___y_4345_ = stack[10].m_obj;
lean_object* v_res_4348_;
v_res_4348_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2(v_ref_4335_, v_msgData_4336_, v_severity_4337_, v_isSilent_4338_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_);
stack->m_obj
 = v_res_4348_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2___boxed(lean_object* v_ref_4349_, lean_object* v_msgData_4350_, lean_object* v_severity_4351_, lean_object* v_isSilent_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_){
_start:
{
uint8_t v_severity_boxed_4361_; uint8_t v_isSilent_boxed_4362_; lean_object* v_res_4363_; 
v_severity_boxed_4361_ = lean_unbox(v_severity_4351_);
v_isSilent_boxed_4362_ = lean_unbox(v_isSilent_4352_);
v_res_4363_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Tactic_Do_elabDoAssertion_spec__0_spec__0_spec__2(v_ref_4349_, v_msgData_4350_, v_severity_boxed_4361_, v_isSilent_boxed_4362_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_);
lean_dec(v___y_4359_);
lean_dec_ref(v___y_4358_);
lean_dec(v___y_4357_);
lean_dec_ref(v___y_4356_);
lean_dec(v___y_4355_);
lean_dec_ref(v___y_4354_);
lean_dec_ref(v___y_4353_);
lean_dec(v_ref_4349_);
return v_res_4363_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1(){
_start:
{
lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; 
v___x_4372_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4373_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___closed__13));
v___x_4374_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___closed__1));
v___x_4375_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elabDoAssertion___boxed), 10, 0);
v___x_4376_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4372_, v___x_4373_, v___x_4374_, v___x_4375_);
return v___x_4376_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4377_;
v_res_4377_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1();
stack->m_obj
 = v_res_4377_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1___boxed(lean_object* v_a_4378_){
_start:
{
lean_object* v_res_4379_; 
v_res_4379_ = l___private_Lean_Elab_Tactic_Do_Contract_0__Lean_Elab_Tactic_Do_elabDoAssertion___regBuiltin_Lean_Elab_Tactic_Do_elabDoAssertion__1();
return v_res_4379_;
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
