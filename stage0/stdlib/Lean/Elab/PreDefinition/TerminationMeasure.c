// Lean compiler output
// Module: Lean.Elab.PreDefinition.TerminationMeasure
// Imports: public import Lean.Elab.Binders import Init.Omega
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
uint8_t l_Lean_Syntax_hasIdent(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_andList(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_Term_elabFunBinders___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM___redArg();
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isSuffixOf(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_delabCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withDeclName___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__0 = (const lean_object*)&l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__0_value;
static const lean_ctor_object l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__1 = (const lean_object*)&l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__1_value;
static lean_once_cell_t l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__2;
static lean_once_cell_t l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedTerminationMeasure_default;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedTerminationMeasure;
static const lean_string_object l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = " parameters"};
static const lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__1;
static const lean_string_object l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "one parameter"};
static const lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__2_value)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_TerminationMeasure_elab_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_TerminationMeasure_elab_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_TerminationMeasure_elab_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_TerminationMeasure_elab_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__10___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2_spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3___closed__0_value;
static lean_once_cell_t l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3___closed__1;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__0_value;
static const lean_string_object l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__1_value;
static const lean_string_object l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__3;
static const lean_string_object l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "The termination measure of a structurally recursive "};
static const lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__4_value;
static lean_once_cell_t l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__5;
static const lean_string_object l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "function must be one of the parameters "};
static const lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__6_value;
static lean_once_cell_t l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__7;
static const lean_string_object l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = ", but"};
static const lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__8 = (const lean_object*)&l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__8_value;
static lean_once_cell_t l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__9;
static const lean_string_object l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "\nisn't "};
static const lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__10 = (const lean_object*)&l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__10_value;
static lean_once_cell_t l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__11;
static const lean_string_object l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "one of these."};
static const lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__12 = (const lean_object*)&l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__12_value;
static lean_once_cell_t l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__13;
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Lean.Elab.PreDefinition.TerminationMeasure"};
static const lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__0 = (const lean_object*)&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__0_value;
static const lean_string_object l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Lean.Elab.TerminationMeasure.elab"};
static const lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__1 = (const lean_object*)&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__1_value;
static const lean_string_object l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 43, .m_data = "assertion violation: extraParams ≤ arity\n  "};
static const lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__2 = (const lean_object*)&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__2_value;
static lean_once_cell_t l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__3;
static const lean_string_object l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = " bound in `termination_by`, but the body of "};
static const lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__4 = (const lean_object*)&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__4_value;
static lean_once_cell_t l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__5;
static const lean_string_object l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = " only binds "};
static const lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__6 = (const lean_object*)&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__6_value;
static lean_once_cell_t l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__7;
static const lean_string_object l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__8 = (const lean_object*)&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__8_value;
static lean_once_cell_t l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__9;
static const lean_string_object l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__10 = (const lean_object*)&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__10_value;
static const lean_ctor_object l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__11 = (const lean_object*)&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__11_value;
static const lean_string_object l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = " (Since Lean v4.6.0, the `termination_by` clause no longer "};
static const lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__12 = (const lean_object*)&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__12_value;
static lean_once_cell_t l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__13;
static const lean_string_object l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "expects the function name here.)"};
static const lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__14 = (const lean_object*)&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__14_value;
static const lean_ctor_object l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__14_value)}};
static const lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__15 = (const lean_object*)&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__15_value;
static lean_once_cell_t l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__16;
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1___closed__0 = (const lean_object*)&l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Lean.Elab.TerminationMeasure.structuralArg"};
static const lean_object* l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "TerminationMeasure.structuralArg: body not one of the parameters"};
static const lean_object* l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_structuralArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_TerminationMeasure_structuralArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "assertion violation: measure.structural\n  "};
static const lean_object* l_Lean_Elab_TerminationMeasure_structuralArg___closed__0 = (const lean_object*)&l_Lean_Elab_TerminationMeasure_structuralArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_TerminationMeasure_structuralArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_TerminationMeasure_structuralArg___closed__1;
static const lean_closure_object l_Lean_Elab_TerminationMeasure_structuralArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_TerminationMeasure_structuralArg___closed__2 = (const lean_object*)&l_Lean_Elab_TerminationMeasure_structuralArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_structuralArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_structuralArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__0_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__1_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__2_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__3 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__3_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4_value_aux_0),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4_value_aux_1),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4_value_aux_2),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__0_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "terminationBy"};
static const lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__2_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3_value_aux_0),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(20, 221, 175, 114, 26, 111, 13, 165)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "termination_by"};
static const lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__4_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__5_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__6 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7;
static const lean_string_object l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__8 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__8_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structural"};
static const lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__9 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__9_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Array_map__unattach_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Array_map__unattach_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_TerminationMeasure_delab___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_TerminationMeasure_delab___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_TerminationMeasure_delab___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_delab___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_delab___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_delab___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_box(0);
v___x_5_ = ((lean_object*)(l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__1));
v___x_6_ = l_Lean_Expr_const___override(v___x_5_, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__3(void){
_start:
{
lean_object* v___x_7_; uint8_t v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_7_ = lean_obj_once(&l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__2, &l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__2_once, _init_l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__2);
v___x_8_ = 0;
v___x_9_ = lean_box(0);
v___x_10_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_10_, 0, v___x_9_);
lean_ctor_set(v___x_10_, 1, v___x_7_);
lean_ctor_set_uint8(v___x_10_, sizeof(void*)*2, v___x_8_);
return v___x_10_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTerminationMeasure_default(void){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_obj_once(&l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__3, &l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__3_once, _init_l_Lean_Elab_instInhabitedTerminationMeasure_default___closed__3);
return v___x_11_;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTerminationMeasure(void){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = l_Lean_Elab_instInhabitedTerminationMeasure_default;
return v___x_12_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__1(void){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__0));
v___x_15_ = l_Lean_stringToMessageData(v___x_14_);
return v___x_15_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__4(void){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_19_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__3));
v___x_20_ = l_Lean_MessageData_ofFormat(v___x_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters(lean_object* v_a_21_){
_start:
{
lean_object* v___x_22_; uint8_t v___x_23_; 
v___x_22_ = lean_unsigned_to_nat(1u);
v___x_23_ = lean_nat_dec_eq(v_a_21_, v___x_22_);
if (v___x_23_ == 0)
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_24_ = l_Nat_reprFast(v_a_21_);
v___x_25_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_25_, 0, v___x_24_);
v___x_26_ = l_Lean_MessageData_ofFormat(v___x_25_);
v___x_27_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__1, &l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__1);
v___x_28_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_28_, 0, v___x_26_);
lean_ctor_set(v___x_28_, 1, v___x_27_);
return v___x_28_;
}
else
{
lean_object* v___x_29_; 
lean_dec(v_a_21_);
v___x_29_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__4, &l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters___closed__4);
return v___x_29_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___redArg___lam__0(lean_object* v_k_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v_b_33_, lean_object* v_c_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_){
_start:
{
lean_object* v___x_40_; 
lean_inc(v___y_38_);
lean_inc_ref(v___y_37_);
lean_inc(v___y_36_);
lean_inc_ref(v___y_35_);
lean_inc(v___y_32_);
lean_inc_ref(v___y_31_);
v___x_40_ = lean_apply_9(v_k_30_, v_b_33_, v_c_34_, v___y_31_, v___y_32_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, lean_box(0));
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___redArg___lam__0___boxed(lean_object* v_k_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v_b_44_, lean_object* v_c_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___redArg___lam__0(v_k_41_, v___y_42_, v___y_43_, v_b_44_, v_c_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_);
lean_dec(v___y_49_);
lean_dec_ref(v___y_48_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___redArg(lean_object* v_type_52_, lean_object* v_maxFVars_x3f_53_, lean_object* v_k_54_, uint8_t v_cleanupAnnotations_55_, uint8_t v_whnfType_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_){
_start:
{
lean_object* v___f_64_; lean_object* v___x_65_; 
lean_inc(v___y_58_);
lean_inc_ref(v___y_57_);
v___f_64_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_64_, 0, v_k_54_);
lean_closure_set(v___f_64_, 1, v___y_57_);
lean_closure_set(v___f_64_, 2, v___y_58_);
v___x_65_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_52_, v_maxFVars_x3f_53_, v___f_64_, v_cleanupAnnotations_55_, v_whnfType_56_, v___y_59_, v___y_60_, v___y_61_, v___y_62_);
if (lean_obj_tag(v___x_65_) == 0)
{
return v___x_65_;
}
else
{
lean_object* v_a_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_73_; 
v_a_66_ = lean_ctor_get(v___x_65_, 0);
v_isSharedCheck_73_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_73_ == 0)
{
v___x_68_ = v___x_65_;
v_isShared_69_ = v_isSharedCheck_73_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_a_66_);
lean_dec(v___x_65_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_73_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
lean_object* v___x_71_; 
if (v_isShared_69_ == 0)
{
v___x_71_ = v___x_68_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v_a_66_);
v___x_71_ = v_reuseFailAlloc_72_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
return v___x_71_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___redArg___boxed(lean_object* v_type_74_, lean_object* v_maxFVars_x3f_75_, lean_object* v_k_76_, lean_object* v_cleanupAnnotations_77_, lean_object* v_whnfType_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_86_; uint8_t v_whnfType_boxed_87_; lean_object* v_res_88_; 
v_cleanupAnnotations_boxed_86_ = lean_unbox(v_cleanupAnnotations_77_);
v_whnfType_boxed_87_ = lean_unbox(v_whnfType_78_);
v_res_88_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___redArg(v_type_74_, v_maxFVars_x3f_75_, v_k_76_, v_cleanupAnnotations_boxed_86_, v_whnfType_boxed_87_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0(lean_object* v_00_u03b1_89_, lean_object* v_type_90_, lean_object* v_maxFVars_x3f_91_, lean_object* v_k_92_, uint8_t v_cleanupAnnotations_93_, uint8_t v_whnfType_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___redArg(v_type_90_, v_maxFVars_x3f_91_, v_k_92_, v_cleanupAnnotations_93_, v_whnfType_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___boxed(lean_object* v_00_u03b1_103_, lean_object* v_type_104_, lean_object* v_maxFVars_x3f_105_, lean_object* v_k_106_, lean_object* v_cleanupAnnotations_107_, lean_object* v_whnfType_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_116_; uint8_t v_whnfType_boxed_117_; lean_object* v_res_118_; 
v_cleanupAnnotations_boxed_116_ = lean_unbox(v_cleanupAnnotations_107_);
v_whnfType_boxed_117_ = lean_unbox(v_whnfType_108_);
v_res_118_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0(v_00_u03b1_103_, v_type_104_, v_maxFVars_x3f_105_, v_k_106_, v_cleanupAnnotations_boxed_116_, v_whnfType_boxed_117_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__1(lean_object* v_msg_119_){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = l_Lean_instInhabitedExpr;
v___x_121_ = lean_panic_fn_borrowed(v___x_120_, v_msg_119_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_TerminationMeasure_elab_spec__5___redArg(lean_object* v_a_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_TerminationMeasure_elab_spec__5___redArg___boxed(lean_object* v_a_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_TerminationMeasure_elab_spec__5___redArg(v_a_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_TerminationMeasure_elab_spec__5(lean_object* v_00_u03b1_140_, lean_object* v_a_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_TerminationMeasure_elab_spec__5___boxed(lean_object* v_00_u03b1_150_, lean_object* v_a_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_TerminationMeasure_elab_spec__5(v_00_u03b1_150_, v_a_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_);
lean_dec(v___y_157_);
lean_dec_ref(v___y_156_);
lean_dec(v___y_155_);
lean_dec_ref(v___y_154_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_152_);
return v_res_159_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6___closed__0(void){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_Lean_Elab_Term_instInhabitedTermElabM___redArg();
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6(lean_object* v_msg_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v___x_169_; lean_object* v___x_3202__overap_170_; lean_object* v___x_171_; 
v___x_169_ = lean_obj_once(&l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6___closed__0, &l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6___closed__0_once, _init_l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6___closed__0);
v___x_3202__overap_170_ = lean_panic_fn_borrowed(v___x_169_, v_msg_161_);
lean_inc(v___y_167_);
lean_inc_ref(v___y_166_);
lean_inc(v___y_165_);
lean_inc_ref(v___y_164_);
lean_inc(v___y_163_);
lean_inc_ref(v___y_162_);
v___x_171_ = lean_apply_7(v___x_3202__overap_170_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, lean_box(0));
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6___boxed(lean_object* v_msg_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6(v_msg_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__0(lean_object* v_ys_181_, lean_object* v_xs_182_, lean_object* v_a_183_, uint8_t v___x_184_, lean_object* v_zs_185_, lean_object* v_x_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; uint8_t v___x_197_; lean_object* v___x_198_; 
v___x_194_ = l_Array_append___redArg(v_ys_181_, v_xs_182_);
v___x_195_ = l_Array_append___redArg(v___x_194_, v_zs_185_);
v___x_196_ = 0;
v___x_197_ = 1;
v___x_198_ = l_Lean_Meta_mkLambdaFVars(v___x_195_, v_a_183_, v___x_196_, v___x_184_, v___x_196_, v___x_184_, v___x_197_, v___y_189_, v___y_190_, v___y_191_, v___y_192_);
lean_dec_ref(v___x_195_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__0___boxed(lean_object* v_ys_199_, lean_object* v_xs_200_, lean_object* v_a_201_, lean_object* v___x_202_, lean_object* v_zs_203_, lean_object* v_x_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
uint8_t v___x_5555__boxed_212_; lean_object* v_res_213_; 
v___x_5555__boxed_212_ = lean_unbox(v___x_202_);
v_res_213_ = l_Lean_Elab_TerminationMeasure_elab___lam__0(v_ys_199_, v_xs_200_, v_a_201_, v___x_5555__boxed_212_, v_zs_203_, v_x_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
lean_dec_ref(v_x_204_);
lean_dec_ref(v_zs_203_);
lean_dec_ref(v_xs_200_);
return v_res_213_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__0(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = lean_box(1);
v___x_215_ = l_Lean_MessageData_ofFormat(v___x_214_);
return v___x_215_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__3(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__2));
v___x_220_ = l_Lean_MessageData_ofFormat(v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11(lean_object* v_x_221_, lean_object* v_x_222_){
_start:
{
if (lean_obj_tag(v_x_222_) == 0)
{
return v_x_221_;
}
else
{
lean_object* v_head_223_; lean_object* v_tail_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_246_; 
v_head_223_ = lean_ctor_get(v_x_222_, 0);
v_tail_224_ = lean_ctor_get(v_x_222_, 1);
v_isSharedCheck_246_ = !lean_is_exclusive(v_x_222_);
if (v_isSharedCheck_246_ == 0)
{
v___x_226_ = v_x_222_;
v_isShared_227_ = v_isSharedCheck_246_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_tail_224_);
lean_inc(v_head_223_);
lean_dec(v_x_222_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_246_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v_before_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_244_; 
v_before_228_ = lean_ctor_get(v_head_223_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v_head_223_);
if (v_isSharedCheck_244_ == 0)
{
lean_object* v_unused_245_; 
v_unused_245_ = lean_ctor_get(v_head_223_, 1);
lean_dec(v_unused_245_);
v___x_230_ = v_head_223_;
v_isShared_231_ = v_isSharedCheck_244_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_before_228_);
lean_dec(v_head_223_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_244_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_232_; lean_object* v___x_234_; 
v___x_232_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__0);
if (v_isShared_231_ == 0)
{
lean_ctor_set_tag(v___x_230_, 7);
lean_ctor_set(v___x_230_, 1, v___x_232_);
lean_ctor_set(v___x_230_, 0, v_x_221_);
v___x_234_ = v___x_230_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_x_221_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v___x_232_);
v___x_234_ = v_reuseFailAlloc_243_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
lean_object* v___x_235_; lean_object* v___x_237_; 
v___x_235_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__3);
if (v_isShared_227_ == 0)
{
lean_ctor_set_tag(v___x_226_, 7);
lean_ctor_set(v___x_226_, 1, v___x_235_);
lean_ctor_set(v___x_226_, 0, v___x_234_);
v___x_237_ = v___x_226_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v___x_235_);
v___x_237_ = v_reuseFailAlloc_242_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_238_ = l_Lean_MessageData_ofSyntax(v_before_228_);
v___x_239_ = l_Lean_indentD(v___x_238_);
v___x_240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_237_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
v_x_221_ = v___x_240_;
v_x_222_ = v_tail_224_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__10(lean_object* v_opts_247_, lean_object* v_opt_248_){
_start:
{
lean_object* v_name_249_; lean_object* v_defValue_250_; lean_object* v_map_251_; lean_object* v___x_252_; 
v_name_249_ = lean_ctor_get(v_opt_248_, 0);
v_defValue_250_ = lean_ctor_get(v_opt_248_, 1);
v_map_251_ = lean_ctor_get(v_opts_247_, 0);
v___x_252_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_251_, v_name_249_);
if (lean_obj_tag(v___x_252_) == 0)
{
uint8_t v___x_253_; 
v___x_253_ = lean_unbox(v_defValue_250_);
return v___x_253_;
}
else
{
lean_object* v_val_254_; 
v_val_254_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_val_254_);
lean_dec_ref_known(v___x_252_, 1);
if (lean_obj_tag(v_val_254_) == 1)
{
uint8_t v_v_255_; 
v_v_255_ = lean_ctor_get_uint8(v_val_254_, 0);
lean_dec_ref_known(v_val_254_, 0);
return v_v_255_;
}
else
{
uint8_t v___x_256_; 
lean_dec(v_val_254_);
v___x_256_ = lean_unbox(v_defValue_250_);
return v___x_256_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__10___boxed(lean_object* v_opts_257_, lean_object* v_opt_258_){
_start:
{
uint8_t v_res_259_; lean_object* v_r_260_; 
v_res_259_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__10(v_opts_257_, v_opt_258_);
lean_dec_ref(v_opt_258_);
lean_dec_ref(v_opts_257_);
v_r_260_ = lean_box(v_res_259_);
return v_r_260_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg___closed__1));
v___x_265_ = l_Lean_MessageData_ofFormat(v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg(lean_object* v_msgData_266_, lean_object* v_macroStack_267_, lean_object* v___y_268_){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_270_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_268_);
v___x_271_ = l_Lean_Elab_pp_macroStack;
v___x_272_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__10(v___x_270_, v___x_271_);
lean_dec_ref(v___x_270_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; 
lean_dec(v_macroStack_267_);
v___x_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_273_, 0, v_msgData_266_);
return v___x_273_;
}
else
{
if (lean_obj_tag(v_macroStack_267_) == 0)
{
lean_object* v___x_274_; 
v___x_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_274_, 0, v_msgData_266_);
return v___x_274_;
}
else
{
lean_object* v_head_275_; lean_object* v_after_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_291_; 
v_head_275_ = lean_ctor_get(v_macroStack_267_, 0);
lean_inc(v_head_275_);
v_after_276_ = lean_ctor_get(v_head_275_, 1);
v_isSharedCheck_291_ = !lean_is_exclusive(v_head_275_);
if (v_isSharedCheck_291_ == 0)
{
lean_object* v_unused_292_; 
v_unused_292_ = lean_ctor_get(v_head_275_, 0);
lean_dec(v_unused_292_);
v___x_278_ = v_head_275_;
v_isShared_279_ = v_isSharedCheck_291_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_after_276_);
lean_dec(v_head_275_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_291_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_280_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__0);
if (v_isShared_279_ == 0)
{
lean_ctor_set_tag(v___x_278_, 7);
lean_ctor_set(v___x_278_, 1, v___x_280_);
lean_ctor_set(v___x_278_, 0, v_msgData_266_);
v___x_282_ = v___x_278_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_msgData_266_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v___x_280_);
v___x_282_ = v_reuseFailAlloc_290_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v_msgData_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_283_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg___closed__2);
v___x_284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_282_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
v___x_285_ = l_Lean_MessageData_ofSyntax(v_after_276_);
v___x_286_ = l_Lean_indentD(v___x_285_);
v_msgData_287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_287_, 0, v___x_284_);
lean_ctor_set(v_msgData_287_, 1, v___x_286_);
v___x_288_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11(v_msgData_287_, v_macroStack_267_);
v___x_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
return v___x_289_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg___boxed(lean_object* v_msgData_293_, lean_object* v_macroStack_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg(v_msgData_293_, v_macroStack_294_, v___y_295_);
lean_dec_ref(v___y_295_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__8(lean_object* v_msgData_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v___x_304_; lean_object* v_env_305_; uint8_t v___x_306_; lean_object* v_env_307_; lean_object* v___x_308_; lean_object* v_toCold_309_; lean_object* v_mctx_310_; lean_object* v_lctx_311_; lean_object* v_options_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_304_ = lean_st_ref_get(v___y_302_);
v_env_305_ = lean_ctor_get(v___x_304_, 0);
lean_inc_ref(v_env_305_);
lean_dec(v___x_304_);
v___x_306_ = 0;
v_env_307_ = l_Lean_Environment_setRecordingDeps(v_env_305_, v___x_306_);
v___x_308_ = lean_st_ref_get(v___y_300_);
v_toCold_309_ = lean_ctor_get(v___y_301_, 0);
v_mctx_310_ = lean_ctor_get(v___x_308_, 0);
lean_inc_ref(v_mctx_310_);
lean_dec(v___x_308_);
v_lctx_311_ = lean_ctor_get(v___y_299_, 2);
v_options_312_ = lean_ctor_get(v_toCold_309_, 2);
lean_inc_ref(v_options_312_);
lean_inc_ref(v_lctx_311_);
v___x_313_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_313_, 0, v_env_307_);
lean_ctor_set(v___x_313_, 1, v_mctx_310_);
lean_ctor_set(v___x_313_, 2, v_lctx_311_);
lean_ctor_set(v___x_313_, 3, v_options_312_);
v___x_314_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
lean_ctor_set(v___x_314_, 1, v_msgData_298_);
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__8___boxed(lean_object* v_msgData_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__8(v_msgData_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5___redArg(lean_object* v_msg_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v_ref_331_; lean_object* v_macroStack_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v_a_335_; lean_object* v___x_336_; lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_345_; 
v_ref_331_ = lean_ctor_get(v___y_328_, 2);
v_macroStack_332_ = lean_ctor_get(v___y_324_, 1);
v___x_333_ = l_Lean_Elab_getBetterRef(v_ref_331_, v_macroStack_332_);
v___x_334_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__8(v_msg_323_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
v_a_335_ = lean_ctor_get(v___x_334_, 0);
lean_inc(v_a_335_);
lean_dec_ref(v___x_334_);
lean_inc(v_macroStack_332_);
v___x_336_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg(v_a_335_, v_macroStack_332_, v___y_328_);
v_a_337_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_345_ == 0)
{
v___x_339_ = v___x_336_;
v_isShared_340_ = v_isSharedCheck_345_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_336_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_345_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_341_; lean_object* v___x_343_; 
v___x_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_333_);
lean_ctor_set(v___x_341_, 1, v_a_337_);
if (v_isShared_340_ == 0)
{
lean_ctor_set_tag(v___x_339_, 1);
lean_ctor_set(v___x_339_, 0, v___x_341_);
v___x_343_ = v___x_339_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_341_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5___redArg___boxed(lean_object* v_msg_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5___redArg(v_msg_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
lean_dec(v___y_348_);
lean_dec_ref(v___y_347_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___redArg(lean_object* v_ref_355_, lean_object* v_msg_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v_toCold_364_; lean_object* v_currRecDepth_365_; lean_object* v_ref_366_; uint16_t v_optionFlags_367_; uint8_t v_suppressElabErrors_368_; uint8_t v_checkDeprecated_369_; uint8_t v_isRecordingDeps_370_; lean_object* v_ref_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v_toCold_364_ = lean_ctor_get(v___y_361_, 0);
v_currRecDepth_365_ = lean_ctor_get(v___y_361_, 1);
v_ref_366_ = lean_ctor_get(v___y_361_, 2);
v_optionFlags_367_ = lean_ctor_get_uint16(v___y_361_, sizeof(void*)*3);
v_suppressElabErrors_368_ = lean_ctor_get_uint8(v___y_361_, sizeof(void*)*3 + 2);
v_checkDeprecated_369_ = lean_ctor_get_uint8(v___y_361_, sizeof(void*)*3 + 3);
v_isRecordingDeps_370_ = lean_ctor_get_uint8(v___y_361_, sizeof(void*)*3 + 4);
v_ref_371_ = l_Lean_replaceRef(v_ref_355_, v_ref_366_);
lean_inc(v_currRecDepth_365_);
lean_inc_ref(v_toCold_364_);
v___x_372_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_372_, 0, v_toCold_364_);
lean_ctor_set(v___x_372_, 1, v_currRecDepth_365_);
lean_ctor_set(v___x_372_, 2, v_ref_371_);
lean_ctor_set_uint16(v___x_372_, sizeof(void*)*3, v_optionFlags_367_);
lean_ctor_set_uint8(v___x_372_, sizeof(void*)*3 + 2, v_suppressElabErrors_368_);
lean_ctor_set_uint8(v___x_372_, sizeof(void*)*3 + 3, v_checkDeprecated_369_);
lean_ctor_set_uint8(v___x_372_, sizeof(void*)*3 + 4, v_isRecordingDeps_370_);
v___x_373_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5___redArg(v_msg_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___x_372_, v___y_362_);
lean_dec_ref_known(v___x_372_, 3);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___redArg___boxed(lean_object* v_ref_374_, lean_object* v_msg_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___redArg(v_ref_374_, v_msg_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v_ref_374_);
return v_res_383_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2_spec__2(lean_object* v_a_384_, lean_object* v_as_385_, size_t v_i_386_, size_t v_stop_387_){
_start:
{
uint8_t v___x_388_; 
v___x_388_ = lean_usize_dec_eq(v_i_386_, v_stop_387_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_389_ = lean_array_uget_borrowed(v_as_385_, v_i_386_);
v___x_390_ = lean_expr_eqv(v_a_384_, v___x_389_);
if (v___x_390_ == 0)
{
size_t v___x_391_; size_t v___x_392_; 
v___x_391_ = ((size_t)1ULL);
v___x_392_ = lean_usize_add(v_i_386_, v___x_391_);
v_i_386_ = v___x_392_;
goto _start;
}
else
{
return v___x_390_;
}
}
else
{
uint8_t v___x_394_; 
v___x_394_ = 0;
return v___x_394_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2_spec__2___boxed(lean_object* v_a_395_, lean_object* v_as_396_, lean_object* v_i_397_, lean_object* v_stop_398_){
_start:
{
size_t v_i_boxed_399_; size_t v_stop_boxed_400_; uint8_t v_res_401_; lean_object* v_r_402_; 
v_i_boxed_399_ = lean_unbox_usize(v_i_397_);
lean_dec(v_i_397_);
v_stop_boxed_400_ = lean_unbox_usize(v_stop_398_);
lean_dec(v_stop_398_);
v_res_401_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2_spec__2(v_a_395_, v_as_396_, v_i_boxed_399_, v_stop_boxed_400_);
lean_dec_ref(v_as_396_);
lean_dec_ref(v_a_395_);
v_r_402_ = lean_box(v_res_401_);
return v_r_402_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2(lean_object* v_as_403_, lean_object* v_a_404_){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_405_ = lean_unsigned_to_nat(0u);
v___x_406_ = lean_array_get_size(v_as_403_);
v___x_407_ = lean_nat_dec_lt(v___x_405_, v___x_406_);
if (v___x_407_ == 0)
{
return v___x_407_;
}
else
{
size_t v___x_408_; size_t v___x_409_; uint8_t v___x_410_; 
v___x_408_ = ((size_t)0ULL);
v___x_409_ = lean_usize_of_nat(v___x_406_);
v___x_410_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2_spec__2(v_a_404_, v_as_403_, v___x_408_, v___x_409_);
return v___x_410_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2___boxed(lean_object* v_as_411_, lean_object* v_a_412_){
_start:
{
uint8_t v_res_413_; lean_object* v_r_414_; 
v_res_413_ = l_Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2(v_as_411_, v_a_412_);
lean_dec_ref(v_a_412_);
lean_dec_ref(v_as_411_);
v_r_414_ = lean_box(v_res_413_);
return v_r_414_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3___closed__1(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3___closed__0));
v___x_417_ = l_Lean_stringToMessageData(v___x_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3(lean_object* v_a_418_, lean_object* v_a_419_){
_start:
{
if (lean_obj_tag(v_a_418_) == 0)
{
lean_object* v___x_420_; 
v___x_420_ = l_List_reverse___redArg(v_a_419_);
return v___x_420_;
}
else
{
lean_object* v_head_421_; lean_object* v_tail_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_434_; 
v_head_421_ = lean_ctor_get(v_a_418_, 0);
v_tail_422_ = lean_ctor_get(v_a_418_, 1);
v_isSharedCheck_434_ = !lean_is_exclusive(v_a_418_);
if (v_isSharedCheck_434_ == 0)
{
v___x_424_ = v_a_418_;
v_isShared_425_ = v_isSharedCheck_434_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_tail_422_);
lean_inc(v_head_421_);
lean_dec(v_a_418_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_434_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_426_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3___closed__1, &l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3___closed__1);
v___x_427_ = l_Lean_MessageData_ofExpr(v_head_421_);
v___x_428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_426_);
lean_ctor_set(v___x_428_, 1, v___x_427_);
v___x_429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
lean_ctor_set(v___x_429_, 1, v___x_426_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 1, v_a_419_);
lean_ctor_set(v___x_424_, 0, v___x_429_);
v___x_431_ = v___x_424_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_429_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_a_419_);
v___x_431_ = v_reuseFailAlloc_433_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
v_a_418_ = v_tail_422_;
v_a_419_ = v___x_431_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__3(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_438_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__2));
v___x_439_ = lean_unsigned_to_nat(14u);
v___x_440_ = lean_unsigned_to_nat(22u);
v___x_441_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__1));
v___x_442_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__0));
v___x_443_ = l_mkPanicMessageWithDecl(v___x_442_, v___x_441_, v___x_440_, v___x_439_, v___x_438_);
return v___x_443_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__5(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__4));
v___x_446_ = l_Lean_stringToMessageData(v___x_445_);
return v___x_446_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__7(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__6));
v___x_449_ = l_Lean_stringToMessageData(v___x_448_);
return v___x_449_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__9(void){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_451_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__8));
v___x_452_ = l_Lean_stringToMessageData(v___x_451_);
return v___x_452_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__11(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__10));
v___x_455_ = l_Lean_stringToMessageData(v___x_454_);
return v___x_455_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__13(void){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__12));
v___x_458_ = l_Lean_stringToMessageData(v___x_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__1(lean_object* v_body_459_, uint8_t v___x_460_, lean_object* v_ys_461_, lean_object* v_vars_462_, lean_object* v_extraParams_463_, uint8_t v_structural_464_, lean_object* v_ref_465_, lean_object* v_xs_466_, lean_object* v_type_x27_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; uint8_t v___x_479_; lean_object* v___x_480_; 
v___x_475_ = lean_box(0);
v___x_476_ = lean_box(v___x_460_);
v___x_477_ = lean_box(v___x_460_);
v___x_478_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_478_, 0, v_body_459_);
lean_closure_set(v___x_478_, 1, v___x_475_);
lean_closure_set(v___x_478_, 2, v___x_476_);
lean_closure_set(v___x_478_, 3, v___x_477_);
lean_closure_set(v___x_478_, 4, v___x_475_);
v___x_479_ = 1;
v___x_480_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_478_, v___x_479_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_539_; 
v_a_481_ = lean_ctor_get(v___x_480_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_539_ == 0)
{
v___x_483_ = v___x_480_;
v_isShared_484_ = v_isSharedCheck_539_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_480_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_539_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; lean_object* v___f_486_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v___y_494_; lean_object* v___y_503_; lean_object* v___y_504_; lean_object* v___y_505_; lean_object* v___y_506_; lean_object* v___y_507_; lean_object* v___y_508_; 
v___x_485_ = lean_box(v___x_460_);
lean_inc(v_a_481_);
lean_inc_ref(v_xs_466_);
lean_inc_ref(v_ys_461_);
v___f_486_ = lean_alloc_closure((void*)(l_Lean_Elab_TerminationMeasure_elab___lam__0___boxed), 13, 4);
lean_closure_set(v___f_486_, 0, v_ys_461_);
lean_closure_set(v___f_486_, 1, v_xs_466_);
lean_closure_set(v___f_486_, 2, v_a_481_);
lean_closure_set(v___f_486_, 3, v___x_485_);
if (v_structural_464_ == 0)
{
lean_dec(v_a_481_);
lean_dec_ref(v_xs_466_);
lean_dec_ref(v_ys_461_);
v___y_503_ = v___y_468_;
v___y_504_ = v___y_469_;
v___y_505_ = v___y_470_;
v___y_506_ = v___y_471_;
v___y_507_ = v___y_472_;
v___y_508_ = v___y_473_;
goto v___jp_502_;
}
else
{
lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_512_ = l_Array_append___redArg(v_ys_461_, v_xs_466_);
lean_dec_ref(v_xs_466_);
v___x_513_ = l_Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2(v___x_512_, v_a_481_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
lean_dec_ref(v___f_486_);
lean_del_object(v___x_483_);
lean_dec(v_type_x27_467_);
v___x_514_ = lean_array_to_list(v___x_512_);
v___x_515_ = lean_box(0);
v___x_516_ = l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3(v___x_514_, v___x_515_);
v___x_517_ = l_Lean_MessageData_andList(v___x_516_);
v___x_518_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__5, &l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__5_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__5);
v___x_519_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__7, &l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__7_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__7);
v___x_520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
lean_ctor_set(v___x_520_, 1, v___x_517_);
v___x_521_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__9, &l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__9_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__9);
v___x_522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_520_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
v___x_523_ = l_Lean_indentExpr(v_a_481_);
v___x_524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_522_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
v___x_525_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__11, &l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__11_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__11);
v___x_526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_524_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_518_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v___x_528_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__13, &l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__13_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__13);
v___x_529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_527_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
v___x_530_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___redArg(v_ref_465_, v___x_529_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
v_a_531_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_530_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_530_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_531_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
else
{
lean_dec_ref(v___x_512_);
lean_dec(v_a_481_);
v___y_503_ = v___y_468_;
v___y_504_ = v___y_469_;
v___y_505_ = v___y_470_;
v___y_506_ = v___y_471_;
v___y_507_ = v___y_472_;
v___y_508_ = v___y_473_;
goto v___jp_502_;
}
}
v___jp_487_:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_498_; 
v___x_495_ = lean_array_get_size(v_vars_462_);
v___x_496_ = lean_nat_sub(v_extraParams_463_, v___x_495_);
if (v_isShared_484_ == 0)
{
lean_ctor_set_tag(v___x_483_, 1);
lean_ctor_set(v___x_483_, 0, v___x_496_);
v___x_498_ = v___x_483_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_496_);
v___x_498_ = v_reuseFailAlloc_501_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
uint8_t v___x_499_; lean_object* v___x_500_; 
v___x_499_ = 0;
v___x_500_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___redArg(v___y_494_, v___x_498_, v___f_486_, v___x_499_, v___x_499_, v___y_493_, v___y_492_, v___y_488_, v___y_491_, v___y_489_, v___y_490_);
return v___x_500_;
}
}
v___jp_502_:
{
if (lean_obj_tag(v_type_x27_467_) == 0)
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__3, &l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__3_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__3);
v___x_510_ = l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__1(v___x_509_);
v___y_488_ = v___y_505_;
v___y_489_ = v___y_507_;
v___y_490_ = v___y_508_;
v___y_491_ = v___y_506_;
v___y_492_ = v___y_504_;
v___y_493_ = v___y_503_;
v___y_494_ = v___x_510_;
goto v___jp_487_;
}
else
{
lean_object* v_val_511_; 
v_val_511_ = lean_ctor_get(v_type_x27_467_, 0);
lean_inc(v_val_511_);
lean_dec_ref_known(v_type_x27_467_, 1);
v___y_488_ = v___y_505_;
v___y_489_ = v___y_507_;
v___y_490_ = v___y_508_;
v___y_491_ = v___y_506_;
v___y_492_ = v___y_504_;
v___y_493_ = v___y_503_;
v___y_494_ = v_val_511_;
goto v___jp_487_;
}
}
}
}
else
{
lean_dec(v_type_x27_467_);
lean_dec_ref(v_xs_466_);
lean_dec_ref(v_ys_461_);
return v___x_480_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__1___boxed(lean_object* v_body_540_, lean_object* v___x_541_, lean_object* v_ys_542_, lean_object* v_vars_543_, lean_object* v_extraParams_544_, lean_object* v_structural_545_, lean_object* v_ref_546_, lean_object* v_xs_547_, lean_object* v_type_x27_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
uint8_t v___x_5958__boxed_556_; uint8_t v_structural_boxed_557_; lean_object* v_res_558_; 
v___x_5958__boxed_556_ = lean_unbox(v___x_541_);
v_structural_boxed_557_ = lean_unbox(v_structural_545_);
v_res_558_ = l_Lean_Elab_TerminationMeasure_elab___lam__1(v_body_540_, v___x_5958__boxed_556_, v_ys_542_, v_vars_543_, v_extraParams_544_, v_structural_boxed_557_, v_ref_546_, v_xs_547_, v_type_x27_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v_ref_546_);
lean_dec(v_extraParams_544_);
lean_dec_ref(v_vars_543_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__2(lean_object* v_hint_559_, uint8_t v___x_560_, lean_object* v_extraParams_561_, lean_object* v_ys_562_, lean_object* v_type_x27_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v_ref_571_; uint8_t v_structural_572_; lean_object* v_vars_573_; lean_object* v_body_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___f_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v_ref_571_ = lean_ctor_get(v_hint_559_, 0);
lean_inc(v_ref_571_);
v_structural_572_ = lean_ctor_get_uint8(v_hint_559_, sizeof(void*)*3);
v_vars_573_ = lean_ctor_get(v_hint_559_, 1);
lean_inc_ref_n(v_vars_573_, 2);
v_body_574_ = lean_ctor_get(v_hint_559_, 2);
lean_inc(v_body_574_);
lean_dec_ref(v_hint_559_);
v___x_575_ = lean_box(v___x_560_);
v___x_576_ = lean_box(v_structural_572_);
v___f_577_ = lean_alloc_closure((void*)(l_Lean_Elab_TerminationMeasure_elab___lam__1___boxed), 16, 7);
lean_closure_set(v___f_577_, 0, v_body_574_);
lean_closure_set(v___f_577_, 1, v___x_575_);
lean_closure_set(v___f_577_, 2, v_ys_562_);
lean_closure_set(v___f_577_, 3, v_vars_573_);
lean_closure_set(v___f_577_, 4, v_extraParams_561_);
lean_closure_set(v___f_577_, 5, v___x_576_);
lean_closure_set(v___f_577_, 6, v_ref_571_);
v___x_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_578_, 0, v_type_x27_563_);
v___x_579_ = l_Lean_Elab_Term_elabFunBinders___redArg(v_vars_573_, v___x_578_, v___f_577_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
lean_dec_ref(v_vars_573_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__2___boxed(lean_object* v_hint_580_, lean_object* v___x_581_, lean_object* v_extraParams_582_, lean_object* v_ys_583_, lean_object* v_type_x27_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
uint8_t v___x_6138__boxed_592_; lean_object* v_res_593_; 
v___x_6138__boxed_592_ = lean_unbox(v___x_581_);
v_res_593_ = l_Lean_Elab_TerminationMeasure_elab___lam__2(v_hint_580_, v___x_6138__boxed_592_, v_extraParams_582_, v_ys_583_, v_type_x27_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
return v_res_593_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__3(void){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_597_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__2));
v___x_598_ = lean_unsigned_to_nat(2u);
v___x_599_ = lean_unsigned_to_nat(54u);
v___x_600_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__1));
v___x_601_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__0));
v___x_602_ = l_mkPanicMessageWithDecl(v___x_601_, v___x_600_, v___x_599_, v___x_598_, v___x_597_);
return v___x_602_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__5(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__4));
v___x_605_ = l_Lean_stringToMessageData(v___x_604_);
return v___x_605_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__7(void){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__6));
v___x_608_ = l_Lean_stringToMessageData(v___x_607_);
return v___x_608_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__9(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__8));
v___x_611_ = l_Lean_stringToMessageData(v___x_610_);
return v___x_611_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__13(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__12));
v___x_617_ = l_Lean_stringToMessageData(v___x_616_);
return v___x_617_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__16(void){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__15));
v___x_622_ = l_Lean_MessageData_ofFormat(v___x_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__3(uint8_t v___x_623_, lean_object* v_hint_624_, lean_object* v_arity_625_, lean_object* v_extraParams_626_, lean_object* v_type_627_, lean_object* v___f_628_, lean_object* v_funName_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
if (v___x_623_ == 0)
{
lean_object* v___x_637_; lean_object* v___x_638_; 
lean_dec(v_funName_629_);
lean_dec_ref(v___f_628_);
lean_dec_ref(v_type_627_);
lean_dec(v_extraParams_626_);
v___x_637_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__3, &l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__3_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__3);
v___x_638_ = l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6(v___x_637_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
return v___x_638_;
}
else
{
lean_object* v_ref_639_; uint8_t v_structural_640_; lean_object* v_vars_641_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v_msg_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___x_701_; uint8_t v___x_702_; 
v_ref_639_ = lean_ctor_get(v_hint_624_, 0);
v_structural_640_ = lean_ctor_get_uint8(v_hint_624_, sizeof(void*)*3);
v_vars_641_ = lean_ctor_get(v_hint_624_, 1);
v___x_701_ = lean_array_get_size(v_vars_641_);
v___x_702_ = lean_nat_dec_lt(v_extraParams_626_, v___x_701_);
if (v___x_702_ == 0)
{
lean_dec(v_funName_629_);
v___y_643_ = v___y_630_;
v___y_644_ = v___y_631_;
v___y_645_ = v___y_632_;
v___y_646_ = v___y_633_;
v___y_647_ = v___y_634_;
v___y_648_ = v___y_635_;
goto v___jp_642_;
}
else
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v_msg_713_; lean_object* v___x_714_; lean_object* v_ident_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
lean_dec_ref(v___f_628_);
lean_dec_ref(v_type_627_);
v___x_703_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters(v___x_701_);
v___x_704_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__5, &l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__5_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__5);
v___x_705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_703_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
lean_inc(v_funName_629_);
v___x_706_ = l_Lean_MessageData_ofName(v_funName_629_);
v___x_707_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__7, &l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__7_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__7);
v___x_708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_708_, 0, v___x_706_);
lean_ctor_set(v___x_708_, 1, v___x_707_);
v___x_709_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters(v_extraParams_626_);
v___x_710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_708_);
lean_ctor_set(v___x_710_, 1, v___x_709_);
v___x_711_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__9, &l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__9_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__9);
v___x_712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_712_, 0, v___x_710_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
v_msg_713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_713_, 0, v___x_705_);
lean_ctor_set(v_msg_713_, 1, v___x_712_);
v___x_714_ = lean_unsigned_to_nat(0u);
v_ident_715_ = lean_array_fget_borrowed(v_vars_641_, v___x_714_);
v___x_716_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__11));
lean_inc(v_ident_715_);
v___x_717_ = l_Lean_Syntax_isOfKind(v_ident_715_, v___x_716_);
if (v___x_717_ == 0)
{
lean_dec(v_funName_629_);
v_msg_685_ = v_msg_713_;
v___y_686_ = v___y_630_;
v___y_687_ = v___y_631_;
v___y_688_ = v___y_632_;
v___y_689_ = v___y_633_;
v___y_690_ = v___y_634_;
v___y_691_ = v___y_635_;
goto v___jp_684_;
}
else
{
lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_718_ = l_Lean_TSyntax_getId(v_ident_715_);
v___x_719_ = l_Lean_Name_isSuffixOf(v___x_718_, v_funName_629_);
lean_dec(v_funName_629_);
lean_dec(v___x_718_);
if (v___x_719_ == 0)
{
v_msg_685_ = v_msg_713_;
v___y_686_ = v___y_630_;
v___y_687_ = v___y_631_;
v___y_688_ = v___y_632_;
v___y_689_ = v___y_633_;
v___y_690_ = v___y_634_;
v___y_691_ = v___y_635_;
goto v___jp_684_;
}
else
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v_msg_723_; 
v___x_720_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__13, &l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__13_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__13);
v___x_721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_721_, 0, v_msg_713_);
lean_ctor_set(v___x_721_, 1, v___x_720_);
v___x_722_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__16, &l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__16_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__16);
v_msg_723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_723_, 0, v___x_721_);
lean_ctor_set(v_msg_723_, 1, v___x_722_);
v_msg_685_ = v_msg_723_;
v___y_686_ = v___y_630_;
v___y_687_ = v___y_631_;
v___y_688_ = v___y_632_;
v___y_689_ = v___y_633_;
v___y_690_ = v___y_634_;
v___y_691_ = v___y_635_;
goto v___jp_684_;
}
}
}
v___jp_642_:
{
lean_object* v___x_649_; lean_object* v___x_650_; uint8_t v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_649_ = lean_nat_sub(v_arity_625_, v_extraParams_626_);
lean_dec(v_extraParams_626_);
v___x_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
v___x_651_ = 0;
v___x_652_ = lean_box(v___x_623_);
v___x_653_ = lean_box(v___x_651_);
v___x_654_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___boxed), 13, 6);
lean_closure_set(v___x_654_, 0, lean_box(0));
lean_closure_set(v___x_654_, 1, v_type_627_);
lean_closure_set(v___x_654_, 2, v___x_650_);
lean_closure_set(v___x_654_, 3, v___f_628_);
lean_closure_set(v___x_654_, 4, v___x_652_);
lean_closure_set(v___x_654_, 5, v___x_653_);
v___x_655_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_654_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; uint8_t v___x_657_; lean_object* v___x_658_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc_n(v_a_656_, 2);
lean_dec_ref_known(v___x_655_, 1);
v___x_657_ = 0;
v___x_658_ = l_Lean_Meta_check(v_a_656_, v___x_657_, v___y_645_, v___y_646_, v___y_647_, v___y_648_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_666_; 
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_666_ == 0)
{
lean_object* v_unused_667_; 
v_unused_667_ = lean_ctor_get(v___x_658_, 0);
lean_dec(v_unused_667_);
v___x_660_ = v___x_658_;
v_isShared_661_ = v_isSharedCheck_666_;
goto v_resetjp_659_;
}
else
{
lean_dec(v___x_658_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_666_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_662_; lean_object* v___x_664_; 
lean_inc(v_ref_639_);
v___x_662_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_662_, 0, v_ref_639_);
lean_ctor_set(v___x_662_, 1, v_a_656_);
lean_ctor_set_uint8(v___x_662_, sizeof(void*)*2, v_structural_640_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 0, v___x_662_);
v___x_664_ = v___x_660_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_662_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
else
{
lean_object* v_a_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_675_; 
lean_dec(v_a_656_);
v_a_668_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_675_ == 0)
{
v___x_670_ = v___x_658_;
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_a_668_);
lean_dec(v___x_658_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_673_; 
if (v_isShared_671_ == 0)
{
v___x_673_ = v___x_670_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_a_668_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
else
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_683_; 
v_a_676_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v___x_655_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_655_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_a_676_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
v___jp_684_:
{
lean_object* v___x_692_; lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_700_; 
v___x_692_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___redArg(v_ref_639_, v_msg_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
v_a_693_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_700_ == 0)
{
v___x_695_ = v___x_692_;
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_692_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_698_; 
if (v_isShared_696_ == 0)
{
v___x_698_ = v___x_695_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_693_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__3___boxed(lean_object* v___x_724_, lean_object* v_hint_725_, lean_object* v_arity_726_, lean_object* v_extraParams_727_, lean_object* v_type_728_, lean_object* v___f_729_, lean_object* v_funName_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
uint8_t v___x_6230__boxed_738_; lean_object* v_res_739_; 
v___x_6230__boxed_738_ = lean_unbox(v___x_724_);
v_res_739_ = l_Lean_Elab_TerminationMeasure_elab___lam__3(v___x_6230__boxed_738_, v_hint_725_, v_arity_726_, v_extraParams_727_, v_type_728_, v___f_729_, v_funName_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v_arity_726_);
lean_dec_ref(v_hint_725_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab(lean_object* v_funName_740_, lean_object* v_type_741_, lean_object* v_arity_742_, lean_object* v_extraParams_743_, lean_object* v_hint_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_){
_start:
{
uint8_t v___x_752_; lean_object* v___x_753_; lean_object* v___f_754_; lean_object* v___x_755_; lean_object* v___y_756_; lean_object* v___x_757_; 
v___x_752_ = lean_nat_dec_le(v_extraParams_743_, v_arity_742_);
v___x_753_ = lean_box(v___x_752_);
lean_inc(v_extraParams_743_);
lean_inc_ref(v_hint_744_);
v___f_754_ = lean_alloc_closure((void*)(l_Lean_Elab_TerminationMeasure_elab___lam__2___boxed), 12, 3);
lean_closure_set(v___f_754_, 0, v_hint_744_);
lean_closure_set(v___f_754_, 1, v___x_753_);
lean_closure_set(v___f_754_, 2, v_extraParams_743_);
v___x_755_ = lean_box(v___x_752_);
lean_inc(v_funName_740_);
v___y_756_ = lean_alloc_closure((void*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___boxed), 14, 7);
lean_closure_set(v___y_756_, 0, v___x_755_);
lean_closure_set(v___y_756_, 1, v_hint_744_);
lean_closure_set(v___y_756_, 2, v_arity_742_);
lean_closure_set(v___y_756_, 3, v_extraParams_743_);
lean_closure_set(v___y_756_, 4, v_type_741_);
lean_closure_set(v___y_756_, 5, v___f_754_);
lean_closure_set(v___y_756_, 6, v_funName_740_);
v___x_757_ = l_Lean_Elab_Term_withDeclName___redArg(v_funName_740_, v___y_756_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___boxed(lean_object* v_funName_758_, lean_object* v_type_759_, lean_object* v_arity_760_, lean_object* v_extraParams_761_, lean_object* v_hint_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_Elab_TerminationMeasure_elab(v_funName_758_, v_type_759_, v_arity_760_, v_extraParams_761_, v_hint_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_);
lean_dec(v_a_768_);
lean_dec_ref(v_a_767_);
lean_dec(v_a_766_);
lean_dec_ref(v_a_765_);
lean_dec(v_a_764_);
lean_dec_ref(v_a_763_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4(lean_object* v_00_u03b1_771_, lean_object* v_ref_772_, lean_object* v_msg_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___redArg(v_ref_772_, v_msg_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___boxed(lean_object* v_00_u03b1_782_, lean_object* v_ref_783_, lean_object* v_msg_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4(v_00_u03b1_782_, v_ref_783_, v_msg_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v_ref_783_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5(lean_object* v_00_u03b1_793_, lean_object* v_msg_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5___redArg(v_msg_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5___boxed(lean_object* v_00_u03b1_803_, lean_object* v_msg_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5(v_00_u03b1_803_, v_msg_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9(lean_object* v_msgData_813_, lean_object* v_macroStack_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg(v_msgData_813_, v_macroStack_814_, v___y_819_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___boxed(lean_object* v_msgData_823_, lean_object* v_macroStack_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9(v_msgData_823_, v_macroStack_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1(lean_object* v_msg_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
lean_object* v___f_840_; lean_object* v___x_288__overap_841_; lean_object* v___x_842_; 
v___f_840_ = ((lean_object*)(l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1___closed__0));
v___x_288__overap_841_ = lean_panic_fn_borrowed(v___f_840_, v_msg_834_);
lean_inc(v___y_838_);
lean_inc_ref(v___y_837_);
lean_inc(v___y_836_);
lean_inc_ref(v___y_835_);
v___x_842_ = lean_apply_5(v___x_288__overap_841_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, lean_box(0));
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1___boxed(lean_object* v_msg_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1(v_msg_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg___lam__0(lean_object* v_k_850_, lean_object* v_b_851_, lean_object* v_c_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v___x_858_; 
lean_inc(v___y_856_);
lean_inc_ref(v___y_855_);
lean_inc(v___y_854_);
lean_inc_ref(v___y_853_);
v___x_858_ = lean_apply_7(v_k_850_, v_b_851_, v_c_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, lean_box(0));
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg___lam__0___boxed(lean_object* v_k_859_, lean_object* v_b_860_, lean_object* v_c_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg___lam__0(v_k_859_, v_b_860_, v_c_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg(lean_object* v_e_868_, lean_object* v_k_869_, uint8_t v_cleanupAnnotations_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v___f_876_; uint8_t v___x_877_; uint8_t v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v___f_876_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_876_, 0, v_k_869_);
v___x_877_ = 1;
v___x_878_ = 0;
v___x_879_ = lean_box(0);
v___x_880_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_868_, v___x_877_, v___x_878_, v___x_877_, v___x_878_, v___x_879_, v___f_876_, v_cleanupAnnotations_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_880_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_880_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
else
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
v_a_889_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_880_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_880_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_889_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg___boxed(lean_object* v_e_897_, lean_object* v_k_898_, lean_object* v_cleanupAnnotations_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_905_; lean_object* v_res_906_; 
v_cleanupAnnotations_boxed_905_ = lean_unbox(v_cleanupAnnotations_899_);
v_res_906_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg(v_e_897_, v_k_898_, v_cleanupAnnotations_boxed_905_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2(lean_object* v_00_u03b1_907_, lean_object* v_e_908_, lean_object* v_k_909_, uint8_t v_cleanupAnnotations_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg(v_e_908_, v_k_909_, v_cleanupAnnotations_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___boxed(lean_object* v_00_u03b1_917_, lean_object* v_e_918_, lean_object* v_k_919_, lean_object* v_cleanupAnnotations_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_926_; lean_object* v_res_927_; 
v_cleanupAnnotations_boxed_926_ = lean_unbox(v_cleanupAnnotations_920_);
v_res_927_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2(v_00_u03b1_917_, v_e_918_, v_k_919_, v_cleanupAnnotations_boxed_926_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0_spec__3(lean_object* v_xs_928_, lean_object* v_v_929_, lean_object* v_i_930_){
_start:
{
lean_object* v___x_931_; uint8_t v___x_932_; 
v___x_931_ = lean_array_get_size(v_xs_928_);
v___x_932_ = lean_nat_dec_lt(v_i_930_, v___x_931_);
if (v___x_932_ == 0)
{
lean_object* v___x_933_; 
lean_dec(v_i_930_);
v___x_933_ = lean_box(0);
return v___x_933_;
}
else
{
lean_object* v___x_934_; uint8_t v___x_935_; 
v___x_934_ = lean_array_fget_borrowed(v_xs_928_, v_i_930_);
v___x_935_ = lean_expr_eqv(v___x_934_, v_v_929_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_936_ = lean_unsigned_to_nat(1u);
v___x_937_ = lean_nat_add(v_i_930_, v___x_936_);
lean_dec(v_i_930_);
v_i_930_ = v___x_937_;
goto _start;
}
else
{
lean_object* v___x_939_; 
v___x_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_939_, 0, v_i_930_);
return v___x_939_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0_spec__3___boxed(lean_object* v_xs_940_, lean_object* v_v_941_, lean_object* v_i_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0_spec__3(v_xs_940_, v_v_941_, v_i_942_);
lean_dec_ref(v_v_941_);
lean_dec_ref(v_xs_940_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0(lean_object* v_xs_944_, lean_object* v_v_945_){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = lean_unsigned_to_nat(0u);
v___x_947_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0_spec__3(v_xs_944_, v_v_945_, v___x_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0___boxed(lean_object* v_xs_948_, lean_object* v_v_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0(v_xs_948_, v_v_949_);
lean_dec_ref(v_v_949_);
lean_dec_ref(v_xs_948_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0(lean_object* v_xs_951_, lean_object* v_v_952_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0(v_xs_951_, v_v_952_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v___x_954_; 
v___x_954_ = lean_box(0);
return v___x_954_;
}
else
{
lean_object* v_val_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_962_; 
v_val_955_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_962_ == 0)
{
v___x_957_ = v___x_953_;
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_val_955_);
lean_dec(v___x_953_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_960_; 
if (v_isShared_958_ == 0)
{
v___x_960_ = v___x_957_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_val_955_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0___boxed(lean_object* v_xs_963_, lean_object* v_v_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0(v_xs_963_, v_v_964_);
lean_dec_ref(v_v_964_);
lean_dec_ref(v_xs_963_);
return v_res_965_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_968_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__1));
v___x_969_ = lean_unsigned_to_nat(8u);
v___x_970_ = lean_unsigned_to_nat(93u);
v___x_971_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__0));
v___x_972_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__0));
v___x_973_ = l_mkPanicMessageWithDecl(v___x_972_, v___x_971_, v___x_970_, v___x_969_, v___x_968_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_structuralArg___lam__0(lean_object* v_ys_974_, lean_object* v_e_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l_Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0(v_ys_974_, v_e_975_);
if (lean_obj_tag(v___x_981_) == 1)
{
lean_object* v_val_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_989_; 
v_val_982_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_989_ == 0)
{
v___x_984_ = v___x_981_;
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_val_982_);
lean_dec(v___x_981_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_987_; 
if (v_isShared_985_ == 0)
{
lean_ctor_set_tag(v___x_984_, 0);
v___x_987_ = v___x_984_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_val_982_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
else
{
lean_object* v___x_990_; lean_object* v___x_991_; 
lean_dec(v___x_981_);
v___x_990_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__2, &l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__2_once, _init_l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__2);
v___x_991_ = l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1(v___x_990_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
return v___x_991_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___boxed(lean_object* v_ys_992_, lean_object* v_e_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Lean_Elab_TerminationMeasure_structuralArg___lam__0(v_ys_992_, v_e_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec_ref(v_e_993_);
lean_dec_ref(v_ys_992_);
return v_res_999_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_structuralArg___closed__1(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1001_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_structuralArg___closed__0));
v___x_1002_ = lean_unsigned_to_nat(2u);
v___x_1003_ = lean_unsigned_to_nat(90u);
v___x_1004_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__0));
v___x_1005_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__0));
v___x_1006_ = l_mkPanicMessageWithDecl(v___x_1005_, v___x_1004_, v___x_1003_, v___x_1002_, v___x_1001_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_structuralArg(lean_object* v_measure_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_){
_start:
{
uint8_t v_structural_1014_; 
v_structural_1014_ = lean_ctor_get_uint8(v_measure_1008_, sizeof(void*)*2);
if (v_structural_1014_ == 0)
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
lean_dec_ref(v_measure_1008_);
v___x_1015_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_structuralArg___closed__1, &l_Lean_Elab_TerminationMeasure_structuralArg___closed__1_once, _init_l_Lean_Elab_TerminationMeasure_structuralArg___closed__1);
v___x_1016_ = l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1(v___x_1015_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_);
return v___x_1016_;
}
else
{
lean_object* v_fn_1017_; lean_object* v___f_1018_; uint8_t v___x_1019_; lean_object* v___x_1020_; 
v_fn_1017_ = lean_ctor_get(v_measure_1008_, 1);
lean_inc_ref(v_fn_1017_);
lean_dec_ref(v_measure_1008_);
v___f_1018_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_structuralArg___closed__2));
v___x_1019_ = 0;
v___x_1020_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg(v_fn_1017_, v___f_1018_, v___x_1019_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_);
return v___x_1020_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_structuralArg___boxed(lean_object* v_measure_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l_Lean_Elab_TerminationMeasure_structuralArg(v_measure_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_);
lean_dec(v_a_1025_);
lean_dec_ref(v_a_1024_);
lean_dec(v_a_1023_);
lean_dec_ref(v_a_1022_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2___redArg(lean_object* v___y_1028_){
_start:
{
lean_object* v_subExpr_1030_; lean_object* v_expr_1031_; lean_object* v___x_1032_; 
v_subExpr_1030_ = lean_ctor_get(v___y_1028_, 3);
v_expr_1031_ = lean_ctor_get(v_subExpr_1030_, 0);
lean_inc_ref(v_expr_1031_);
v___x_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1032_, 0, v_expr_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2___redArg___boxed(lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2___redArg(v___y_1033_);
lean_dec_ref(v___y_1033_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2(lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2___redArg(v___y_1036_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2___boxed(lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2(v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0(lean_object* v_____do__lift_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
uint8_t v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1060_ = 0;
v___x_1061_ = l_Lean_SourceInfo_fromRef(v_____do__lift_1052_, v___x_1060_);
v___x_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0___boxed(lean_object* v_____do__lift_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0(v_____do__lift_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v_____do__lift_1063_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg(lean_object* v_a_1081_){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; 
v___x_1083_ = lean_array_get_size(v_a_1081_);
v___x_1084_ = lean_unsigned_to_nat(0u);
v___x_1085_ = lean_nat_dec_eq(v___x_1083_, v___x_1084_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; uint8_t v___x_1091_; 
v___x_1086_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4));
v___x_1087_ = lean_box(0);
v___x_1088_ = lean_unsigned_to_nat(1u);
v___x_1089_ = lean_nat_sub(v___x_1083_, v___x_1088_);
v___x_1090_ = lean_array_get_borrowed(v___x_1087_, v_a_1081_, v___x_1089_);
lean_dec(v___x_1089_);
lean_inc(v___x_1090_);
v___x_1091_ = l_Lean_Syntax_isOfKind(v___x_1090_, v___x_1086_);
if (v___x_1091_ == 0)
{
lean_object* v___x_1092_; 
v___x_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1092_, 0, v_a_1081_);
return v___x_1092_;
}
else
{
lean_object* v___x_1093_; 
v___x_1093_ = lean_array_pop(v_a_1081_);
v_a_1081_ = v___x_1093_;
goto _start;
}
}
else
{
lean_object* v___x_1095_; 
v___x_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1095_, 0, v_a_1081_);
return v___x_1095_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___boxed(lean_object* v_a_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg(v_a_1096_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__0(lean_object* v_a_1099_, lean_object* v___x_1100_, size_t v_sz_1101_, size_t v_i_1102_, lean_object* v_bs_1103_){
_start:
{
uint8_t v___x_1104_; 
v___x_1104_ = lean_usize_dec_lt(v_i_1102_, v_sz_1101_);
if (v___x_1104_ == 0)
{
lean_dec(v___x_1100_);
return v_bs_1103_;
}
else
{
lean_object* v_v_1105_; lean_object* v___x_1106_; lean_object* v_bs_x27_1107_; lean_object* v___y_1109_; lean_object* v___x_1114_; uint8_t v___x_1115_; 
v_v_1105_ = lean_array_uget(v_bs_1103_, v_i_1102_);
v___x_1106_ = lean_unsigned_to_nat(0u);
v_bs_x27_1107_ = lean_array_uset(v_bs_1103_, v_i_1102_, v___x_1106_);
v___x_1114_ = l_Lean_TSyntax_getId(v_v_1105_);
v___x_1115_ = l_Lean_Syntax_hasIdent(v___x_1114_, v_a_1099_);
lean_dec(v___x_1114_);
if (v___x_1115_ == 0)
{
lean_dec(v_v_1105_);
lean_inc(v___x_1100_);
v___y_1109_ = v___x_1100_;
goto v___jp_1108_;
}
else
{
v___y_1109_ = v_v_1105_;
goto v___jp_1108_;
}
v___jp_1108_:
{
size_t v___x_1110_; size_t v___x_1111_; lean_object* v___x_1112_; 
v___x_1110_ = ((size_t)1ULL);
v___x_1111_ = lean_usize_add(v_i_1102_, v___x_1110_);
v___x_1112_ = lean_array_uset(v_bs_x27_1107_, v_i_1102_, v___y_1109_);
v_i_1102_ = v___x_1111_;
v_bs_1103_ = v___x_1112_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__0___boxed(lean_object* v_a_1116_, lean_object* v___x_1117_, lean_object* v_sz_1118_, lean_object* v_i_1119_, lean_object* v_bs_1120_){
_start:
{
size_t v_sz_boxed_1121_; size_t v_i_boxed_1122_; lean_object* v_res_1123_; 
v_sz_boxed_1121_ = lean_unbox_usize(v_sz_1118_);
lean_dec(v_sz_1118_);
v_i_boxed_1122_ = lean_unbox_usize(v_i_1119_);
lean_dec(v_i_1119_);
v_res_1123_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__0(v_a_1116_, v___x_1117_, v_sz_boxed_1121_, v_i_boxed_1122_, v_bs_1120_);
lean_dec(v_a_1116_);
return v_res_1123_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7(void){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = l_Array_mkArray0___redArg();
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__1___boxed(lean_object* v_a_1139_, lean_object* v_measure_1140_, lean_object* v_n_1141_, lean_object* v_n_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__1(v_a_1139_, v_measure_1140_, v_n_1141_, v_n_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v_n_1141_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go(lean_object* v_measure_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_){
_start:
{
lean_object* v_zero_1161_; uint8_t v_isZero_1162_; 
v_zero_1161_ = lean_unsigned_to_nat(0u);
v_isZero_1162_ = lean_nat_dec_eq(v_a_1152_, v_zero_1161_);
if (v_isZero_1162_ == 1)
{
lean_object* v___x_1163_; 
v___x_1163_ = l_Lean_PrettyPrinter_Delaborator_delab(v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v_a_1164_; lean_object* v_ref_1165_; lean_object* v___x_1166_; lean_object* v_a_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; size_t v_sz_1172_; size_t v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
lean_inc(v_a_1164_);
lean_dec_ref_known(v___x_1163_, 1);
v_ref_1165_ = lean_ctor_get(v_a_1158_, 2);
v___x_1166_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0(v_ref_1165_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_);
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc_n(v_a_1167_, 2);
lean_dec_ref(v___x_1166_);
v___x_1168_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4));
v___x_1169_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__0));
v___x_1170_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1170_, 0, v_a_1167_);
lean_ctor_set(v___x_1170_, 1, v___x_1169_);
v___x_1171_ = l_Lean_Syntax_node1(v_a_1167_, v___x_1168_, v___x_1170_);
v_sz_1172_ = lean_array_size(v_a_1153_);
v___x_1173_ = ((size_t)0ULL);
v___x_1174_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__0(v_a_1164_, v___x_1171_, v_sz_1172_, v___x_1173_, v_a_1153_);
v___x_1175_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg(v___x_1174_);
if (lean_obj_tag(v___x_1175_) == 0)
{
uint8_t v_structural_1176_; 
v_structural_1176_ = lean_ctor_get_uint8(v_measure_1151_, sizeof(void*)*2);
lean_dec_ref(v_measure_1151_);
if (v_structural_1176_ == 0)
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1215_; 
v_a_1177_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1179_ = v___x_1175_;
v_isShared_1180_ = v_isSharedCheck_1215_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1175_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1215_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1181_; uint8_t v___x_1182_; 
v___x_1181_ = lean_array_get_size(v_a_1177_);
v___x_1182_ = lean_nat_dec_eq(v___x_1181_, v_zero_1161_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1197_; 
v___x_1183_ = l_Lean_SourceInfo_fromRef(v_ref_1165_, v___x_1182_);
v___x_1184_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3));
v___x_1185_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__4));
lean_inc_n(v___x_1183_, 5);
v___x_1186_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1183_);
lean_ctor_set(v___x_1186_, 1, v___x_1185_);
v___x_1187_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__6));
v___x_1188_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7, &l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7);
v___x_1189_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1183_);
lean_ctor_set(v___x_1189_, 1, v___x_1187_);
lean_ctor_set(v___x_1189_, 2, v___x_1188_);
v___x_1190_ = l_Array_append___redArg(v___x_1188_, v_a_1177_);
lean_dec(v_a_1177_);
v___x_1191_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1183_);
lean_ctor_set(v___x_1191_, 1, v___x_1187_);
lean_ctor_set(v___x_1191_, 2, v___x_1190_);
v___x_1192_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__8));
v___x_1193_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1183_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
v___x_1194_ = l_Lean_Syntax_node2(v___x_1183_, v___x_1187_, v___x_1191_, v___x_1193_);
v___x_1195_ = l_Lean_Syntax_node4(v___x_1183_, v___x_1184_, v___x_1186_, v___x_1189_, v___x_1194_, v_a_1164_);
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 0, v___x_1195_);
v___x_1197_ = v___x_1179_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1195_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
else
{
lean_object* v___x_1199_; lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1214_; 
lean_del_object(v___x_1179_);
lean_dec(v_a_1177_);
v___x_1199_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0(v_ref_1165_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_);
v_a_1200_ = lean_ctor_get(v___x_1199_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1202_ = v___x_1199_;
v_isShared_1203_ = v_isSharedCheck_1214_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1199_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1214_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1212_; 
v___x_1204_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3));
v___x_1205_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__4));
lean_inc_n(v_a_1200_, 2);
v___x_1206_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1206_, 0, v_a_1200_);
lean_ctor_set(v___x_1206_, 1, v___x_1205_);
v___x_1207_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__6));
v___x_1208_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7, &l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7);
v___x_1209_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1209_, 0, v_a_1200_);
lean_ctor_set(v___x_1209_, 1, v___x_1207_);
lean_ctor_set(v___x_1209_, 2, v___x_1208_);
lean_inc_ref(v___x_1209_);
v___x_1210_ = l_Lean_Syntax_node4(v_a_1200_, v___x_1204_, v___x_1206_, v___x_1209_, v___x_1209_, v_a_1164_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 0, v___x_1210_);
v___x_1212_ = v___x_1202_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1210_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
}
else
{
lean_object* v_a_1216_; lean_object* v___x_1217_; uint8_t v___x_1218_; 
v_a_1216_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_a_1216_);
lean_dec_ref_known(v___x_1175_, 1);
v___x_1217_ = lean_array_get_size(v_a_1216_);
v___x_1218_ = lean_nat_dec_eq(v___x_1217_, v_zero_1161_);
if (v___x_1218_ == 0)
{
lean_object* v___x_1219_; lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1241_; 
v___x_1219_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0(v_ref_1165_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_);
v_a_1220_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1222_ = v___x_1219_;
v_isShared_1223_ = v_isSharedCheck_1241_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1219_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1241_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1239_; 
v___x_1224_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3));
v___x_1225_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__4));
lean_inc_n(v_a_1220_, 6);
v___x_1226_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1226_, 0, v_a_1220_);
lean_ctor_set(v___x_1226_, 1, v___x_1225_);
v___x_1227_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__6));
v___x_1228_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__9));
v___x_1229_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1229_, 0, v_a_1220_);
lean_ctor_set(v___x_1229_, 1, v___x_1228_);
v___x_1230_ = l_Lean_Syntax_node1(v_a_1220_, v___x_1227_, v___x_1229_);
v___x_1231_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7, &l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7);
v___x_1232_ = l_Array_append___redArg(v___x_1231_, v_a_1216_);
lean_dec(v_a_1216_);
v___x_1233_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1233_, 0, v_a_1220_);
lean_ctor_set(v___x_1233_, 1, v___x_1227_);
lean_ctor_set(v___x_1233_, 2, v___x_1232_);
v___x_1234_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__8));
v___x_1235_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1235_, 0, v_a_1220_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
v___x_1236_ = l_Lean_Syntax_node2(v_a_1220_, v___x_1227_, v___x_1233_, v___x_1235_);
v___x_1237_ = l_Lean_Syntax_node4(v_a_1220_, v___x_1224_, v___x_1226_, v___x_1230_, v___x_1236_, v_a_1164_);
if (v_isShared_1223_ == 0)
{
lean_ctor_set(v___x_1222_, 0, v___x_1237_);
v___x_1239_ = v___x_1222_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1237_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
else
{
lean_object* v___x_1242_; lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1260_; 
lean_dec(v_a_1216_);
v___x_1242_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0(v_ref_1165_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_);
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1245_ = v___x_1242_;
v_isShared_1246_ = v_isSharedCheck_1260_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1242_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1260_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1258_; 
v___x_1247_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3));
v___x_1248_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__4));
lean_inc_n(v_a_1243_, 4);
v___x_1249_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1249_, 0, v_a_1243_);
lean_ctor_set(v___x_1249_, 1, v___x_1248_);
v___x_1250_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__6));
v___x_1251_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__9));
v___x_1252_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1252_, 0, v_a_1243_);
lean_ctor_set(v___x_1252_, 1, v___x_1251_);
v___x_1253_ = l_Lean_Syntax_node1(v_a_1243_, v___x_1250_, v___x_1252_);
v___x_1254_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7, &l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7);
v___x_1255_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1255_, 0, v_a_1243_);
lean_ctor_set(v___x_1255_, 1, v___x_1250_);
lean_ctor_set(v___x_1255_, 2, v___x_1254_);
v___x_1256_ = l_Lean_Syntax_node4(v_a_1243_, v___x_1247_, v___x_1249_, v___x_1253_, v___x_1255_, v_a_1164_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 0, v___x_1256_);
v___x_1258_ = v___x_1245_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v___x_1256_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
}
else
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1268_; 
lean_dec(v_a_1164_);
lean_dec_ref(v_measure_1151_);
v_a_1261_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1263_ = v___x_1175_;
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1175_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_a_1261_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
else
{
lean_dec_ref(v_a_1153_);
lean_dec_ref(v_measure_1151_);
return v___x_1163_;
}
}
else
{
lean_object* v_one_1269_; lean_object* v_n_1270_; lean_object* v___f_1271_; lean_object* v___x_1272_; lean_object* v_a_1273_; uint8_t v___x_1274_; 
v_one_1269_ = lean_unsigned_to_nat(1u);
v_n_1270_ = lean_nat_sub(v_a_1152_, v_one_1269_);
lean_inc_ref(v_measure_1151_);
lean_inc_ref(v_a_1153_);
v___f_1271_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__1___boxed), 11, 3);
lean_closure_set(v___f_1271_, 0, v_a_1153_);
lean_closure_set(v___f_1271_, 1, v_measure_1151_);
lean_closure_set(v___f_1271_, 2, v_n_1270_);
v___x_1272_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2___redArg(v_a_1154_);
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_a_1273_);
lean_dec_ref(v___x_1272_);
v___x_1274_ = l_Lean_Expr_isLambda(v_a_1273_);
lean_dec(v_a_1273_);
if (v___x_1274_ == 0)
{
lean_dec_ref(v___f_1271_);
v_a_1152_ = v_zero_1161_;
goto _start;
}
else
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
lean_dec_ref(v_a_1153_);
lean_dec_ref(v_measure_1151_);
v___x_1276_ = l_Lean_NameSet_empty;
v___x_1277_ = l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg(v___f_1271_, v_isZero_1162_, v___x_1276_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_);
return v___x_1277_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__1(lean_object* v_a_1278_, lean_object* v_measure_1279_, lean_object* v_n_1280_, lean_object* v_n_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = lean_array_push(v_a_1278_, v_n_1281_);
v___x_1290_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go(v_measure_1279_, v_n_1280_, v___x_1289_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___boxed(lean_object* v_measure_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go(v_measure_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_);
lean_dec(v_a_1299_);
lean_dec_ref(v_a_1298_);
lean_dec(v_a_1297_);
lean_dec_ref(v_a_1296_);
lean_dec(v_a_1295_);
lean_dec_ref(v_a_1294_);
lean_dec(v_a_1292_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1(lean_object* v_inst_1302_, lean_object* v_a_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v___x_1311_; 
v___x_1311_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg(v_a_1303_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___boxed(lean_object* v_inst_1312_, lean_object* v_a_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1(v_inst_1312_, v_a_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter___redArg(lean_object* v_x_1322_, lean_object* v_x_1323_, lean_object* v_h__1_1324_, lean_object* v_h__2_1325_){
_start:
{
lean_object* v_zero_1326_; uint8_t v_isZero_1327_; 
v_zero_1326_ = lean_unsigned_to_nat(0u);
v_isZero_1327_ = lean_nat_dec_eq(v_x_1322_, v_zero_1326_);
if (v_isZero_1327_ == 1)
{
lean_object* v___x_1328_; 
lean_dec(v_h__2_1325_);
v___x_1328_ = lean_apply_1(v_h__1_1324_, v_x_1323_);
return v___x_1328_;
}
else
{
lean_object* v_one_1329_; lean_object* v_n_1330_; lean_object* v___x_1331_; 
lean_dec(v_h__1_1324_);
v_one_1329_ = lean_unsigned_to_nat(1u);
v_n_1330_ = lean_nat_sub(v_x_1322_, v_one_1329_);
v___x_1331_ = lean_apply_2(v_h__2_1325_, v_n_1330_, v_x_1323_);
return v___x_1331_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter___redArg___boxed(lean_object* v_x_1332_, lean_object* v_x_1333_, lean_object* v_h__1_1334_, lean_object* v_h__2_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter___redArg(v_x_1332_, v_x_1333_, v_h__1_1334_, v_h__2_1335_);
lean_dec(v_x_1332_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter(lean_object* v_motive_1337_, lean_object* v_x_1338_, lean_object* v_x_1339_, lean_object* v_h__1_1340_, lean_object* v_h__2_1341_){
_start:
{
lean_object* v_zero_1342_; uint8_t v_isZero_1343_; 
v_zero_1342_ = lean_unsigned_to_nat(0u);
v_isZero_1343_ = lean_nat_dec_eq(v_x_1338_, v_zero_1342_);
if (v_isZero_1343_ == 1)
{
lean_object* v___x_1344_; 
lean_dec(v_h__2_1341_);
v___x_1344_ = lean_apply_1(v_h__1_1340_, v_x_1339_);
return v___x_1344_;
}
else
{
lean_object* v_one_1345_; lean_object* v_n_1346_; lean_object* v___x_1347_; 
lean_dec(v_h__1_1340_);
v_one_1345_ = lean_unsigned_to_nat(1u);
v_n_1346_ = lean_nat_sub(v_x_1338_, v_one_1345_);
v___x_1347_ = lean_apply_2(v_h__2_1341_, v_n_1346_, v_x_1339_);
return v___x_1347_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter___boxed(lean_object* v_motive_1348_, lean_object* v_x_1349_, lean_object* v_x_1350_, lean_object* v_h__1_1351_, lean_object* v_h__2_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter(v_motive_1348_, v_x_1349_, v_x_1350_, v_h__1_1351_, v_h__2_1352_);
lean_dec(v_x_1349_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Array_map__unattach_match__1_splitter___redArg(lean_object* v_x_1354_, lean_object* v_h__1_1355_){
_start:
{
lean_object* v___x_1356_; 
v___x_1356_ = lean_apply_2(v_h__1_1355_, v_x_1354_, lean_box(0));
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Array_map__unattach_match__1_splitter(lean_object* v_00_u03b1_1357_, lean_object* v_P_1358_, lean_object* v_motive_1359_, lean_object* v_x_1360_, lean_object* v_h__1_1361_){
_start:
{
lean_object* v___x_1362_; 
v___x_1362_ = lean_apply_2(v_h__1_1361_, v_x_1360_, lean_box(0));
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___redArg(lean_object* v_e_1363_, lean_object* v_maxFVars_1364_, lean_object* v_k_1365_, uint8_t v_cleanupAnnotations_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v___f_1372_; uint8_t v___x_1373_; uint8_t v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___f_1372_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1372_, 0, v_k_1365_);
v___x_1373_ = 1;
v___x_1374_ = 0;
v___x_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1375_, 0, v_maxFVars_1364_);
v___x_1376_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1363_, v___x_1373_, v___x_1374_, v___x_1373_, v___x_1374_, v___x_1375_, v___f_1372_, v_cleanupAnnotations_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
lean_dec_ref_known(v___x_1375_, 1);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1379_ = v___x_1376_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1376_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1377_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
else
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1392_; 
v_a_1385_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1387_ = v___x_1376_;
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1376_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
if (v_isShared_1388_ == 0)
{
v___x_1390_ = v___x_1387_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_a_1385_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___redArg___boxed(lean_object* v_e_1393_, lean_object* v_maxFVars_1394_, lean_object* v_k_1395_, lean_object* v_cleanupAnnotations_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1402_; lean_object* v_res_1403_; 
v_cleanupAnnotations_boxed_1402_ = lean_unbox(v_cleanupAnnotations_1396_);
v_res_1403_ = l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___redArg(v_e_1393_, v_maxFVars_1394_, v_k_1395_, v_cleanupAnnotations_boxed_1402_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0(lean_object* v_00_u03b1_1404_, lean_object* v_e_1405_, lean_object* v_maxFVars_1406_, lean_object* v_k_1407_, uint8_t v_cleanupAnnotations_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v___x_1414_; 
v___x_1414_ = l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___redArg(v_e_1405_, v_maxFVars_1406_, v_k_1407_, v_cleanupAnnotations_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___boxed(lean_object* v_00_u03b1_1415_, lean_object* v_e_1416_, lean_object* v_maxFVars_1417_, lean_object* v_k_1418_, lean_object* v_cleanupAnnotations_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1425_; lean_object* v_res_1426_; 
v_cleanupAnnotations_boxed_1425_ = lean_unbox(v_cleanupAnnotations_1419_);
v_res_1426_ = l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0(v_00_u03b1_1415_, v_e_1416_, v_maxFVars_1417_, v_k_1418_, v_cleanupAnnotations_boxed_1425_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_delab___lam__0(lean_object* v_measure_1429_, lean_object* v_extraParams_1430_, lean_object* v___ys_1431_, lean_object* v_e_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1438_ = lean_box(1);
v___x_1439_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_delab___lam__0___closed__0));
v___x_1440_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___boxed), 10, 3);
lean_closure_set(v___x_1440_, 0, v_measure_1429_);
lean_closure_set(v___x_1440_, 1, v_extraParams_1430_);
lean_closure_set(v___x_1440_, 2, v___x_1439_);
v___x_1441_ = l_Lean_PrettyPrinter_delabCore___redArg(v_e_1432_, v___x_1438_, v___x_1440_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1450_; 
v_a_1442_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1444_ = v___x_1441_;
v_isShared_1445_ = v_isSharedCheck_1450_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1441_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1450_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v_fst_1446_; lean_object* v___x_1448_; 
v_fst_1446_ = lean_ctor_get(v_a_1442_, 0);
lean_inc(v_fst_1446_);
lean_dec(v_a_1442_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 0, v_fst_1446_);
v___x_1448_ = v___x_1444_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_fst_1446_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
else
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
v_a_1451_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1441_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1441_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1451_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_delab___lam__0___boxed(lean_object* v_measure_1459_, lean_object* v_extraParams_1460_, lean_object* v___ys_1461_, lean_object* v_e_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Lean_Elab_TerminationMeasure_delab___lam__0(v_measure_1459_, v_extraParams_1460_, v___ys_1461_, v_e_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec_ref(v___ys_1461_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_delab(lean_object* v_arity_1469_, lean_object* v_extraParams_1470_, lean_object* v_measure_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_){
_start:
{
lean_object* v_fn_1477_; lean_object* v___f_1478_; lean_object* v___x_1479_; uint8_t v___x_1480_; lean_object* v___x_1481_; 
v_fn_1477_ = lean_ctor_get(v_measure_1471_, 1);
lean_inc_ref(v_fn_1477_);
lean_inc(v_extraParams_1470_);
v___f_1478_ = lean_alloc_closure((void*)(l_Lean_Elab_TerminationMeasure_delab___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1478_, 0, v_measure_1471_);
lean_closure_set(v___f_1478_, 1, v_extraParams_1470_);
v___x_1479_ = lean_nat_sub(v_arity_1469_, v_extraParams_1470_);
lean_dec(v_extraParams_1470_);
v___x_1480_ = 0;
v___x_1481_ = l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___redArg(v_fn_1477_, v___x_1479_, v___f_1478_, v___x_1480_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_delab___boxed(lean_object* v_arity_1482_, lean_object* v_extraParams_1483_, lean_object* v_measure_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_Lean_Elab_TerminationMeasure_delab(v_arity_1482_, v_extraParams_1483_, v_measure_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_);
lean_dec(v_a_1488_);
lean_dec_ref(v_a_1487_);
lean_dec(v_a_1486_);
lean_dec_ref(v_a_1485_);
lean_dec(v_arity_1482_);
return v_res_1490_;
}
}
lean_object* runtime_initialize_Lean_Elab_Binders(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_TerminationMeasure(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Binders(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_instInhabitedTerminationMeasure_default = _init_l_Lean_Elab_instInhabitedTerminationMeasure_default();
lean_mark_persistent(l_Lean_Elab_instInhabitedTerminationMeasure_default);
l_Lean_Elab_instInhabitedTerminationMeasure = _init_l_Lean_Elab_instInhabitedTerminationMeasure();
lean_mark_persistent(l_Lean_Elab_instInhabitedTerminationMeasure);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_PreDefinition_TerminationMeasure(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Binders(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_TerminationMeasure(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Binders(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_TerminationMeasure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_PreDefinition_TerminationMeasure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_PreDefinition_TerminationMeasure(builtin);
}
#ifdef __cplusplus
}
#endif
