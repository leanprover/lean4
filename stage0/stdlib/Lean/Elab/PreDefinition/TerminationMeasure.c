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
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___redArg___lam__0(lean_object* v_k_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v_b_33_, lean_object* v_c_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_){
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
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_30_ = stack[0].m_obj;
lean_object* v___y_31_ = stack[1].m_obj;
lean_object* v___y_32_ = stack[2].m_obj;
lean_object* v_b_33_ = stack[3].m_obj;
lean_object* v_c_34_ = stack[4].m_obj;
lean_object* v___y_35_ = stack[5].m_obj;
lean_object* v___y_36_ = stack[6].m_obj;
lean_object* v___y_37_ = stack[7].m_obj;
lean_object* v___y_38_ = stack[8].m_obj;
lean_object* v_res_41_;
v_res_41_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___redArg___lam__0(v_k_30_, v___y_31_, v___y_32_, v_b_33_, v_c_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_);
stack->m_obj
 = v_res_41_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___redArg___lam__0___boxed(lean_object* v_k_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v_b_45_, lean_object* v_c_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___redArg___lam__0(v_k_42_, v___y_43_, v___y_44_, v_b_45_, v_c_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_44_);
lean_dec_ref(v___y_43_);
return v_res_52_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___redArg(lean_object* v_type_53_, lean_object* v_maxFVars_x3f_54_, lean_object* v_k_55_, uint8_t v_cleanupAnnotations_56_, uint8_t v_whnfType_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_){
_start:
{
lean_object* v___f_65_; lean_object* v___x_66_; 
lean_inc(v___y_59_);
lean_inc_ref(v___y_58_);
v___f_65_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_65_, 0, v_k_55_);
lean_closure_set(v___f_65_, 1, v___y_58_);
lean_closure_set(v___f_65_, 2, v___y_59_);
v___x_66_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_53_, v_maxFVars_x3f_54_, v___f_65_, v_cleanupAnnotations_56_, v_whnfType_57_, v___y_60_, v___y_61_, v___y_62_, v___y_63_);
if (lean_obj_tag(v___x_66_) == 0)
{
return v___x_66_;
}
else
{
lean_object* v_a_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_74_; 
v_a_67_ = lean_ctor_get(v___x_66_, 0);
v_isSharedCheck_74_ = !lean_is_exclusive(v___x_66_);
if (v_isSharedCheck_74_ == 0)
{
v___x_69_ = v___x_66_;
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_a_67_);
lean_dec(v___x_66_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_72_; 
if (v_isShared_70_ == 0)
{
v___x_72_ = v___x_69_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_a_67_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_53_ = stack[0].m_obj;
lean_object* v_maxFVars_x3f_54_ = stack[1].m_obj;
lean_object* v_k_55_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_56_ = stack[3].m_num;
uint8_t v_whnfType_57_ = stack[4].m_num;
lean_object* v___y_58_ = stack[5].m_obj;
lean_object* v___y_59_ = stack[6].m_obj;
lean_object* v___y_60_ = stack[7].m_obj;
lean_object* v___y_61_ = stack[8].m_obj;
lean_object* v___y_62_ = stack[9].m_obj;
lean_object* v___y_63_ = stack[10].m_obj;
lean_object* v_res_75_;
v_res_75_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___redArg(v_type_53_, v_maxFVars_x3f_54_, v_k_55_, v_cleanupAnnotations_56_, v_whnfType_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_);
stack->m_obj
 = v_res_75_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___redArg___boxed(lean_object* v_type_76_, lean_object* v_maxFVars_x3f_77_, lean_object* v_k_78_, lean_object* v_cleanupAnnotations_79_, lean_object* v_whnfType_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_88_; uint8_t v_whnfType_boxed_89_; lean_object* v_res_90_; 
v_cleanupAnnotations_boxed_88_ = lean_unbox(v_cleanupAnnotations_79_);
v_whnfType_boxed_89_ = lean_unbox(v_whnfType_80_);
v_res_90_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___redArg(v_type_76_, v_maxFVars_x3f_77_, v_k_78_, v_cleanupAnnotations_boxed_88_, v_whnfType_boxed_89_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_85_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
return v_res_90_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0(lean_object* v_00_u03b1_91_, lean_object* v_type_92_, lean_object* v_maxFVars_x3f_93_, lean_object* v_k_94_, uint8_t v_cleanupAnnotations_95_, uint8_t v_whnfType_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___redArg(v_type_92_, v_maxFVars_x3f_93_, v_k_94_, v_cleanupAnnotations_95_, v_whnfType_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_);
return v___x_104_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_92_ = stack[1].m_obj;
lean_object* v_maxFVars_x3f_93_ = stack[2].m_obj;
lean_object* v_k_94_ = stack[3].m_obj;
uint8_t v_cleanupAnnotations_95_ = stack[4].m_num;
uint8_t v_whnfType_96_ = stack[5].m_num;
lean_object* v___y_97_ = stack[6].m_obj;
lean_object* v___y_98_ = stack[7].m_obj;
lean_object* v___y_99_ = stack[8].m_obj;
lean_object* v___y_100_ = stack[9].m_obj;
lean_object* v___y_101_ = stack[10].m_obj;
lean_object* v___y_102_ = stack[11].m_obj;
lean_object* v_res_105_;
v_res_105_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0(lean_box(0), v_type_92_, v_maxFVars_x3f_93_, v_k_94_, v_cleanupAnnotations_95_, v_whnfType_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_);
stack->m_obj
 = v_res_105_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___boxed(lean_object* v_00_u03b1_106_, lean_object* v_type_107_, lean_object* v_maxFVars_x3f_108_, lean_object* v_k_109_, lean_object* v_cleanupAnnotations_110_, lean_object* v_whnfType_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_119_; uint8_t v_whnfType_boxed_120_; lean_object* v_res_121_; 
v_cleanupAnnotations_boxed_119_ = lean_unbox(v_cleanupAnnotations_110_);
v_whnfType_boxed_120_ = lean_unbox(v_whnfType_111_);
v_res_121_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0(v_00_u03b1_106_, v_type_107_, v_maxFVars_x3f_108_, v_k_109_, v_cleanupAnnotations_boxed_119_, v_whnfType_boxed_120_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__1(lean_object* v_msg_122_){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = l_Lean_instInhabitedExpr;
v___x_124_ = lean_panic_fn_borrowed(v___x_123_, v_msg_122_);
return v___x_124_;
}
}
lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_TerminationMeasure_elab_spec__5___redArg(lean_object* v_a_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_);
return v___x_133_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_TerminationMeasure_elab_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_125_ = stack[0].m_obj;
lean_object* v___y_126_ = stack[1].m_obj;
lean_object* v___y_127_ = stack[2].m_obj;
lean_object* v___y_128_ = stack[3].m_obj;
lean_object* v___y_129_ = stack[4].m_obj;
lean_object* v___y_130_ = stack[5].m_obj;
lean_object* v___y_131_ = stack[6].m_obj;
lean_object* v_res_134_;
v_res_134_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_TerminationMeasure_elab_spec__5___redArg(v_a_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_);
stack->m_obj
 = v_res_134_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_TerminationMeasure_elab_spec__5___redArg___boxed(lean_object* v_a_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_TerminationMeasure_elab_spec__5___redArg(v_a_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
return v_res_143_;
}
}
lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_TerminationMeasure_elab_spec__5(lean_object* v_00_u03b1_144_, lean_object* v_a_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_);
return v___x_153_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_TerminationMeasure_elab_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_145_ = stack[1].m_obj;
lean_object* v___y_146_ = stack[2].m_obj;
lean_object* v___y_147_ = stack[3].m_obj;
lean_object* v___y_148_ = stack[4].m_obj;
lean_object* v___y_149_ = stack[5].m_obj;
lean_object* v___y_150_ = stack[6].m_obj;
lean_object* v___y_151_ = stack[7].m_obj;
lean_object* v_res_154_;
v_res_154_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_TerminationMeasure_elab_spec__5(lean_box(0), v_a_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_);
stack->m_obj
 = v_res_154_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_TerminationMeasure_elab_spec__5___boxed(lean_object* v_00_u03b1_155_, lean_object* v_a_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_TerminationMeasure_elab_spec__5(v_00_u03b1_155_, v_a_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
lean_dec(v___y_158_);
lean_dec_ref(v___y_157_);
return v_res_164_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6___closed__0(void){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = l_Lean_Elab_Term_instInhabitedTermElabM___redArg();
return v___x_165_;
}
}
lean_object* l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6(lean_object* v_msg_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v___x_174_; lean_object* v___x_3233__overap_175_; lean_object* v___x_176_; 
v___x_174_ = lean_obj_once(&l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6___closed__0, &l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6___closed__0_once, _init_l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6___closed__0);
v___x_3233__overap_175_ = lean_panic_fn_borrowed(v___x_174_, v_msg_166_);
lean_inc(v___y_172_);
lean_inc_ref(v___y_171_);
lean_inc(v___y_170_);
lean_inc_ref(v___y_169_);
lean_inc(v___y_168_);
lean_inc_ref(v___y_167_);
v___x_176_ = lean_apply_7(v___x_3233__overap_175_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, lean_box(0));
return v___x_176_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_166_ = stack[0].m_obj;
lean_object* v___y_167_ = stack[1].m_obj;
lean_object* v___y_168_ = stack[2].m_obj;
lean_object* v___y_169_ = stack[3].m_obj;
lean_object* v___y_170_ = stack[4].m_obj;
lean_object* v___y_171_ = stack[5].m_obj;
lean_object* v___y_172_ = stack[6].m_obj;
lean_object* v_res_177_;
v_res_177_ = l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6(v_msg_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
stack->m_obj
 = v_res_177_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6___boxed(lean_object* v_msg_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6(v_msg_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_);
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
return v_res_186_;
}
}
lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__0(lean_object* v_ys_187_, lean_object* v_xs_188_, lean_object* v_a_189_, uint8_t v___x_190_, lean_object* v_zs_191_, lean_object* v_x_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; uint8_t v___x_202_; uint8_t v___x_203_; lean_object* v___x_204_; 
v___x_200_ = l_Array_append___redArg(v_ys_187_, v_xs_188_);
v___x_201_ = l_Array_append___redArg(v___x_200_, v_zs_191_);
v___x_202_ = 0;
v___x_203_ = 1;
v___x_204_ = l_Lean_Meta_mkLambdaFVars(v___x_201_, v_a_189_, v___x_202_, v___x_190_, v___x_202_, v___x_190_, v___x_203_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
lean_dec_ref(v___x_201_);
return v___x_204_;
}
}
LEAN_EXPORT void l_Lean_Elab_TerminationMeasure_elab___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ys_187_ = stack[0].m_obj;
lean_object* v_xs_188_ = stack[1].m_obj;
lean_object* v_a_189_ = stack[2].m_obj;
uint8_t v___x_190_ = stack[3].m_num;
lean_object* v_zs_191_ = stack[4].m_obj;
lean_object* v_x_192_ = stack[5].m_obj;
lean_object* v___y_193_ = stack[6].m_obj;
lean_object* v___y_194_ = stack[7].m_obj;
lean_object* v___y_195_ = stack[8].m_obj;
lean_object* v___y_196_ = stack[9].m_obj;
lean_object* v___y_197_ = stack[10].m_obj;
lean_object* v___y_198_ = stack[11].m_obj;
lean_object* v_res_205_;
v_res_205_ = l_Lean_Elab_TerminationMeasure_elab___lam__0(v_ys_187_, v_xs_188_, v_a_189_, v___x_190_, v_zs_191_, v_x_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
stack->m_obj
 = v_res_205_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__0___boxed(lean_object* v_ys_206_, lean_object* v_xs_207_, lean_object* v_a_208_, lean_object* v___x_209_, lean_object* v_zs_210_, lean_object* v_x_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
uint8_t v___x_5715__boxed_219_; lean_object* v_res_220_; 
v___x_5715__boxed_219_ = lean_unbox(v___x_209_);
v_res_220_ = l_Lean_Elab_TerminationMeasure_elab___lam__0(v_ys_206_, v_xs_207_, v_a_208_, v___x_5715__boxed_219_, v_zs_210_, v_x_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
lean_dec_ref(v_x_211_);
lean_dec_ref(v_zs_210_);
lean_dec_ref(v_xs_207_);
return v_res_220_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__0(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = lean_box(1);
v___x_222_ = l_Lean_MessageData_ofFormat(v___x_221_);
return v___x_222_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__3(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__2));
v___x_227_ = l_Lean_MessageData_ofFormat(v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11(lean_object* v_x_228_, lean_object* v_x_229_){
_start:
{
if (lean_obj_tag(v_x_229_) == 0)
{
return v_x_228_;
}
else
{
lean_object* v_head_230_; lean_object* v_tail_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_253_; 
v_head_230_ = lean_ctor_get(v_x_229_, 0);
v_tail_231_ = lean_ctor_get(v_x_229_, 1);
v_isSharedCheck_253_ = !lean_is_exclusive(v_x_229_);
if (v_isSharedCheck_253_ == 0)
{
v___x_233_ = v_x_229_;
v_isShared_234_ = v_isSharedCheck_253_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_tail_231_);
lean_inc(v_head_230_);
lean_dec(v_x_229_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_253_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v_before_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_251_; 
v_before_235_ = lean_ctor_get(v_head_230_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v_head_230_);
if (v_isSharedCheck_251_ == 0)
{
lean_object* v_unused_252_; 
v_unused_252_ = lean_ctor_get(v_head_230_, 1);
lean_dec(v_unused_252_);
v___x_237_ = v_head_230_;
v_isShared_238_ = v_isSharedCheck_251_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_before_235_);
lean_dec(v_head_230_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_251_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_239_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__0);
if (v_isShared_238_ == 0)
{
lean_ctor_set_tag(v___x_237_, 7);
lean_ctor_set(v___x_237_, 1, v___x_239_);
lean_ctor_set(v___x_237_, 0, v_x_228_);
v___x_241_ = v___x_237_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_x_228_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v___x_239_);
v___x_241_ = v_reuseFailAlloc_250_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_242_; lean_object* v___x_244_; 
v___x_242_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__3);
if (v_isShared_234_ == 0)
{
lean_ctor_set_tag(v___x_233_, 7);
lean_ctor_set(v___x_233_, 1, v___x_242_);
lean_ctor_set(v___x_233_, 0, v___x_241_);
v___x_244_ = v___x_233_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_241_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v___x_242_);
v___x_244_ = v_reuseFailAlloc_249_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_245_ = l_Lean_MessageData_ofSyntax(v_before_235_);
v___x_246_ = l_Lean_indentD(v___x_245_);
v___x_247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_244_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
v_x_228_ = v___x_247_;
v_x_229_ = v_tail_231_;
goto _start;
}
}
}
}
}
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__10(lean_object* v_opts_254_, lean_object* v_opt_255_){
_start:
{
lean_object* v_name_256_; lean_object* v_defValue_257_; lean_object* v_map_258_; lean_object* v___x_259_; 
v_name_256_ = lean_ctor_get(v_opt_255_, 0);
v_defValue_257_ = lean_ctor_get(v_opt_255_, 1);
v_map_258_ = lean_ctor_get(v_opts_254_, 0);
v___x_259_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_258_, v_name_256_);
if (lean_obj_tag(v___x_259_) == 0)
{
uint8_t v___x_260_; 
v___x_260_ = lean_unbox(v_defValue_257_);
return v___x_260_;
}
else
{
lean_object* v_val_261_; 
v_val_261_ = lean_ctor_get(v___x_259_, 0);
lean_inc(v_val_261_);
lean_dec_ref_known(v___x_259_, 1);
if (lean_obj_tag(v_val_261_) == 1)
{
uint8_t v_v_262_; 
v_v_262_ = lean_ctor_get_uint8(v_val_261_, 0);
lean_dec_ref_known(v_val_261_, 0);
return v_v_262_;
}
else
{
uint8_t v___x_263_; 
lean_dec(v_val_261_);
v___x_263_ = lean_unbox(v_defValue_257_);
return v___x_263_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_254_ = stack[0].m_obj;
lean_object* v_opt_255_ = stack[1].m_obj;
uint8_t v_res_264_;
v_res_264_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__10(v_opts_254_, v_opt_255_);
stack->m_num = v_res_264_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__10___boxed(lean_object* v_opts_265_, lean_object* v_opt_266_){
_start:
{
uint8_t v_res_267_; lean_object* v_r_268_; 
v_res_267_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__10(v_opts_265_, v_opt_266_);
lean_dec_ref(v_opt_266_);
lean_dec_ref(v_opts_265_);
v_r_268_ = lean_box(v_res_267_);
return v_r_268_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg___closed__1));
v___x_273_ = l_Lean_MessageData_ofFormat(v___x_272_);
return v___x_273_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg(lean_object* v_msgData_274_, lean_object* v_macroStack_275_, lean_object* v___y_276_){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; uint8_t v___x_280_; 
v___x_278_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_276_);
v___x_279_ = l_Lean_Elab_pp_macroStack;
v___x_280_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__10(v___x_278_, v___x_279_);
lean_dec_ref(v___x_278_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; 
lean_dec(v_macroStack_275_);
v___x_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_281_, 0, v_msgData_274_);
return v___x_281_;
}
else
{
if (lean_obj_tag(v_macroStack_275_) == 0)
{
lean_object* v___x_282_; 
v___x_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_282_, 0, v_msgData_274_);
return v___x_282_;
}
else
{
lean_object* v_head_283_; lean_object* v_after_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_299_; 
v_head_283_ = lean_ctor_get(v_macroStack_275_, 0);
lean_inc(v_head_283_);
v_after_284_ = lean_ctor_get(v_head_283_, 1);
v_isSharedCheck_299_ = !lean_is_exclusive(v_head_283_);
if (v_isSharedCheck_299_ == 0)
{
lean_object* v_unused_300_; 
v_unused_300_ = lean_ctor_get(v_head_283_, 0);
lean_dec(v_unused_300_);
v___x_286_ = v_head_283_;
v_isShared_287_ = v_isSharedCheck_299_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_after_284_);
lean_dec(v_head_283_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_299_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_288_; lean_object* v___x_290_; 
v___x_288_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11___closed__0);
if (v_isShared_287_ == 0)
{
lean_ctor_set_tag(v___x_286_, 7);
lean_ctor_set(v___x_286_, 1, v___x_288_);
lean_ctor_set(v___x_286_, 0, v_msgData_274_);
v___x_290_ = v___x_286_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_msgData_274_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v___x_288_);
v___x_290_ = v_reuseFailAlloc_298_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v_msgData_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_291_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg___closed__2);
v___x_292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_290_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
v___x_293_ = l_Lean_MessageData_ofSyntax(v_after_284_);
v___x_294_ = l_Lean_indentD(v___x_293_);
v_msgData_295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_295_, 0, v___x_292_);
lean_ctor_set(v_msgData_295_, 1, v___x_294_);
v___x_296_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__11(v_msgData_295_, v_macroStack_275_);
v___x_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
return v___x_297_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_274_ = stack[0].m_obj;
lean_object* v_macroStack_275_ = stack[1].m_obj;
lean_object* v___y_276_ = stack[2].m_obj;
lean_object* v_res_301_;
v_res_301_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg(v_msgData_274_, v_macroStack_275_, v___y_276_);
stack->m_obj
 = v_res_301_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg___boxed(lean_object* v_msgData_302_, lean_object* v_macroStack_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg(v_msgData_302_, v_macroStack_303_, v___y_304_);
lean_dec_ref(v___y_304_);
return v_res_306_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__8(lean_object* v_msgData_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
lean_object* v___x_313_; lean_object* v_env_314_; uint8_t v___x_315_; lean_object* v_env_316_; lean_object* v___x_317_; lean_object* v_toCold_318_; lean_object* v_mctx_319_; lean_object* v_lctx_320_; lean_object* v_options_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_313_ = lean_st_ref_get(v___y_311_);
v_env_314_ = lean_ctor_get(v___x_313_, 0);
lean_inc_ref(v_env_314_);
lean_dec(v___x_313_);
v___x_315_ = 0;
v_env_316_ = l_Lean_Environment_setRecordingDeps(v_env_314_, v___x_315_);
v___x_317_ = lean_st_ref_get(v___y_309_);
v_toCold_318_ = lean_ctor_get(v___y_310_, 0);
v_mctx_319_ = lean_ctor_get(v___x_317_, 0);
lean_inc_ref(v_mctx_319_);
lean_dec(v___x_317_);
v_lctx_320_ = lean_ctor_get(v___y_308_, 2);
v_options_321_ = lean_ctor_get(v_toCold_318_, 2);
lean_inc_ref(v_options_321_);
lean_inc_ref(v_lctx_320_);
v___x_322_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_322_, 0, v_env_316_);
lean_ctor_set(v___x_322_, 1, v_mctx_319_);
lean_ctor_set(v___x_322_, 2, v_lctx_320_);
lean_ctor_set(v___x_322_, 3, v_options_321_);
v___x_323_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
lean_ctor_set(v___x_323_, 1, v_msgData_307_);
v___x_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
return v___x_324_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_307_ = stack[0].m_obj;
lean_object* v___y_308_ = stack[1].m_obj;
lean_object* v___y_309_ = stack[2].m_obj;
lean_object* v___y_310_ = stack[3].m_obj;
lean_object* v___y_311_ = stack[4].m_obj;
lean_object* v_res_325_;
v_res_325_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__8(v_msgData_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_);
stack->m_obj
 = v_res_325_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__8___boxed(lean_object* v_msgData_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__8(v_msgData_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
return v_res_332_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5___redArg(lean_object* v_msg_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v_ref_341_; lean_object* v_macroStack_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v_a_345_; lean_object* v___x_346_; lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_355_; 
v_ref_341_ = lean_ctor_get(v___y_338_, 2);
v_macroStack_342_ = lean_ctor_get(v___y_334_, 1);
v___x_343_ = l_Lean_Elab_getBetterRef(v_ref_341_, v_macroStack_342_);
v___x_344_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__8(v_msg_333_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
v_a_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_a_345_);
lean_dec_ref(v___x_344_);
lean_inc(v_macroStack_342_);
v___x_346_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg(v_a_345_, v_macroStack_342_, v___y_338_);
v_a_347_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_355_ == 0)
{
v___x_349_ = v___x_346_;
v_isShared_350_ = v_isSharedCheck_355_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_346_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_355_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_351_; lean_object* v___x_353_; 
v___x_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_351_, 0, v___x_343_);
lean_ctor_set(v___x_351_, 1, v_a_347_);
if (v_isShared_350_ == 0)
{
lean_ctor_set_tag(v___x_349_, 1);
lean_ctor_set(v___x_349_, 0, v___x_351_);
v___x_353_ = v___x_349_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_351_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_333_ = stack[0].m_obj;
lean_object* v___y_334_ = stack[1].m_obj;
lean_object* v___y_335_ = stack[2].m_obj;
lean_object* v___y_336_ = stack[3].m_obj;
lean_object* v___y_337_ = stack[4].m_obj;
lean_object* v___y_338_ = stack[5].m_obj;
lean_object* v___y_339_ = stack[6].m_obj;
lean_object* v_res_356_;
v_res_356_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5___redArg(v_msg_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
stack->m_obj
 = v_res_356_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5___redArg___boxed(lean_object* v_msg_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5___redArg(v_msg_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
return v_res_365_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___redArg(lean_object* v_ref_366_, lean_object* v_msg_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v_toCold_375_; lean_object* v_currRecDepth_376_; lean_object* v_ref_377_; uint16_t v_optionFlags_378_; uint8_t v_suppressElabErrors_379_; uint8_t v_isRecordingDeps_380_; lean_object* v_ref_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v_toCold_375_ = lean_ctor_get(v___y_372_, 0);
v_currRecDepth_376_ = lean_ctor_get(v___y_372_, 1);
v_ref_377_ = lean_ctor_get(v___y_372_, 2);
v_optionFlags_378_ = lean_ctor_get_uint16(v___y_372_, sizeof(void*)*3);
v_suppressElabErrors_379_ = lean_ctor_get_uint8(v___y_372_, sizeof(void*)*3 + 2);
v_isRecordingDeps_380_ = lean_ctor_get_uint8(v___y_372_, sizeof(void*)*3 + 3);
v_ref_381_ = l_Lean_replaceRef(v_ref_366_, v_ref_377_);
lean_inc(v_currRecDepth_376_);
lean_inc_ref(v_toCold_375_);
v___x_382_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_382_, 0, v_toCold_375_);
lean_ctor_set(v___x_382_, 1, v_currRecDepth_376_);
lean_ctor_set(v___x_382_, 2, v_ref_381_);
lean_ctor_set_uint16(v___x_382_, sizeof(void*)*3, v_optionFlags_378_);
lean_ctor_set_uint8(v___x_382_, sizeof(void*)*3 + 2, v_suppressElabErrors_379_);
lean_ctor_set_uint8(v___x_382_, sizeof(void*)*3 + 3, v_isRecordingDeps_380_);
v___x_383_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5___redArg(v_msg_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___x_382_, v___y_373_);
lean_dec_ref_known(v___x_382_, 3);
return v___x_383_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_366_ = stack[0].m_obj;
lean_object* v_msg_367_ = stack[1].m_obj;
lean_object* v___y_368_ = stack[2].m_obj;
lean_object* v___y_369_ = stack[3].m_obj;
lean_object* v___y_370_ = stack[4].m_obj;
lean_object* v___y_371_ = stack[5].m_obj;
lean_object* v___y_372_ = stack[6].m_obj;
lean_object* v___y_373_ = stack[7].m_obj;
lean_object* v_res_384_;
v_res_384_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___redArg(v_ref_366_, v_msg_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_);
stack->m_obj
 = v_res_384_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___redArg___boxed(lean_object* v_ref_385_, lean_object* v_msg_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___redArg(v_ref_385_, v_msg_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v_ref_385_);
return v_res_394_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2_spec__2(lean_object* v_a_395_, lean_object* v_as_396_, size_t v_i_397_, size_t v_stop_398_){
_start:
{
uint8_t v___x_399_; 
v___x_399_ = lean_usize_dec_eq(v_i_397_, v_stop_398_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; uint8_t v___x_401_; 
v___x_400_ = lean_array_uget_borrowed(v_as_396_, v_i_397_);
v___x_401_ = lean_expr_eqv(v_a_395_, v___x_400_);
if (v___x_401_ == 0)
{
size_t v___x_402_; size_t v___x_403_; 
v___x_402_ = ((size_t)1ULL);
v___x_403_ = lean_usize_add(v_i_397_, v___x_402_);
v_i_397_ = v___x_403_;
goto _start;
}
else
{
return v___x_401_;
}
}
else
{
uint8_t v___x_405_; 
v___x_405_ = 0;
return v___x_405_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_395_ = stack[0].m_obj;
lean_object* v_as_396_ = stack[1].m_obj;
size_t v_i_397_ = stack[2].m_num;
size_t v_stop_398_ = stack[3].m_num;
uint8_t v_res_406_;
v_res_406_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2_spec__2(v_a_395_, v_as_396_, v_i_397_, v_stop_398_);
stack->m_num = v_res_406_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2_spec__2___boxed(lean_object* v_a_407_, lean_object* v_as_408_, lean_object* v_i_409_, lean_object* v_stop_410_){
_start:
{
size_t v_i_boxed_411_; size_t v_stop_boxed_412_; uint8_t v_res_413_; lean_object* v_r_414_; 
v_i_boxed_411_ = lean_unbox_usize(v_i_409_);
lean_dec(v_i_409_);
v_stop_boxed_412_ = lean_unbox_usize(v_stop_410_);
lean_dec(v_stop_410_);
v_res_413_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2_spec__2(v_a_407_, v_as_408_, v_i_boxed_411_, v_stop_boxed_412_);
lean_dec_ref(v_as_408_);
lean_dec_ref(v_a_407_);
v_r_414_ = lean_box(v_res_413_);
return v_r_414_;
}
}
uint8_t l_Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2(lean_object* v_as_415_, lean_object* v_a_416_){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; uint8_t v___x_419_; 
v___x_417_ = lean_unsigned_to_nat(0u);
v___x_418_ = lean_array_get_size(v_as_415_);
v___x_419_ = lean_nat_dec_lt(v___x_417_, v___x_418_);
if (v___x_419_ == 0)
{
return v___x_419_;
}
else
{
if (v___x_419_ == 0)
{
return v___x_419_;
}
else
{
size_t v___x_420_; size_t v___x_421_; uint8_t v___x_422_; 
v___x_420_ = ((size_t)0ULL);
v___x_421_ = lean_usize_of_nat(v___x_418_);
v___x_422_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2_spec__2(v_a_416_, v_as_415_, v___x_420_, v___x_421_);
return v___x_422_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_415_ = stack[0].m_obj;
lean_object* v_a_416_ = stack[1].m_obj;
uint8_t v_res_423_;
v_res_423_ = l_Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2(v_as_415_, v_a_416_);
stack->m_num = v_res_423_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2___boxed(lean_object* v_as_424_, lean_object* v_a_425_){
_start:
{
uint8_t v_res_426_; lean_object* v_r_427_; 
v_res_426_ = l_Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2(v_as_424_, v_a_425_);
lean_dec_ref(v_a_425_);
lean_dec_ref(v_as_424_);
v_r_427_ = lean_box(v_res_426_);
return v_r_427_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3___closed__1(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3___closed__0));
v___x_430_ = l_Lean_stringToMessageData(v___x_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3(lean_object* v_a_431_, lean_object* v_a_432_){
_start:
{
if (lean_obj_tag(v_a_431_) == 0)
{
lean_object* v___x_433_; 
v___x_433_ = l_List_reverse___redArg(v_a_432_);
return v___x_433_;
}
else
{
lean_object* v_head_434_; lean_object* v_tail_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_447_; 
v_head_434_ = lean_ctor_get(v_a_431_, 0);
v_tail_435_ = lean_ctor_get(v_a_431_, 1);
v_isSharedCheck_447_ = !lean_is_exclusive(v_a_431_);
if (v_isSharedCheck_447_ == 0)
{
v___x_437_ = v_a_431_;
v_isShared_438_ = v_isSharedCheck_447_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_tail_435_);
lean_inc(v_head_434_);
lean_dec(v_a_431_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_447_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_439_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3___closed__1, &l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3___closed__1);
v___x_440_ = l_Lean_MessageData_ofExpr(v_head_434_);
v___x_441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_439_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
v___x_442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
lean_ctor_set(v___x_442_, 1, v___x_439_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 1, v_a_432_);
lean_ctor_set(v___x_437_, 0, v___x_442_);
v___x_444_ = v___x_437_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_442_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v_a_432_);
v___x_444_ = v_reuseFailAlloc_446_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
v_a_431_ = v_tail_435_;
v_a_432_ = v___x_444_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__3(void){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_451_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__2));
v___x_452_ = lean_unsigned_to_nat(14u);
v___x_453_ = lean_unsigned_to_nat(22u);
v___x_454_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__1));
v___x_455_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__0));
v___x_456_ = l_mkPanicMessageWithDecl(v___x_455_, v___x_454_, v___x_453_, v___x_452_, v___x_451_);
return v___x_456_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__5(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__4));
v___x_459_ = l_Lean_stringToMessageData(v___x_458_);
return v___x_459_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__7(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__6));
v___x_462_ = l_Lean_stringToMessageData(v___x_461_);
return v___x_462_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__9(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__8));
v___x_465_ = l_Lean_stringToMessageData(v___x_464_);
return v___x_465_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__11(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__10));
v___x_468_ = l_Lean_stringToMessageData(v___x_467_);
return v___x_468_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__13(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__12));
v___x_471_ = l_Lean_stringToMessageData(v___x_470_);
return v___x_471_;
}
}
lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__1(lean_object* v_body_472_, uint8_t v___x_473_, lean_object* v_ys_474_, lean_object* v_vars_475_, lean_object* v_extraParams_476_, uint8_t v_structural_477_, lean_object* v_ref_478_, lean_object* v_xs_479_, lean_object* v_type_x27_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; uint8_t v___x_492_; lean_object* v___x_493_; 
v___x_488_ = lean_box(0);
v___x_489_ = lean_box(v___x_473_);
v___x_490_ = lean_box(v___x_473_);
v___x_491_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_491_, 0, v_body_472_);
lean_closure_set(v___x_491_, 1, v___x_488_);
lean_closure_set(v___x_491_, 2, v___x_489_);
lean_closure_set(v___x_491_, 3, v___x_490_);
lean_closure_set(v___x_491_, 4, v___x_488_);
v___x_492_ = 1;
v___x_493_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_491_, v___x_492_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_552_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_552_ == 0)
{
v___x_496_ = v___x_493_;
v_isShared_497_ = v_isSharedCheck_552_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_493_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_552_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; lean_object* v___f_499_; lean_object* v___y_501_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v___y_504_; lean_object* v___y_505_; lean_object* v___y_506_; lean_object* v___y_507_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; 
v___x_498_ = lean_box(v___x_473_);
lean_inc(v_a_494_);
lean_inc_ref(v_xs_479_);
lean_inc_ref(v_ys_474_);
v___f_499_ = lean_alloc_closure((void*)(l_Lean_Elab_TerminationMeasure_elab___lam__0___boxed), 13, 4);
lean_closure_set(v___f_499_, 0, v_ys_474_);
lean_closure_set(v___f_499_, 1, v_xs_479_);
lean_closure_set(v___f_499_, 2, v_a_494_);
lean_closure_set(v___f_499_, 3, v___x_498_);
if (v_structural_477_ == 0)
{
lean_dec(v_a_494_);
lean_dec_ref(v_xs_479_);
lean_dec_ref(v_ys_474_);
v___y_516_ = v___y_481_;
v___y_517_ = v___y_482_;
v___y_518_ = v___y_483_;
v___y_519_ = v___y_484_;
v___y_520_ = v___y_485_;
v___y_521_ = v___y_486_;
goto v___jp_515_;
}
else
{
lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_525_ = l_Array_append___redArg(v_ys_474_, v_xs_479_);
lean_dec_ref(v_xs_479_);
v___x_526_ = l_Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2(v___x_525_, v_a_494_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
lean_dec_ref(v___f_499_);
lean_del_object(v___x_496_);
lean_dec(v_type_x27_480_);
v___x_527_ = lean_array_to_list(v___x_525_);
v___x_528_ = lean_box(0);
v___x_529_ = l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3(v___x_527_, v___x_528_);
v___x_530_ = l_Lean_MessageData_andList(v___x_529_);
v___x_531_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__5, &l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__5_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__5);
v___x_532_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__7, &l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__7_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__7);
v___x_533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
lean_ctor_set(v___x_533_, 1, v___x_530_);
v___x_534_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__9, &l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__9_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__9);
v___x_535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_533_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
v___x_536_ = l_Lean_indentExpr(v_a_494_);
v___x_537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
v___x_538_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__11, &l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__11_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__11);
v___x_539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_537_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
v___x_540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_531_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
v___x_541_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__13, &l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__13_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__13);
v___x_542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_540_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
v___x_543_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___redArg(v_ref_478_, v___x_542_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
v_a_544_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v___x_543_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_543_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
else
{
lean_dec_ref(v___x_525_);
lean_dec(v_a_494_);
v___y_516_ = v___y_481_;
v___y_517_ = v___y_482_;
v___y_518_ = v___y_483_;
v___y_519_ = v___y_484_;
v___y_520_ = v___y_485_;
v___y_521_ = v___y_486_;
goto v___jp_515_;
}
}
v___jp_500_:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_511_; 
v___x_508_ = lean_array_get_size(v_vars_475_);
v___x_509_ = lean_nat_sub(v_extraParams_476_, v___x_508_);
if (v_isShared_497_ == 0)
{
lean_ctor_set_tag(v___x_496_, 1);
lean_ctor_set(v___x_496_, 0, v___x_509_);
v___x_511_ = v___x_496_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_509_);
v___x_511_ = v_reuseFailAlloc_514_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
uint8_t v___x_512_; lean_object* v___x_513_; 
v___x_512_ = 0;
v___x_513_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___redArg(v___y_507_, v___x_511_, v___f_499_, v___x_512_, v___x_512_, v___y_502_, v___y_505_, v___y_506_, v___y_501_, v___y_504_, v___y_503_);
return v___x_513_;
}
}
v___jp_515_:
{
if (lean_obj_tag(v_type_x27_480_) == 0)
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__3, &l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__3_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__3);
v___x_523_ = l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__1(v___x_522_);
v___y_501_ = v___y_519_;
v___y_502_ = v___y_516_;
v___y_503_ = v___y_521_;
v___y_504_ = v___y_520_;
v___y_505_ = v___y_517_;
v___y_506_ = v___y_518_;
v___y_507_ = v___x_523_;
goto v___jp_500_;
}
else
{
lean_object* v_val_524_; 
v_val_524_ = lean_ctor_get(v_type_x27_480_, 0);
lean_inc(v_val_524_);
lean_dec_ref_known(v_type_x27_480_, 1);
v___y_501_ = v___y_519_;
v___y_502_ = v___y_516_;
v___y_503_ = v___y_521_;
v___y_504_ = v___y_520_;
v___y_505_ = v___y_517_;
v___y_506_ = v___y_518_;
v___y_507_ = v_val_524_;
goto v___jp_500_;
}
}
}
}
else
{
lean_dec(v_type_x27_480_);
lean_dec_ref(v_xs_479_);
lean_dec_ref(v_ys_474_);
return v___x_493_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_TerminationMeasure_elab___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_body_472_ = stack[0].m_obj;
uint8_t v___x_473_ = stack[1].m_num;
lean_object* v_ys_474_ = stack[2].m_obj;
lean_object* v_vars_475_ = stack[3].m_obj;
lean_object* v_extraParams_476_ = stack[4].m_obj;
uint8_t v_structural_477_ = stack[5].m_num;
lean_object* v_ref_478_ = stack[6].m_obj;
lean_object* v_xs_479_ = stack[7].m_obj;
lean_object* v_type_x27_480_ = stack[8].m_obj;
lean_object* v___y_481_ = stack[9].m_obj;
lean_object* v___y_482_ = stack[10].m_obj;
lean_object* v___y_483_ = stack[11].m_obj;
lean_object* v___y_484_ = stack[12].m_obj;
lean_object* v___y_485_ = stack[13].m_obj;
lean_object* v___y_486_ = stack[14].m_obj;
lean_object* v_res_553_;
v_res_553_ = l_Lean_Elab_TerminationMeasure_elab___lam__1(v_body_472_, v___x_473_, v_ys_474_, v_vars_475_, v_extraParams_476_, v_structural_477_, v_ref_478_, v_xs_479_, v_type_x27_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
stack->m_obj
 = v_res_553_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__1___boxed(lean_object* v_body_554_, lean_object* v___x_555_, lean_object* v_ys_556_, lean_object* v_vars_557_, lean_object* v_extraParams_558_, lean_object* v_structural_559_, lean_object* v_ref_560_, lean_object* v_xs_561_, lean_object* v_type_x27_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
uint8_t v___x_6302__boxed_570_; uint8_t v_structural_boxed_571_; lean_object* v_res_572_; 
v___x_6302__boxed_570_ = lean_unbox(v___x_555_);
v_structural_boxed_571_ = lean_unbox(v_structural_559_);
v_res_572_ = l_Lean_Elab_TerminationMeasure_elab___lam__1(v_body_554_, v___x_6302__boxed_570_, v_ys_556_, v_vars_557_, v_extraParams_558_, v_structural_boxed_571_, v_ref_560_, v_xs_561_, v_type_x27_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v_ref_560_);
lean_dec(v_extraParams_558_);
lean_dec_ref(v_vars_557_);
return v_res_572_;
}
}
lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__2(lean_object* v_hint_573_, uint8_t v___x_574_, lean_object* v_extraParams_575_, lean_object* v_ys_576_, lean_object* v_type_x27_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v_ref_585_; uint8_t v_structural_586_; lean_object* v_vars_587_; lean_object* v_body_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___f_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v_ref_585_ = lean_ctor_get(v_hint_573_, 0);
lean_inc(v_ref_585_);
v_structural_586_ = lean_ctor_get_uint8(v_hint_573_, sizeof(void*)*3);
v_vars_587_ = lean_ctor_get(v_hint_573_, 1);
lean_inc_ref_n(v_vars_587_, 2);
v_body_588_ = lean_ctor_get(v_hint_573_, 2);
lean_inc(v_body_588_);
lean_dec_ref(v_hint_573_);
v___x_589_ = lean_box(v___x_574_);
v___x_590_ = lean_box(v_structural_586_);
v___f_591_ = lean_alloc_closure((void*)(l_Lean_Elab_TerminationMeasure_elab___lam__1___boxed), 16, 7);
lean_closure_set(v___f_591_, 0, v_body_588_);
lean_closure_set(v___f_591_, 1, v___x_589_);
lean_closure_set(v___f_591_, 2, v_ys_576_);
lean_closure_set(v___f_591_, 3, v_vars_587_);
lean_closure_set(v___f_591_, 4, v_extraParams_575_);
lean_closure_set(v___f_591_, 5, v___x_590_);
lean_closure_set(v___f_591_, 6, v_ref_585_);
v___x_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_592_, 0, v_type_x27_577_);
v___x_593_ = l_Lean_Elab_Term_elabFunBinders___redArg(v_vars_587_, v___x_592_, v___f_591_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
lean_dec_ref(v_vars_587_);
return v___x_593_;
}
}
LEAN_EXPORT void l_Lean_Elab_TerminationMeasure_elab___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_hint_573_ = stack[0].m_obj;
uint8_t v___x_574_ = stack[1].m_num;
lean_object* v_extraParams_575_ = stack[2].m_obj;
lean_object* v_ys_576_ = stack[3].m_obj;
lean_object* v_type_x27_577_ = stack[4].m_obj;
lean_object* v___y_578_ = stack[5].m_obj;
lean_object* v___y_579_ = stack[6].m_obj;
lean_object* v___y_580_ = stack[7].m_obj;
lean_object* v___y_581_ = stack[8].m_obj;
lean_object* v___y_582_ = stack[9].m_obj;
lean_object* v___y_583_ = stack[10].m_obj;
lean_object* v_res_594_;
v_res_594_ = l_Lean_Elab_TerminationMeasure_elab___lam__2(v_hint_573_, v___x_574_, v_extraParams_575_, v_ys_576_, v_type_x27_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
stack->m_obj
 = v_res_594_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__2___boxed(lean_object* v_hint_595_, lean_object* v___x_596_, lean_object* v_extraParams_597_, lean_object* v_ys_598_, lean_object* v_type_x27_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
uint8_t v___x_6587__boxed_607_; lean_object* v_res_608_; 
v___x_6587__boxed_607_ = lean_unbox(v___x_596_);
v_res_608_ = l_Lean_Elab_TerminationMeasure_elab___lam__2(v_hint_595_, v___x_6587__boxed_607_, v_extraParams_597_, v_ys_598_, v_type_x27_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
return v_res_608_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__3(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_612_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__2));
v___x_613_ = lean_unsigned_to_nat(2u);
v___x_614_ = lean_unsigned_to_nat(54u);
v___x_615_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__1));
v___x_616_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__0));
v___x_617_ = l_mkPanicMessageWithDecl(v___x_616_, v___x_615_, v___x_614_, v___x_613_, v___x_612_);
return v___x_617_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__5(void){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__4));
v___x_620_ = l_Lean_stringToMessageData(v___x_619_);
return v___x_620_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__7(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__6));
v___x_623_ = l_Lean_stringToMessageData(v___x_622_);
return v___x_623_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__9(void){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__8));
v___x_626_ = l_Lean_stringToMessageData(v___x_625_);
return v___x_626_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__13(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__12));
v___x_632_ = l_Lean_stringToMessageData(v___x_631_);
return v___x_632_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__16(void){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__15));
v___x_637_ = l_Lean_MessageData_ofFormat(v___x_636_);
return v___x_637_;
}
}
lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__3(uint8_t v___x_638_, lean_object* v_hint_639_, lean_object* v_arity_640_, lean_object* v_extraParams_641_, lean_object* v_type_642_, lean_object* v___f_643_, lean_object* v_funName_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
if (v___x_638_ == 0)
{
lean_object* v___x_652_; lean_object* v___x_653_; 
lean_dec(v_funName_644_);
lean_dec_ref(v___f_643_);
lean_dec_ref(v_type_642_);
lean_dec(v_extraParams_641_);
v___x_652_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__3, &l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__3_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__3);
v___x_653_ = l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6(v___x_652_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
return v___x_653_;
}
else
{
lean_object* v_ref_654_; uint8_t v_structural_655_; lean_object* v_vars_656_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v_msg_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___x_716_; uint8_t v___x_717_; 
v_ref_654_ = lean_ctor_get(v_hint_639_, 0);
v_structural_655_ = lean_ctor_get_uint8(v_hint_639_, sizeof(void*)*3);
v_vars_656_ = lean_ctor_get(v_hint_639_, 1);
v___x_716_ = lean_array_get_size(v_vars_656_);
v___x_717_ = lean_nat_dec_lt(v_extraParams_641_, v___x_716_);
if (v___x_717_ == 0)
{
lean_dec(v_funName_644_);
v___y_658_ = v___y_645_;
v___y_659_ = v___y_646_;
v___y_660_ = v___y_647_;
v___y_661_ = v___y_648_;
v___y_662_ = v___y_649_;
v___y_663_ = v___y_650_;
goto v___jp_657_;
}
else
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v_msg_728_; lean_object* v___x_729_; lean_object* v_ident_730_; lean_object* v___x_731_; uint8_t v___x_732_; 
lean_dec_ref(v___f_643_);
lean_dec_ref(v_type_642_);
v___x_718_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters(v___x_716_);
v___x_719_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__5, &l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__5_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__5);
v___x_720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_718_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
lean_inc(v_funName_644_);
v___x_721_ = l_Lean_MessageData_ofName(v_funName_644_);
v___x_722_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__7, &l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__7_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__7);
v___x_723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_721_);
lean_ctor_set(v___x_723_, 1, v___x_722_);
v___x_724_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters(v_extraParams_641_);
v___x_725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_725_, 0, v___x_723_);
lean_ctor_set(v___x_725_, 1, v___x_724_);
v___x_726_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__9, &l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__9_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__9);
v___x_727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_725_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
v_msg_728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_728_, 0, v___x_720_);
lean_ctor_set(v_msg_728_, 1, v___x_727_);
v___x_729_ = lean_unsigned_to_nat(0u);
v_ident_730_ = lean_array_fget_borrowed(v_vars_656_, v___x_729_);
v___x_731_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__11));
lean_inc(v_ident_730_);
v___x_732_ = l_Lean_Syntax_isOfKind(v_ident_730_, v___x_731_);
if (v___x_732_ == 0)
{
lean_dec(v_funName_644_);
v_msg_700_ = v_msg_728_;
v___y_701_ = v___y_645_;
v___y_702_ = v___y_646_;
v___y_703_ = v___y_647_;
v___y_704_ = v___y_648_;
v___y_705_ = v___y_649_;
v___y_706_ = v___y_650_;
goto v___jp_699_;
}
else
{
lean_object* v___x_733_; uint8_t v___x_734_; 
v___x_733_ = l_Lean_TSyntax_getId(v_ident_730_);
v___x_734_ = l_Lean_Name_isSuffixOf(v___x_733_, v_funName_644_);
lean_dec(v_funName_644_);
lean_dec(v___x_733_);
if (v___x_734_ == 0)
{
v_msg_700_ = v_msg_728_;
v___y_701_ = v___y_645_;
v___y_702_ = v___y_646_;
v___y_703_ = v___y_647_;
v___y_704_ = v___y_648_;
v___y_705_ = v___y_649_;
v___y_706_ = v___y_650_;
goto v___jp_699_;
}
else
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v_msg_738_; 
v___x_735_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__13, &l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__13_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__13);
v___x_736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_736_, 0, v_msg_728_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v___x_737_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__16, &l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__16_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__16);
v_msg_738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_738_, 0, v___x_736_);
lean_ctor_set(v_msg_738_, 1, v___x_737_);
v_msg_700_ = v_msg_738_;
v___y_701_ = v___y_645_;
v___y_702_ = v___y_646_;
v___y_703_ = v___y_647_;
v___y_704_ = v___y_648_;
v___y_705_ = v___y_649_;
v___y_706_ = v___y_650_;
goto v___jp_699_;
}
}
}
v___jp_657_:
{
lean_object* v___x_664_; lean_object* v___x_665_; uint8_t v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_664_ = lean_nat_sub(v_arity_640_, v_extraParams_641_);
lean_dec(v_extraParams_641_);
v___x_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
v___x_666_ = 0;
v___x_667_ = lean_box(v___x_638_);
v___x_668_ = lean_box(v___x_666_);
v___x_669_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___boxed), 13, 6);
lean_closure_set(v___x_669_, 0, lean_box(0));
lean_closure_set(v___x_669_, 1, v_type_642_);
lean_closure_set(v___x_669_, 2, v___x_665_);
lean_closure_set(v___x_669_, 3, v___f_643_);
lean_closure_set(v___x_669_, 4, v___x_667_);
lean_closure_set(v___x_669_, 5, v___x_668_);
v___x_670_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_669_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; uint8_t v___x_672_; lean_object* v___x_673_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc_n(v_a_671_, 2);
lean_dec_ref_known(v___x_670_, 1);
v___x_672_ = 0;
v___x_673_ = l_Lean_Meta_check(v_a_671_, v___x_672_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_681_; 
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_681_ == 0)
{
lean_object* v_unused_682_; 
v_unused_682_ = lean_ctor_get(v___x_673_, 0);
lean_dec(v_unused_682_);
v___x_675_ = v___x_673_;
v_isShared_676_ = v_isSharedCheck_681_;
goto v_resetjp_674_;
}
else
{
lean_dec(v___x_673_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_681_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_677_; lean_object* v___x_679_; 
lean_inc(v_ref_654_);
v___x_677_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_677_, 0, v_ref_654_);
lean_ctor_set(v___x_677_, 1, v_a_671_);
lean_ctor_set_uint8(v___x_677_, sizeof(void*)*2, v_structural_655_);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 0, v___x_677_);
v___x_679_ = v___x_675_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_677_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
else
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
lean_dec(v_a_671_);
v_a_683_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v___x_673_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_673_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_683_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
v_a_691_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_670_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_670_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
v___jp_699_:
{
lean_object* v___x_707_; lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
v___x_707_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___redArg(v_ref_654_, v_msg_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
v_a_708_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_707_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_707_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_TerminationMeasure_elab___lam__3_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_638_ = stack[0].m_num;
lean_object* v_hint_639_ = stack[1].m_obj;
lean_object* v_arity_640_ = stack[2].m_obj;
lean_object* v_extraParams_641_ = stack[3].m_obj;
lean_object* v_type_642_ = stack[4].m_obj;
lean_object* v___f_643_ = stack[5].m_obj;
lean_object* v_funName_644_ = stack[6].m_obj;
lean_object* v___y_645_ = stack[7].m_obj;
lean_object* v___y_646_ = stack[8].m_obj;
lean_object* v___y_647_ = stack[9].m_obj;
lean_object* v___y_648_ = stack[10].m_obj;
lean_object* v___y_649_ = stack[11].m_obj;
lean_object* v___y_650_ = stack[12].m_obj;
lean_object* v_res_739_;
v_res_739_ = l_Lean_Elab_TerminationMeasure_elab___lam__3(v___x_638_, v_hint_639_, v_arity_640_, v_extraParams_641_, v_type_642_, v___f_643_, v_funName_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
stack->m_obj
 = v_res_739_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__3___boxed(lean_object* v___x_740_, lean_object* v_hint_741_, lean_object* v_arity_742_, lean_object* v_extraParams_743_, lean_object* v_type_744_, lean_object* v___f_745_, lean_object* v_funName_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
uint8_t v___x_6700__boxed_754_; lean_object* v_res_755_; 
v___x_6700__boxed_754_ = lean_unbox(v___x_740_);
v_res_755_ = l_Lean_Elab_TerminationMeasure_elab___lam__3(v___x_6700__boxed_754_, v_hint_741_, v_arity_742_, v_extraParams_743_, v_type_744_, v___f_745_, v_funName_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v_arity_742_);
lean_dec_ref(v_hint_741_);
return v_res_755_;
}
}
lean_object* l_Lean_Elab_TerminationMeasure_elab(lean_object* v_funName_756_, lean_object* v_type_757_, lean_object* v_arity_758_, lean_object* v_extraParams_759_, lean_object* v_hint_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_){
_start:
{
uint8_t v___x_768_; lean_object* v___x_769_; lean_object* v___f_770_; lean_object* v___x_771_; lean_object* v___y_772_; lean_object* v___x_773_; 
v___x_768_ = lean_nat_dec_le(v_extraParams_759_, v_arity_758_);
v___x_769_ = lean_box(v___x_768_);
lean_inc(v_extraParams_759_);
lean_inc_ref(v_hint_760_);
v___f_770_ = lean_alloc_closure((void*)(l_Lean_Elab_TerminationMeasure_elab___lam__2___boxed), 12, 3);
lean_closure_set(v___f_770_, 0, v_hint_760_);
lean_closure_set(v___f_770_, 1, v___x_769_);
lean_closure_set(v___f_770_, 2, v_extraParams_759_);
v___x_771_ = lean_box(v___x_768_);
lean_inc(v_funName_756_);
v___y_772_ = lean_alloc_closure((void*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___boxed), 14, 7);
lean_closure_set(v___y_772_, 0, v___x_771_);
lean_closure_set(v___y_772_, 1, v_hint_760_);
lean_closure_set(v___y_772_, 2, v_arity_758_);
lean_closure_set(v___y_772_, 3, v_extraParams_759_);
lean_closure_set(v___y_772_, 4, v_type_757_);
lean_closure_set(v___y_772_, 5, v___f_770_);
lean_closure_set(v___y_772_, 6, v_funName_756_);
v___x_773_ = l_Lean_Elab_Term_withDeclName___redArg(v_funName_756_, v___y_772_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_);
return v___x_773_;
}
}
LEAN_EXPORT void l_Lean_Elab_TerminationMeasure_elab_0interp(lean_interpreter_value* stack)
{
lean_object* v_funName_756_ = stack[0].m_obj;
lean_object* v_type_757_ = stack[1].m_obj;
lean_object* v_arity_758_ = stack[2].m_obj;
lean_object* v_extraParams_759_ = stack[3].m_obj;
lean_object* v_hint_760_ = stack[4].m_obj;
lean_object* v_a_761_ = stack[5].m_obj;
lean_object* v_a_762_ = stack[6].m_obj;
lean_object* v_a_763_ = stack[7].m_obj;
lean_object* v_a_764_ = stack[8].m_obj;
lean_object* v_a_765_ = stack[9].m_obj;
lean_object* v_a_766_ = stack[10].m_obj;
lean_object* v_res_774_;
v_res_774_ = l_Lean_Elab_TerminationMeasure_elab(v_funName_756_, v_type_757_, v_arity_758_, v_extraParams_759_, v_hint_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_);
stack->m_obj
 = v_res_774_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___boxed(lean_object* v_funName_775_, lean_object* v_type_776_, lean_object* v_arity_777_, lean_object* v_extraParams_778_, lean_object* v_hint_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_Elab_TerminationMeasure_elab(v_funName_775_, v_type_776_, v_arity_777_, v_extraParams_778_, v_hint_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
lean_dec(v_a_783_);
lean_dec_ref(v_a_782_);
lean_dec(v_a_781_);
lean_dec_ref(v_a_780_);
return v_res_787_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4(lean_object* v_00_u03b1_788_, lean_object* v_ref_789_, lean_object* v_msg_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___redArg(v_ref_789_, v_msg_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
return v___x_798_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_789_ = stack[1].m_obj;
lean_object* v_msg_790_ = stack[2].m_obj;
lean_object* v___y_791_ = stack[3].m_obj;
lean_object* v___y_792_ = stack[4].m_obj;
lean_object* v___y_793_ = stack[5].m_obj;
lean_object* v___y_794_ = stack[6].m_obj;
lean_object* v___y_795_ = stack[7].m_obj;
lean_object* v___y_796_ = stack[8].m_obj;
lean_object* v_res_799_;
v_res_799_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4(lean_box(0), v_ref_789_, v_msg_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
stack->m_obj
 = v_res_799_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___boxed(lean_object* v_00_u03b1_800_, lean_object* v_ref_801_, lean_object* v_msg_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4(v_00_u03b1_800_, v_ref_801_, v_msg_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v_ref_801_);
return v_res_810_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5(lean_object* v_00_u03b1_811_, lean_object* v_msg_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5___redArg(v_msg_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
return v___x_820_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_812_ = stack[1].m_obj;
lean_object* v___y_813_ = stack[2].m_obj;
lean_object* v___y_814_ = stack[3].m_obj;
lean_object* v___y_815_ = stack[4].m_obj;
lean_object* v___y_816_ = stack[5].m_obj;
lean_object* v___y_817_ = stack[6].m_obj;
lean_object* v___y_818_ = stack[7].m_obj;
lean_object* v_res_821_;
v_res_821_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5(lean_box(0), v_msg_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
stack->m_obj
 = v_res_821_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5___boxed(lean_object* v_00_u03b1_822_, lean_object* v_msg_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5(v_00_u03b1_822_, v_msg_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
return v_res_831_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9(lean_object* v_msgData_832_, lean_object* v_macroStack_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg(v_msgData_832_, v_macroStack_833_, v___y_838_);
return v___x_841_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_832_ = stack[0].m_obj;
lean_object* v_macroStack_833_ = stack[1].m_obj;
lean_object* v___y_834_ = stack[2].m_obj;
lean_object* v___y_835_ = stack[3].m_obj;
lean_object* v___y_836_ = stack[4].m_obj;
lean_object* v___y_837_ = stack[5].m_obj;
lean_object* v___y_838_ = stack[6].m_obj;
lean_object* v___y_839_ = stack[7].m_obj;
lean_object* v_res_842_;
v_res_842_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9(v_msgData_832_, v_macroStack_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
stack->m_obj
 = v_res_842_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___boxed(lean_object* v_msgData_843_, lean_object* v_macroStack_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9(v_msgData_843_, v_macroStack_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
return v_res_852_;
}
}
lean_object* l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1(lean_object* v_msg_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v___f_860_; lean_object* v___x_288__overap_861_; lean_object* v___x_862_; 
v___f_860_ = ((lean_object*)(l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1___closed__0));
v___x_288__overap_861_ = lean_panic_fn_borrowed(v___f_860_, v_msg_854_);
lean_inc(v___y_858_);
lean_inc_ref(v___y_857_);
lean_inc(v___y_856_);
lean_inc_ref(v___y_855_);
v___x_862_ = lean_apply_5(v___x_288__overap_861_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, lean_box(0));
return v___x_862_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_854_ = stack[0].m_obj;
lean_object* v___y_855_ = stack[1].m_obj;
lean_object* v___y_856_ = stack[2].m_obj;
lean_object* v___y_857_ = stack[3].m_obj;
lean_object* v___y_858_ = stack[4].m_obj;
lean_object* v_res_863_;
v_res_863_ = l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1(v_msg_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
stack->m_obj
 = v_res_863_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1___boxed(lean_object* v_msg_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1(v_msg_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
return v_res_870_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg___lam__0(lean_object* v_k_871_, lean_object* v_b_872_, lean_object* v_c_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v___x_879_; 
lean_inc(v___y_877_);
lean_inc_ref(v___y_876_);
lean_inc(v___y_875_);
lean_inc_ref(v___y_874_);
v___x_879_ = lean_apply_7(v_k_871_, v_b_872_, v_c_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, lean_box(0));
return v___x_879_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_871_ = stack[0].m_obj;
lean_object* v_b_872_ = stack[1].m_obj;
lean_object* v_c_873_ = stack[2].m_obj;
lean_object* v___y_874_ = stack[3].m_obj;
lean_object* v___y_875_ = stack[4].m_obj;
lean_object* v___y_876_ = stack[5].m_obj;
lean_object* v___y_877_ = stack[6].m_obj;
lean_object* v_res_880_;
v_res_880_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg___lam__0(v_k_871_, v_b_872_, v_c_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
stack->m_obj
 = v_res_880_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg___lam__0___boxed(lean_object* v_k_881_, lean_object* v_b_882_, lean_object* v_c_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg___lam__0(v_k_881_, v_b_882_, v_c_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
return v_res_889_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg(lean_object* v_e_890_, lean_object* v_k_891_, uint8_t v_cleanupAnnotations_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v___f_898_; uint8_t v___x_899_; uint8_t v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v___f_898_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_898_, 0, v_k_891_);
v___x_899_ = 1;
v___x_900_ = 0;
v___x_901_ = lean_box(0);
v___x_902_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_890_, v___x_899_, v___x_900_, v___x_899_, v___x_900_, v___x_901_, v___f_898_, v_cleanupAnnotations_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_902_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_902_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
else
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
v_a_911_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_902_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_902_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_911_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_890_ = stack[0].m_obj;
lean_object* v_k_891_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_892_ = stack[2].m_num;
lean_object* v___y_893_ = stack[3].m_obj;
lean_object* v___y_894_ = stack[4].m_obj;
lean_object* v___y_895_ = stack[5].m_obj;
lean_object* v___y_896_ = stack[6].m_obj;
lean_object* v_res_919_;
v_res_919_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg(v_e_890_, v_k_891_, v_cleanupAnnotations_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
stack->m_obj
 = v_res_919_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg___boxed(lean_object* v_e_920_, lean_object* v_k_921_, lean_object* v_cleanupAnnotations_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_928_; lean_object* v_res_929_; 
v_cleanupAnnotations_boxed_928_ = lean_unbox(v_cleanupAnnotations_922_);
v_res_929_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg(v_e_920_, v_k_921_, v_cleanupAnnotations_boxed_928_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
return v_res_929_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2(lean_object* v_00_u03b1_930_, lean_object* v_e_931_, lean_object* v_k_932_, uint8_t v_cleanupAnnotations_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg(v_e_931_, v_k_932_, v_cleanupAnnotations_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
return v___x_939_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_931_ = stack[1].m_obj;
lean_object* v_k_932_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_933_ = stack[3].m_num;
lean_object* v___y_934_ = stack[4].m_obj;
lean_object* v___y_935_ = stack[5].m_obj;
lean_object* v___y_936_ = stack[6].m_obj;
lean_object* v___y_937_ = stack[7].m_obj;
lean_object* v_res_940_;
v_res_940_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2(lean_box(0), v_e_931_, v_k_932_, v_cleanupAnnotations_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
stack->m_obj
 = v_res_940_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___boxed(lean_object* v_00_u03b1_941_, lean_object* v_e_942_, lean_object* v_k_943_, lean_object* v_cleanupAnnotations_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_950_; lean_object* v_res_951_; 
v_cleanupAnnotations_boxed_950_ = lean_unbox(v_cleanupAnnotations_944_);
v_res_951_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2(v_00_u03b1_941_, v_e_942_, v_k_943_, v_cleanupAnnotations_boxed_950_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0_spec__3(lean_object* v_xs_952_, lean_object* v_v_953_, lean_object* v_i_954_){
_start:
{
lean_object* v___x_955_; uint8_t v___x_956_; 
v___x_955_ = lean_array_get_size(v_xs_952_);
v___x_956_ = lean_nat_dec_lt(v_i_954_, v___x_955_);
if (v___x_956_ == 0)
{
lean_object* v___x_957_; 
lean_dec(v_i_954_);
v___x_957_ = lean_box(0);
return v___x_957_;
}
else
{
lean_object* v___x_958_; uint8_t v___x_959_; 
v___x_958_ = lean_array_fget_borrowed(v_xs_952_, v_i_954_);
v___x_959_ = lean_expr_eqv(v___x_958_, v_v_953_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = lean_unsigned_to_nat(1u);
v___x_961_ = lean_nat_add(v_i_954_, v___x_960_);
lean_dec(v_i_954_);
v_i_954_ = v___x_961_;
goto _start;
}
else
{
lean_object* v___x_963_; 
v___x_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_963_, 0, v_i_954_);
return v___x_963_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0_spec__3___boxed(lean_object* v_xs_964_, lean_object* v_v_965_, lean_object* v_i_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0_spec__3(v_xs_964_, v_v_965_, v_i_966_);
lean_dec_ref(v_v_965_);
lean_dec_ref(v_xs_964_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0(lean_object* v_xs_968_, lean_object* v_v_969_){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = lean_unsigned_to_nat(0u);
v___x_971_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0_spec__3(v_xs_968_, v_v_969_, v___x_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0___boxed(lean_object* v_xs_972_, lean_object* v_v_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0(v_xs_972_, v_v_973_);
lean_dec_ref(v_v_973_);
lean_dec_ref(v_xs_972_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0(lean_object* v_xs_975_, lean_object* v_v_976_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0(v_xs_975_, v_v_976_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v___x_978_; 
v___x_978_ = lean_box(0);
return v___x_978_;
}
else
{
lean_object* v_val_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_986_; 
v_val_979_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_986_ == 0)
{
v___x_981_ = v___x_977_;
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_val_979_);
lean_dec(v___x_977_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_984_; 
if (v_isShared_982_ == 0)
{
v___x_984_ = v___x_981_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_val_979_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0___boxed(lean_object* v_xs_987_, lean_object* v_v_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0(v_xs_987_, v_v_988_);
lean_dec_ref(v_v_988_);
lean_dec_ref(v_xs_987_);
return v_res_989_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_992_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__1));
v___x_993_ = lean_unsigned_to_nat(8u);
v___x_994_ = lean_unsigned_to_nat(93u);
v___x_995_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__0));
v___x_996_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__0));
v___x_997_ = l_mkPanicMessageWithDecl(v___x_996_, v___x_995_, v___x_994_, v___x_993_, v___x_992_);
return v___x_997_;
}
}
lean_object* l_Lean_Elab_TerminationMeasure_structuralArg___lam__0(lean_object* v_ys_998_, lean_object* v_e_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0(v_ys_998_, v_e_999_);
if (lean_obj_tag(v___x_1005_) == 1)
{
lean_object* v_val_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
v_val_1006_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_1005_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_val_1006_);
lean_dec(v___x_1005_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
lean_ctor_set_tag(v___x_1008_, 0);
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_val_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
else
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
lean_dec(v___x_1005_);
v___x_1014_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__2, &l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__2_once, _init_l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__2);
v___x_1015_ = l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1(v___x_1014_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
return v___x_1015_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_TerminationMeasure_structuralArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ys_998_ = stack[0].m_obj;
lean_object* v_e_999_ = stack[1].m_obj;
lean_object* v___y_1000_ = stack[2].m_obj;
lean_object* v___y_1001_ = stack[3].m_obj;
lean_object* v___y_1002_ = stack[4].m_obj;
lean_object* v___y_1003_ = stack[5].m_obj;
lean_object* v_res_1016_;
v_res_1016_ = l_Lean_Elab_TerminationMeasure_structuralArg___lam__0(v_ys_998_, v_e_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
stack->m_obj
 = v_res_1016_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___boxed(lean_object* v_ys_1017_, lean_object* v_e_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Lean_Elab_TerminationMeasure_structuralArg___lam__0(v_ys_1017_, v_e_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec_ref(v_e_1018_);
lean_dec_ref(v_ys_1017_);
return v_res_1024_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_structuralArg___closed__1(void){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1026_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_structuralArg___closed__0));
v___x_1027_ = lean_unsigned_to_nat(2u);
v___x_1028_ = lean_unsigned_to_nat(90u);
v___x_1029_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__0));
v___x_1030_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__0));
v___x_1031_ = l_mkPanicMessageWithDecl(v___x_1030_, v___x_1029_, v___x_1028_, v___x_1027_, v___x_1026_);
return v___x_1031_;
}
}
lean_object* l_Lean_Elab_TerminationMeasure_structuralArg(lean_object* v_measure_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_){
_start:
{
uint8_t v_structural_1039_; 
v_structural_1039_ = lean_ctor_get_uint8(v_measure_1033_, sizeof(void*)*2);
if (v_structural_1039_ == 0)
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
lean_dec_ref(v_measure_1033_);
v___x_1040_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_structuralArg___closed__1, &l_Lean_Elab_TerminationMeasure_structuralArg___closed__1_once, _init_l_Lean_Elab_TerminationMeasure_structuralArg___closed__1);
v___x_1041_ = l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1(v___x_1040_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_);
return v___x_1041_;
}
else
{
lean_object* v_fn_1042_; lean_object* v___f_1043_; uint8_t v___x_1044_; lean_object* v___x_1045_; 
v_fn_1042_ = lean_ctor_get(v_measure_1033_, 1);
lean_inc_ref(v_fn_1042_);
lean_dec_ref(v_measure_1033_);
v___f_1043_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_structuralArg___closed__2));
v___x_1044_ = 0;
v___x_1045_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg(v_fn_1042_, v___f_1043_, v___x_1044_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_);
return v___x_1045_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_TerminationMeasure_structuralArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_measure_1033_ = stack[0].m_obj;
lean_object* v_a_1034_ = stack[1].m_obj;
lean_object* v_a_1035_ = stack[2].m_obj;
lean_object* v_a_1036_ = stack[3].m_obj;
lean_object* v_a_1037_ = stack[4].m_obj;
lean_object* v_res_1046_;
v_res_1046_ = l_Lean_Elab_TerminationMeasure_structuralArg(v_measure_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_);
stack->m_obj
 = v_res_1046_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_structuralArg___boxed(lean_object* v_measure_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_Elab_TerminationMeasure_structuralArg(v_measure_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
lean_dec(v_a_1051_);
lean_dec_ref(v_a_1050_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
return v_res_1053_;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2___redArg(lean_object* v___y_1054_){
_start:
{
lean_object* v_subExpr_1056_; lean_object* v_expr_1057_; lean_object* v___x_1058_; 
v_subExpr_1056_ = lean_ctor_get(v___y_1054_, 3);
v_expr_1057_ = lean_ctor_get(v_subExpr_1056_, 0);
lean_inc_ref(v_expr_1057_);
v___x_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1058_, 0, v_expr_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT void l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1054_ = stack[0].m_obj;
lean_object* v_res_1059_;
v_res_1059_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2___redArg(v___y_1054_);
stack->m_obj
 = v_res_1059_;
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2___redArg___boxed(lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2___redArg(v___y_1060_);
lean_dec_ref(v___y_1060_);
return v_res_1062_;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2(lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2___redArg(v___y_1063_);
return v___x_1070_;
}
}
LEAN_EXPORT void l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1063_ = stack[0].m_obj;
lean_object* v___y_1064_ = stack[1].m_obj;
lean_object* v___y_1065_ = stack[2].m_obj;
lean_object* v___y_1066_ = stack[3].m_obj;
lean_object* v___y_1067_ = stack[4].m_obj;
lean_object* v___y_1068_ = stack[5].m_obj;
lean_object* v_res_1071_;
v_res_1071_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2(v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
stack->m_obj
 = v_res_1071_;
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2___boxed(lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2(v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
return v_res_1079_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0(lean_object* v_____do__lift_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
uint8_t v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1088_ = 0;
v___x_1089_ = l_Lean_SourceInfo_fromRef(v_____do__lift_1080_, v___x_1088_);
v___x_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_____do__lift_1080_ = stack[0].m_obj;
lean_object* v___y_1081_ = stack[1].m_obj;
lean_object* v___y_1082_ = stack[2].m_obj;
lean_object* v___y_1083_ = stack[3].m_obj;
lean_object* v___y_1084_ = stack[4].m_obj;
lean_object* v___y_1085_ = stack[5].m_obj;
lean_object* v___y_1086_ = stack[6].m_obj;
lean_object* v_res_1091_;
v_res_1091_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0(v_____do__lift_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
stack->m_obj
 = v_res_1091_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0___boxed(lean_object* v_____do__lift_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0(v_____do__lift_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v_____do__lift_1092_);
return v_res_1100_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg(lean_object* v_a_1110_){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; uint8_t v___x_1114_; 
v___x_1112_ = lean_array_get_size(v_a_1110_);
v___x_1113_ = lean_unsigned_to_nat(0u);
v___x_1114_ = lean_nat_dec_eq(v___x_1112_, v___x_1113_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; uint8_t v___x_1120_; 
v___x_1115_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4));
v___x_1116_ = lean_box(0);
v___x_1117_ = lean_unsigned_to_nat(1u);
v___x_1118_ = lean_nat_sub(v___x_1112_, v___x_1117_);
v___x_1119_ = lean_array_get_borrowed(v___x_1116_, v_a_1110_, v___x_1118_);
lean_dec(v___x_1118_);
lean_inc(v___x_1119_);
v___x_1120_ = l_Lean_Syntax_isOfKind(v___x_1119_, v___x_1115_);
if (v___x_1120_ == 0)
{
lean_object* v___x_1121_; 
v___x_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1121_, 0, v_a_1110_);
return v___x_1121_;
}
else
{
lean_object* v___x_1122_; 
v___x_1122_ = lean_array_pop(v_a_1110_);
v_a_1110_ = v___x_1122_;
goto _start;
}
}
else
{
lean_object* v___x_1124_; 
v___x_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1124_, 0, v_a_1110_);
return v___x_1124_;
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1110_ = stack[0].m_obj;
lean_object* v_res_1125_;
v_res_1125_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg(v_a_1110_);
stack->m_obj
 = v_res_1125_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___boxed(lean_object* v_a_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg(v_a_1126_);
return v_res_1128_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__0(lean_object* v_a_1129_, lean_object* v___x_1130_, size_t v_sz_1131_, size_t v_i_1132_, lean_object* v_bs_1133_){
_start:
{
uint8_t v___x_1134_; 
v___x_1134_ = lean_usize_dec_lt(v_i_1132_, v_sz_1131_);
if (v___x_1134_ == 0)
{
lean_dec(v___x_1130_);
return v_bs_1133_;
}
else
{
lean_object* v_v_1135_; lean_object* v___x_1136_; lean_object* v_bs_x27_1137_; lean_object* v___y_1139_; lean_object* v___x_1144_; uint8_t v___x_1145_; 
v_v_1135_ = lean_array_uget(v_bs_1133_, v_i_1132_);
v___x_1136_ = lean_unsigned_to_nat(0u);
v_bs_x27_1137_ = lean_array_uset(v_bs_1133_, v_i_1132_, v___x_1136_);
v___x_1144_ = l_Lean_TSyntax_getId(v_v_1135_);
v___x_1145_ = l_Lean_Syntax_hasIdent(v___x_1144_, v_a_1129_);
lean_dec(v___x_1144_);
if (v___x_1145_ == 0)
{
lean_dec(v_v_1135_);
lean_inc(v___x_1130_);
v___y_1139_ = v___x_1130_;
goto v___jp_1138_;
}
else
{
v___y_1139_ = v_v_1135_;
goto v___jp_1138_;
}
v___jp_1138_:
{
size_t v___x_1140_; size_t v___x_1141_; lean_object* v___x_1142_; 
v___x_1140_ = ((size_t)1ULL);
v___x_1141_ = lean_usize_add(v_i_1132_, v___x_1140_);
v___x_1142_ = lean_array_uset(v_bs_x27_1137_, v_i_1132_, v___y_1139_);
v_i_1132_ = v___x_1141_;
v_bs_1133_ = v___x_1142_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1129_ = stack[0].m_obj;
lean_object* v___x_1130_ = stack[1].m_obj;
size_t v_sz_1131_ = stack[2].m_num;
size_t v_i_1132_ = stack[3].m_num;
lean_object* v_bs_1133_ = stack[4].m_obj;
lean_object* v_res_1146_;
v_res_1146_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__0(v_a_1129_, v___x_1130_, v_sz_1131_, v_i_1132_, v_bs_1133_);
stack->m_obj
 = v_res_1146_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__0___boxed(lean_object* v_a_1147_, lean_object* v___x_1148_, lean_object* v_sz_1149_, lean_object* v_i_1150_, lean_object* v_bs_1151_){
_start:
{
size_t v_sz_boxed_1152_; size_t v_i_boxed_1153_; lean_object* v_res_1154_; 
v_sz_boxed_1152_ = lean_unbox_usize(v_sz_1149_);
lean_dec(v_sz_1149_);
v_i_boxed_1153_ = lean_unbox_usize(v_i_1150_);
lean_dec(v_i_1150_);
v_res_1154_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__0(v_a_1147_, v___x_1148_, v_sz_boxed_1152_, v_i_boxed_1153_, v_bs_1151_);
lean_dec(v_a_1147_);
return v_res_1154_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7(void){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = l_Array_mkArray0___redArg();
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__1___boxed(lean_object* v_a_1170_, lean_object* v_measure_1171_, lean_object* v_n_1172_, lean_object* v_n_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__1(v_a_1170_, v_measure_1171_, v_n_1172_, v_n_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v_n_1172_);
return v_res_1181_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go(lean_object* v_measure_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_){
_start:
{
lean_object* v_zero_1192_; uint8_t v_isZero_1193_; 
v_zero_1192_ = lean_unsigned_to_nat(0u);
v_isZero_1193_ = lean_nat_dec_eq(v_a_1183_, v_zero_1192_);
if (v_isZero_1193_ == 1)
{
lean_object* v___x_1194_; 
v___x_1194_ = l_Lean_PrettyPrinter_Delaborator_delab(v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v_ref_1196_; lean_object* v___x_1197_; lean_object* v_a_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; size_t v_sz_1203_; size_t v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_a_1195_);
lean_dec_ref_known(v___x_1194_, 1);
v_ref_1196_ = lean_ctor_get(v_a_1189_, 2);
v___x_1197_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0(v_ref_1196_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_);
v_a_1198_ = lean_ctor_get(v___x_1197_, 0);
lean_inc_n(v_a_1198_, 2);
lean_dec_ref(v___x_1197_);
v___x_1199_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4));
v___x_1200_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__0));
v___x_1201_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1201_, 0, v_a_1198_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
v___x_1202_ = l_Lean_Syntax_node1(v_a_1198_, v___x_1199_, v___x_1201_);
v_sz_1203_ = lean_array_size(v_a_1184_);
v___x_1204_ = ((size_t)0ULL);
v___x_1205_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__0(v_a_1195_, v___x_1202_, v_sz_1203_, v___x_1204_, v_a_1184_);
v___x_1206_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg(v___x_1205_);
if (lean_obj_tag(v___x_1206_) == 0)
{
uint8_t v_structural_1207_; 
v_structural_1207_ = lean_ctor_get_uint8(v_measure_1182_, sizeof(void*)*2);
lean_dec_ref(v_measure_1182_);
if (v_structural_1207_ == 0)
{
lean_object* v_a_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1246_; 
v_a_1208_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1210_ = v___x_1206_;
v_isShared_1211_ = v_isSharedCheck_1246_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_a_1208_);
lean_dec(v___x_1206_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1246_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1212_; uint8_t v___x_1213_; 
v___x_1212_ = lean_array_get_size(v_a_1208_);
v___x_1213_ = lean_nat_dec_eq(v___x_1212_, v_zero_1192_);
if (v___x_1213_ == 0)
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1228_; 
v___x_1214_ = l_Lean_SourceInfo_fromRef(v_ref_1196_, v___x_1213_);
v___x_1215_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3));
v___x_1216_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__4));
lean_inc_n(v___x_1214_, 5);
v___x_1217_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1214_);
lean_ctor_set(v___x_1217_, 1, v___x_1216_);
v___x_1218_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__6));
v___x_1219_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7, &l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7);
v___x_1220_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1214_);
lean_ctor_set(v___x_1220_, 1, v___x_1218_);
lean_ctor_set(v___x_1220_, 2, v___x_1219_);
v___x_1221_ = l_Array_append___redArg(v___x_1219_, v_a_1208_);
lean_dec(v_a_1208_);
v___x_1222_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1214_);
lean_ctor_set(v___x_1222_, 1, v___x_1218_);
lean_ctor_set(v___x_1222_, 2, v___x_1221_);
v___x_1223_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__8));
v___x_1224_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1214_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
v___x_1225_ = l_Lean_Syntax_node2(v___x_1214_, v___x_1218_, v___x_1222_, v___x_1224_);
v___x_1226_ = l_Lean_Syntax_node4(v___x_1214_, v___x_1215_, v___x_1217_, v___x_1220_, v___x_1225_, v_a_1195_);
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 0, v___x_1226_);
v___x_1228_ = v___x_1210_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1226_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
else
{
lean_object* v___x_1230_; lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1245_; 
lean_del_object(v___x_1210_);
lean_dec(v_a_1208_);
v___x_1230_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0(v_ref_1196_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_);
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1233_ = v___x_1230_;
v_isShared_1234_ = v_isSharedCheck_1245_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1230_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1245_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1243_; 
v___x_1235_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3));
v___x_1236_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__4));
lean_inc_n(v_a_1231_, 2);
v___x_1237_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1237_, 0, v_a_1231_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
v___x_1238_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__6));
v___x_1239_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7, &l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7);
v___x_1240_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1240_, 0, v_a_1231_);
lean_ctor_set(v___x_1240_, 1, v___x_1238_);
lean_ctor_set(v___x_1240_, 2, v___x_1239_);
lean_inc_ref(v___x_1240_);
v___x_1241_ = l_Lean_Syntax_node4(v_a_1231_, v___x_1235_, v___x_1237_, v___x_1240_, v___x_1240_, v_a_1195_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 0, v___x_1241_);
v___x_1243_ = v___x_1233_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1241_);
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
else
{
lean_object* v_a_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; 
v_a_1247_ = lean_ctor_get(v___x_1206_, 0);
lean_inc(v_a_1247_);
lean_dec_ref_known(v___x_1206_, 1);
v___x_1248_ = lean_array_get_size(v_a_1247_);
v___x_1249_ = lean_nat_dec_eq(v___x_1248_, v_zero_1192_);
if (v___x_1249_ == 0)
{
lean_object* v___x_1250_; lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1272_; 
v___x_1250_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0(v_ref_1196_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_);
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1253_ = v___x_1250_;
v_isShared_1254_ = v_isSharedCheck_1272_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1250_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1272_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1270_; 
v___x_1255_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3));
v___x_1256_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__4));
lean_inc_n(v_a_1251_, 6);
v___x_1257_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1257_, 0, v_a_1251_);
lean_ctor_set(v___x_1257_, 1, v___x_1256_);
v___x_1258_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__6));
v___x_1259_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__9));
v___x_1260_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1260_, 0, v_a_1251_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
v___x_1261_ = l_Lean_Syntax_node1(v_a_1251_, v___x_1258_, v___x_1260_);
v___x_1262_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7, &l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7);
v___x_1263_ = l_Array_append___redArg(v___x_1262_, v_a_1247_);
lean_dec(v_a_1247_);
v___x_1264_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1264_, 0, v_a_1251_);
lean_ctor_set(v___x_1264_, 1, v___x_1258_);
lean_ctor_set(v___x_1264_, 2, v___x_1263_);
v___x_1265_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__8));
v___x_1266_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1266_, 0, v_a_1251_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
v___x_1267_ = l_Lean_Syntax_node2(v_a_1251_, v___x_1258_, v___x_1264_, v___x_1266_);
v___x_1268_ = l_Lean_Syntax_node4(v_a_1251_, v___x_1255_, v___x_1257_, v___x_1261_, v___x_1267_, v_a_1195_);
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 0, v___x_1268_);
v___x_1270_ = v___x_1253_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1268_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
else
{
lean_object* v___x_1273_; lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1291_; 
lean_dec(v_a_1247_);
v___x_1273_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0(v_ref_1196_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_);
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1276_ = v___x_1273_;
v_isShared_1277_ = v_isSharedCheck_1291_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1273_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1291_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1289_; 
v___x_1278_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3));
v___x_1279_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__4));
lean_inc_n(v_a_1274_, 4);
v___x_1280_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1280_, 0, v_a_1274_);
lean_ctor_set(v___x_1280_, 1, v___x_1279_);
v___x_1281_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__6));
v___x_1282_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__9));
v___x_1283_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1283_, 0, v_a_1274_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
v___x_1284_ = l_Lean_Syntax_node1(v_a_1274_, v___x_1281_, v___x_1283_);
v___x_1285_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7, &l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7);
v___x_1286_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1286_, 0, v_a_1274_);
lean_ctor_set(v___x_1286_, 1, v___x_1281_);
lean_ctor_set(v___x_1286_, 2, v___x_1285_);
v___x_1287_ = l_Lean_Syntax_node4(v_a_1274_, v___x_1278_, v___x_1280_, v___x_1284_, v___x_1286_, v_a_1195_);
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 0, v___x_1287_);
v___x_1289_ = v___x_1276_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1287_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
lean_dec(v_a_1195_);
lean_dec_ref(v_measure_1182_);
v_a_1292_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v___x_1206_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1206_);
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
lean_dec_ref(v_a_1184_);
lean_dec_ref(v_measure_1182_);
return v___x_1194_;
}
}
else
{
lean_object* v_one_1300_; lean_object* v_n_1301_; lean_object* v___f_1302_; lean_object* v___x_1303_; lean_object* v_a_1304_; uint8_t v___x_1305_; 
v_one_1300_ = lean_unsigned_to_nat(1u);
v_n_1301_ = lean_nat_sub(v_a_1183_, v_one_1300_);
lean_inc_ref(v_measure_1182_);
lean_inc_ref(v_a_1184_);
v___f_1302_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__1___boxed), 11, 3);
lean_closure_set(v___f_1302_, 0, v_a_1184_);
lean_closure_set(v___f_1302_, 1, v_measure_1182_);
lean_closure_set(v___f_1302_, 2, v_n_1301_);
v___x_1303_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2___redArg(v_a_1185_);
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_a_1304_);
lean_dec_ref(v___x_1303_);
v___x_1305_ = l_Lean_Expr_isLambda(v_a_1304_);
lean_dec(v_a_1304_);
if (v___x_1305_ == 0)
{
lean_dec_ref(v___f_1302_);
v_a_1183_ = v_zero_1192_;
goto _start;
}
else
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
lean_dec_ref(v_a_1184_);
lean_dec_ref(v_measure_1182_);
v___x_1307_ = l_Lean_NameSet_empty;
v___x_1308_ = l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg(v___f_1302_, v_isZero_1193_, v___x_1307_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_);
return v___x_1308_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_measure_1182_ = stack[0].m_obj;
lean_object* v_a_1183_ = stack[1].m_obj;
lean_object* v_a_1184_ = stack[2].m_obj;
lean_object* v_a_1185_ = stack[3].m_obj;
lean_object* v_a_1186_ = stack[4].m_obj;
lean_object* v_a_1187_ = stack[5].m_obj;
lean_object* v_a_1188_ = stack[6].m_obj;
lean_object* v_a_1189_ = stack[7].m_obj;
lean_object* v_a_1190_ = stack[8].m_obj;
lean_object* v_res_1309_;
v_res_1309_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go(v_measure_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_);
stack->m_obj
 = v_res_1309_;
}
lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__1(lean_object* v_a_1310_, lean_object* v_measure_1311_, lean_object* v_n_1312_, lean_object* v_n_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1321_ = lean_array_push(v_a_1310_, v_n_1313_);
v___x_1322_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go(v_measure_1311_, v_n_1312_, v___x_1321_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
return v___x_1322_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1310_ = stack[0].m_obj;
lean_object* v_measure_1311_ = stack[1].m_obj;
lean_object* v_n_1312_ = stack[2].m_obj;
lean_object* v_n_1313_ = stack[3].m_obj;
lean_object* v___y_1314_ = stack[4].m_obj;
lean_object* v___y_1315_ = stack[5].m_obj;
lean_object* v___y_1316_ = stack[6].m_obj;
lean_object* v___y_1317_ = stack[7].m_obj;
lean_object* v___y_1318_ = stack[8].m_obj;
lean_object* v___y_1319_ = stack[9].m_obj;
lean_object* v_res_1323_;
v_res_1323_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__1(v_a_1310_, v_measure_1311_, v_n_1312_, v_n_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
stack->m_obj
 = v_res_1323_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___boxed(lean_object* v_measure_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go(v_measure_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_);
lean_dec(v_a_1332_);
lean_dec_ref(v_a_1331_);
lean_dec(v_a_1330_);
lean_dec_ref(v_a_1329_);
lean_dec(v_a_1328_);
lean_dec_ref(v_a_1327_);
lean_dec(v_a_1325_);
return v_res_1334_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1(lean_object* v_inst_1335_, lean_object* v_a_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg(v_a_1336_);
return v___x_1344_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1336_ = stack[1].m_obj;
lean_object* v___y_1337_ = stack[2].m_obj;
lean_object* v___y_1338_ = stack[3].m_obj;
lean_object* v___y_1339_ = stack[4].m_obj;
lean_object* v___y_1340_ = stack[5].m_obj;
lean_object* v___y_1341_ = stack[6].m_obj;
lean_object* v___y_1342_ = stack[7].m_obj;
lean_object* v_res_1345_;
v_res_1345_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1(lean_box(0), v_a_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
stack->m_obj
 = v_res_1345_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___boxed(lean_object* v_inst_1346_, lean_object* v_a_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1(v_inst_1346_, v_a_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter___redArg(lean_object* v_x_1356_, lean_object* v_x_1357_, lean_object* v_h__1_1358_, lean_object* v_h__2_1359_){
_start:
{
lean_object* v_zero_1360_; uint8_t v_isZero_1361_; 
v_zero_1360_ = lean_unsigned_to_nat(0u);
v_isZero_1361_ = lean_nat_dec_eq(v_x_1356_, v_zero_1360_);
if (v_isZero_1361_ == 1)
{
lean_object* v___x_1362_; 
lean_dec(v_h__2_1359_);
v___x_1362_ = lean_apply_1(v_h__1_1358_, v_x_1357_);
return v___x_1362_;
}
else
{
lean_object* v_one_1363_; lean_object* v_n_1364_; lean_object* v___x_1365_; 
lean_dec(v_h__1_1358_);
v_one_1363_ = lean_unsigned_to_nat(1u);
v_n_1364_ = lean_nat_sub(v_x_1356_, v_one_1363_);
v___x_1365_ = lean_apply_2(v_h__2_1359_, v_n_1364_, v_x_1357_);
return v___x_1365_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter___redArg___boxed(lean_object* v_x_1366_, lean_object* v_x_1367_, lean_object* v_h__1_1368_, lean_object* v_h__2_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter___redArg(v_x_1366_, v_x_1367_, v_h__1_1368_, v_h__2_1369_);
lean_dec(v_x_1366_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter(lean_object* v_motive_1371_, lean_object* v_x_1372_, lean_object* v_x_1373_, lean_object* v_h__1_1374_, lean_object* v_h__2_1375_){
_start:
{
lean_object* v_zero_1376_; uint8_t v_isZero_1377_; 
v_zero_1376_ = lean_unsigned_to_nat(0u);
v_isZero_1377_ = lean_nat_dec_eq(v_x_1372_, v_zero_1376_);
if (v_isZero_1377_ == 1)
{
lean_object* v___x_1378_; 
lean_dec(v_h__2_1375_);
v___x_1378_ = lean_apply_1(v_h__1_1374_, v_x_1373_);
return v___x_1378_;
}
else
{
lean_object* v_one_1379_; lean_object* v_n_1380_; lean_object* v___x_1381_; 
lean_dec(v_h__1_1374_);
v_one_1379_ = lean_unsigned_to_nat(1u);
v_n_1380_ = lean_nat_sub(v_x_1372_, v_one_1379_);
v___x_1381_ = lean_apply_2(v_h__2_1375_, v_n_1380_, v_x_1373_);
return v___x_1381_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter___boxed(lean_object* v_motive_1382_, lean_object* v_x_1383_, lean_object* v_x_1384_, lean_object* v_h__1_1385_, lean_object* v_h__2_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter(v_motive_1382_, v_x_1383_, v_x_1384_, v_h__1_1385_, v_h__2_1386_);
lean_dec(v_x_1383_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Array_map__unattach_match__1_splitter___redArg(lean_object* v_x_1388_, lean_object* v_h__1_1389_){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = lean_apply_2(v_h__1_1389_, v_x_1388_, lean_box(0));
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Array_map__unattach_match__1_splitter(lean_object* v_00_u03b1_1391_, lean_object* v_P_1392_, lean_object* v_motive_1393_, lean_object* v_x_1394_, lean_object* v_h__1_1395_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = lean_apply_2(v_h__1_1395_, v_x_1394_, lean_box(0));
return v___x_1396_;
}
}
lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___redArg(lean_object* v_e_1397_, lean_object* v_maxFVars_1398_, lean_object* v_k_1399_, uint8_t v_cleanupAnnotations_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v___f_1406_; uint8_t v___x_1407_; uint8_t v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___f_1406_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1406_, 0, v_k_1399_);
v___x_1407_ = 1;
v___x_1408_ = 0;
v___x_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1409_, 0, v_maxFVars_1398_);
v___x_1410_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1397_, v___x_1407_, v___x_1408_, v___x_1407_, v___x_1408_, v___x_1409_, v___f_1406_, v_cleanupAnnotations_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
lean_dec_ref_known(v___x_1409_, 1);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1418_; 
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1413_ = v___x_1410_;
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1410_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1411_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
else
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
v_a_1419_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1421_ = v___x_1410_;
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1410_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1424_; 
if (v_isShared_1422_ == 0)
{
v___x_1424_ = v___x_1421_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_a_1419_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1397_ = stack[0].m_obj;
lean_object* v_maxFVars_1398_ = stack[1].m_obj;
lean_object* v_k_1399_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_1400_ = stack[3].m_num;
lean_object* v___y_1401_ = stack[4].m_obj;
lean_object* v___y_1402_ = stack[5].m_obj;
lean_object* v___y_1403_ = stack[6].m_obj;
lean_object* v___y_1404_ = stack[7].m_obj;
lean_object* v_res_1427_;
v_res_1427_ = l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___redArg(v_e_1397_, v_maxFVars_1398_, v_k_1399_, v_cleanupAnnotations_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
stack->m_obj
 = v_res_1427_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___redArg___boxed(lean_object* v_e_1428_, lean_object* v_maxFVars_1429_, lean_object* v_k_1430_, lean_object* v_cleanupAnnotations_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1437_; lean_object* v_res_1438_; 
v_cleanupAnnotations_boxed_1437_ = lean_unbox(v_cleanupAnnotations_1431_);
v_res_1438_ = l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___redArg(v_e_1428_, v_maxFVars_1429_, v_k_1430_, v_cleanupAnnotations_boxed_1437_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
return v_res_1438_;
}
}
lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0(lean_object* v_00_u03b1_1439_, lean_object* v_e_1440_, lean_object* v_maxFVars_1441_, lean_object* v_k_1442_, uint8_t v_cleanupAnnotations_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___redArg(v_e_1440_, v_maxFVars_1441_, v_k_1442_, v_cleanupAnnotations_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
return v___x_1449_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1440_ = stack[1].m_obj;
lean_object* v_maxFVars_1441_ = stack[2].m_obj;
lean_object* v_k_1442_ = stack[3].m_obj;
uint8_t v_cleanupAnnotations_1443_ = stack[4].m_num;
lean_object* v___y_1444_ = stack[5].m_obj;
lean_object* v___y_1445_ = stack[6].m_obj;
lean_object* v___y_1446_ = stack[7].m_obj;
lean_object* v___y_1447_ = stack[8].m_obj;
lean_object* v_res_1450_;
v_res_1450_ = l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0(lean_box(0), v_e_1440_, v_maxFVars_1441_, v_k_1442_, v_cleanupAnnotations_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
stack->m_obj
 = v_res_1450_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___boxed(lean_object* v_00_u03b1_1451_, lean_object* v_e_1452_, lean_object* v_maxFVars_1453_, lean_object* v_k_1454_, lean_object* v_cleanupAnnotations_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1461_; lean_object* v_res_1462_; 
v_cleanupAnnotations_boxed_1461_ = lean_unbox(v_cleanupAnnotations_1455_);
v_res_1462_ = l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0(v_00_u03b1_1451_, v_e_1452_, v_maxFVars_1453_, v_k_1454_, v_cleanupAnnotations_boxed_1461_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
return v_res_1462_;
}
}
lean_object* l_Lean_Elab_TerminationMeasure_delab___lam__0(lean_object* v_measure_1465_, lean_object* v_extraParams_1466_, lean_object* v___ys_1467_, lean_object* v_e_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1474_ = lean_box(1);
v___x_1475_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_delab___lam__0___closed__0));
v___x_1476_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___boxed), 10, 3);
lean_closure_set(v___x_1476_, 0, v_measure_1465_);
lean_closure_set(v___x_1476_, 1, v_extraParams_1466_);
lean_closure_set(v___x_1476_, 2, v___x_1475_);
v___x_1477_ = l_Lean_PrettyPrinter_delabCore___redArg(v_e_1468_, v___x_1474_, v___x_1476_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1486_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1480_ = v___x_1477_;
v_isShared_1481_ = v_isSharedCheck_1486_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1477_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1486_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v_fst_1482_; lean_object* v___x_1484_; 
v_fst_1482_ = lean_ctor_get(v_a_1478_, 0);
lean_inc(v_fst_1482_);
lean_dec(v_a_1478_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 0, v_fst_1482_);
v___x_1484_ = v___x_1480_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_fst_1482_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
v_a_1487_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1477_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1477_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_TerminationMeasure_delab___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_measure_1465_ = stack[0].m_obj;
lean_object* v_extraParams_1466_ = stack[1].m_obj;
lean_object* v___ys_1467_ = stack[2].m_obj;
lean_object* v_e_1468_ = stack[3].m_obj;
lean_object* v___y_1469_ = stack[4].m_obj;
lean_object* v___y_1470_ = stack[5].m_obj;
lean_object* v___y_1471_ = stack[6].m_obj;
lean_object* v___y_1472_ = stack[7].m_obj;
lean_object* v_res_1495_;
v_res_1495_ = l_Lean_Elab_TerminationMeasure_delab___lam__0(v_measure_1465_, v_extraParams_1466_, v___ys_1467_, v_e_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
stack->m_obj
 = v_res_1495_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_delab___lam__0___boxed(lean_object* v_measure_1496_, lean_object* v_extraParams_1497_, lean_object* v___ys_1498_, lean_object* v_e_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_Lean_Elab_TerminationMeasure_delab___lam__0(v_measure_1496_, v_extraParams_1497_, v___ys_1498_, v_e_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec_ref(v___ys_1498_);
return v_res_1505_;
}
}
lean_object* l_Lean_Elab_TerminationMeasure_delab(lean_object* v_arity_1506_, lean_object* v_extraParams_1507_, lean_object* v_measure_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_){
_start:
{
lean_object* v_fn_1514_; lean_object* v___f_1515_; lean_object* v___x_1516_; uint8_t v___x_1517_; lean_object* v___x_1518_; 
v_fn_1514_ = lean_ctor_get(v_measure_1508_, 1);
lean_inc_ref(v_fn_1514_);
lean_inc(v_extraParams_1507_);
v___f_1515_ = lean_alloc_closure((void*)(l_Lean_Elab_TerminationMeasure_delab___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1515_, 0, v_measure_1508_);
lean_closure_set(v___f_1515_, 1, v_extraParams_1507_);
v___x_1516_ = lean_nat_sub(v_arity_1506_, v_extraParams_1507_);
lean_dec(v_extraParams_1507_);
v___x_1517_ = 0;
v___x_1518_ = l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___redArg(v_fn_1514_, v___x_1516_, v___f_1515_, v___x_1517_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_);
return v___x_1518_;
}
}
LEAN_EXPORT void l_Lean_Elab_TerminationMeasure_delab_0interp(lean_interpreter_value* stack)
{
lean_object* v_arity_1506_ = stack[0].m_obj;
lean_object* v_extraParams_1507_ = stack[1].m_obj;
lean_object* v_measure_1508_ = stack[2].m_obj;
lean_object* v_a_1509_ = stack[3].m_obj;
lean_object* v_a_1510_ = stack[4].m_obj;
lean_object* v_a_1511_ = stack[5].m_obj;
lean_object* v_a_1512_ = stack[6].m_obj;
lean_object* v_res_1519_;
v_res_1519_ = l_Lean_Elab_TerminationMeasure_delab(v_arity_1506_, v_extraParams_1507_, v_measure_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_);
stack->m_obj
 = v_res_1519_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_delab___boxed(lean_object* v_arity_1520_, lean_object* v_extraParams_1521_, lean_object* v_measure_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Lean_Elab_TerminationMeasure_delab(v_arity_1520_, v_extraParams_1521_, v_measure_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
lean_dec(v_a_1526_);
lean_dec_ref(v_a_1525_);
lean_dec(v_a_1524_);
lean_dec_ref(v_a_1523_);
lean_dec(v_arity_1520_);
return v_res_1528_;
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
