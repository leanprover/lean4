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
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_pop(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
v___x_160_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6(lean_object* v_msg_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v___x_169_; lean_object* v___x_3762__overap_170_; lean_object* v___x_171_; 
v___x_169_ = lean_obj_once(&l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6___closed__0, &l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6___closed__0_once, _init_l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6___closed__0);
v___x_3762__overap_170_ = lean_panic_fn_borrowed(v___x_169_, v_msg_161_);
lean_inc(v___y_167_);
lean_inc_ref(v___y_166_);
lean_inc(v___y_165_);
lean_inc_ref(v___y_164_);
lean_inc(v___y_163_);
lean_inc_ref(v___y_162_);
v___x_171_ = lean_apply_7(v___x_3762__overap_170_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, lean_box(0));
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
uint8_t v___x_6105__boxed_212_; lean_object* v_res_213_; 
v___x_6105__boxed_212_ = lean_unbox(v___x_202_);
v_res_213_ = l_Lean_Elab_TerminationMeasure_elab___lam__0(v_ys_199_, v_xs_200_, v_a_201_, v___x_6105__boxed_212_, v_zs_203_, v_x_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_);
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
lean_object* v_options_270_; lean_object* v___x_271_; uint8_t v___x_272_; uint8_t v___x_273_; 
v_options_270_ = lean_ctor_get(v___y_268_, 2);
v___x_271_ = l_Lean_Elab_pp_macroStack;
v___x_272_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__10(v_options_270_, v___x_271_);
v___x_273_ = lean_bool_not(v___x_272_);
if (v___x_273_ == 0)
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
else
{
lean_object* v___x_293_; 
lean_dec(v_macroStack_267_);
v___x_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_293_, 0, v_msgData_266_);
return v___x_293_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg___boxed(lean_object* v_msgData_294_, lean_object* v_macroStack_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg(v_msgData_294_, v_macroStack_295_, v___y_296_);
lean_dec_ref(v___y_296_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__8(lean_object* v_msgData_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v___x_305_; lean_object* v_env_306_; lean_object* v___x_307_; lean_object* v_mctx_308_; lean_object* v_lctx_309_; lean_object* v_options_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_305_ = lean_st_ref_get(v___y_303_);
v_env_306_ = lean_ctor_get(v___x_305_, 0);
lean_inc_ref(v_env_306_);
lean_dec(v___x_305_);
v___x_307_ = lean_st_ref_get(v___y_301_);
v_mctx_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc_ref(v_mctx_308_);
lean_dec(v___x_307_);
v_lctx_309_ = lean_ctor_get(v___y_300_, 2);
v_options_310_ = lean_ctor_get(v___y_302_, 2);
lean_inc_ref(v_options_310_);
lean_inc_ref(v_lctx_309_);
v___x_311_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_311_, 0, v_env_306_);
lean_ctor_set(v___x_311_, 1, v_mctx_308_);
lean_ctor_set(v___x_311_, 2, v_lctx_309_);
lean_ctor_set(v___x_311_, 3, v_options_310_);
v___x_312_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
lean_ctor_set(v___x_312_, 1, v_msgData_299_);
v___x_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__8___boxed(lean_object* v_msgData_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__8(v_msgData_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5___redArg(lean_object* v_msg_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
lean_object* v_ref_329_; lean_object* v___x_330_; lean_object* v_a_331_; lean_object* v_macroStack_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_343_; 
v_ref_329_ = lean_ctor_get(v___y_326_, 5);
v___x_330_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__8(v_msg_321_, v___y_324_, v___y_325_, v___y_326_, v___y_327_);
v_a_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_a_331_);
lean_dec_ref(v___x_330_);
v_macroStack_332_ = lean_ctor_get(v___y_322_, 1);
v___x_333_ = l_Lean_Elab_getBetterRef(v_ref_329_, v_macroStack_332_);
lean_inc(v_macroStack_332_);
v___x_334_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg(v_a_331_, v_macroStack_332_, v___y_326_);
v_a_335_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_343_ == 0)
{
v___x_337_ = v___x_334_;
v_isShared_338_ = v_isSharedCheck_343_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_dec(v___x_334_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_343_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_339_; lean_object* v___x_341_; 
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_333_);
lean_ctor_set(v___x_339_, 1, v_a_335_);
if (v_isShared_338_ == 0)
{
lean_ctor_set_tag(v___x_337_, 1);
lean_ctor_set(v___x_337_, 0, v___x_339_);
v___x_341_ = v___x_337_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_339_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5___redArg___boxed(lean_object* v_msg_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5___redArg(v_msg_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
lean_dec(v___y_348_);
lean_dec_ref(v___y_347_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___redArg(lean_object* v_ref_353_, lean_object* v_msg_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v_fileName_362_; lean_object* v_fileMap_363_; lean_object* v_options_364_; lean_object* v_currRecDepth_365_; lean_object* v_maxRecDepth_366_; lean_object* v_ref_367_; lean_object* v_currNamespace_368_; lean_object* v_openDecls_369_; lean_object* v_initHeartbeats_370_; lean_object* v_maxHeartbeats_371_; lean_object* v_quotContext_372_; lean_object* v_currMacroScope_373_; uint8_t v_diag_374_; lean_object* v_cancelTk_x3f_375_; uint8_t v_suppressElabErrors_376_; lean_object* v_inheritedTraceOptions_377_; lean_object* v_ref_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v_fileName_362_ = lean_ctor_get(v___y_359_, 0);
v_fileMap_363_ = lean_ctor_get(v___y_359_, 1);
v_options_364_ = lean_ctor_get(v___y_359_, 2);
v_currRecDepth_365_ = lean_ctor_get(v___y_359_, 3);
v_maxRecDepth_366_ = lean_ctor_get(v___y_359_, 4);
v_ref_367_ = lean_ctor_get(v___y_359_, 5);
v_currNamespace_368_ = lean_ctor_get(v___y_359_, 6);
v_openDecls_369_ = lean_ctor_get(v___y_359_, 7);
v_initHeartbeats_370_ = lean_ctor_get(v___y_359_, 8);
v_maxHeartbeats_371_ = lean_ctor_get(v___y_359_, 9);
v_quotContext_372_ = lean_ctor_get(v___y_359_, 10);
v_currMacroScope_373_ = lean_ctor_get(v___y_359_, 11);
v_diag_374_ = lean_ctor_get_uint8(v___y_359_, sizeof(void*)*14);
v_cancelTk_x3f_375_ = lean_ctor_get(v___y_359_, 12);
v_suppressElabErrors_376_ = lean_ctor_get_uint8(v___y_359_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_377_ = lean_ctor_get(v___y_359_, 13);
v_ref_378_ = l_Lean_replaceRef(v_ref_353_, v_ref_367_);
lean_inc_ref(v_inheritedTraceOptions_377_);
lean_inc(v_cancelTk_x3f_375_);
lean_inc(v_currMacroScope_373_);
lean_inc(v_quotContext_372_);
lean_inc(v_maxHeartbeats_371_);
lean_inc(v_initHeartbeats_370_);
lean_inc(v_openDecls_369_);
lean_inc(v_currNamespace_368_);
lean_inc(v_maxRecDepth_366_);
lean_inc(v_currRecDepth_365_);
lean_inc_ref(v_options_364_);
lean_inc_ref(v_fileMap_363_);
lean_inc_ref(v_fileName_362_);
v___x_379_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_379_, 0, v_fileName_362_);
lean_ctor_set(v___x_379_, 1, v_fileMap_363_);
lean_ctor_set(v___x_379_, 2, v_options_364_);
lean_ctor_set(v___x_379_, 3, v_currRecDepth_365_);
lean_ctor_set(v___x_379_, 4, v_maxRecDepth_366_);
lean_ctor_set(v___x_379_, 5, v_ref_378_);
lean_ctor_set(v___x_379_, 6, v_currNamespace_368_);
lean_ctor_set(v___x_379_, 7, v_openDecls_369_);
lean_ctor_set(v___x_379_, 8, v_initHeartbeats_370_);
lean_ctor_set(v___x_379_, 9, v_maxHeartbeats_371_);
lean_ctor_set(v___x_379_, 10, v_quotContext_372_);
lean_ctor_set(v___x_379_, 11, v_currMacroScope_373_);
lean_ctor_set(v___x_379_, 12, v_cancelTk_x3f_375_);
lean_ctor_set(v___x_379_, 13, v_inheritedTraceOptions_377_);
lean_ctor_set_uint8(v___x_379_, sizeof(void*)*14, v_diag_374_);
lean_ctor_set_uint8(v___x_379_, sizeof(void*)*14 + 1, v_suppressElabErrors_376_);
v___x_380_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5___redArg(v_msg_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___x_379_, v___y_360_);
lean_dec_ref_known(v___x_379_, 14);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___redArg___boxed(lean_object* v_ref_381_, lean_object* v_msg_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___redArg(v_ref_381_, v_msg_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v_ref_381_);
return v_res_390_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2_spec__2(lean_object* v_a_391_, lean_object* v_as_392_, size_t v_i_393_, size_t v_stop_394_){
_start:
{
uint8_t v___x_395_; 
v___x_395_ = lean_usize_dec_eq(v_i_393_, v_stop_394_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; uint8_t v___x_397_; 
v___x_396_ = lean_array_uget_borrowed(v_as_392_, v_i_393_);
v___x_397_ = lean_expr_eqv(v_a_391_, v___x_396_);
if (v___x_397_ == 0)
{
size_t v___x_398_; size_t v___x_399_; 
v___x_398_ = ((size_t)1ULL);
v___x_399_ = lean_usize_add(v_i_393_, v___x_398_);
v_i_393_ = v___x_399_;
goto _start;
}
else
{
return v___x_397_;
}
}
else
{
uint8_t v___x_401_; 
v___x_401_ = 0;
return v___x_401_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2_spec__2___boxed(lean_object* v_a_402_, lean_object* v_as_403_, lean_object* v_i_404_, lean_object* v_stop_405_){
_start:
{
size_t v_i_boxed_406_; size_t v_stop_boxed_407_; uint8_t v_res_408_; lean_object* v_r_409_; 
v_i_boxed_406_ = lean_unbox_usize(v_i_404_);
lean_dec(v_i_404_);
v_stop_boxed_407_ = lean_unbox_usize(v_stop_405_);
lean_dec(v_stop_405_);
v_res_408_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2_spec__2(v_a_402_, v_as_403_, v_i_boxed_406_, v_stop_boxed_407_);
lean_dec_ref(v_as_403_);
lean_dec_ref(v_a_402_);
v_r_409_ = lean_box(v_res_408_);
return v_r_409_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2(lean_object* v_as_410_, lean_object* v_a_411_){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_412_ = lean_unsigned_to_nat(0u);
v___x_413_ = lean_array_get_size(v_as_410_);
v___x_414_ = lean_nat_dec_lt(v___x_412_, v___x_413_);
if (v___x_414_ == 0)
{
return v___x_414_;
}
else
{
if (v___x_414_ == 0)
{
return v___x_414_;
}
else
{
size_t v___x_415_; size_t v___x_416_; uint8_t v___x_417_; 
v___x_415_ = ((size_t)0ULL);
v___x_416_ = lean_usize_of_nat(v___x_413_);
v___x_417_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2_spec__2(v_a_411_, v_as_410_, v___x_415_, v___x_416_);
return v___x_417_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2___boxed(lean_object* v_as_418_, lean_object* v_a_419_){
_start:
{
uint8_t v_res_420_; lean_object* v_r_421_; 
v_res_420_ = l_Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2(v_as_418_, v_a_419_);
lean_dec_ref(v_a_419_);
lean_dec_ref(v_as_418_);
v_r_421_ = lean_box(v_res_420_);
return v_r_421_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3___closed__1(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3___closed__0));
v___x_424_ = l_Lean_stringToMessageData(v___x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3(lean_object* v_a_425_, lean_object* v_a_426_){
_start:
{
if (lean_obj_tag(v_a_425_) == 0)
{
lean_object* v___x_427_; 
v___x_427_ = l_List_reverse___redArg(v_a_426_);
return v___x_427_;
}
else
{
lean_object* v_head_428_; lean_object* v_tail_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_441_; 
v_head_428_ = lean_ctor_get(v_a_425_, 0);
v_tail_429_ = lean_ctor_get(v_a_425_, 1);
v_isSharedCheck_441_ = !lean_is_exclusive(v_a_425_);
if (v_isSharedCheck_441_ == 0)
{
v___x_431_ = v_a_425_;
v_isShared_432_ = v_isSharedCheck_441_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_tail_429_);
lean_inc(v_head_428_);
lean_dec(v_a_425_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_441_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_438_; 
v___x_433_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3___closed__1, &l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3___closed__1);
v___x_434_ = l_Lean_MessageData_ofExpr(v_head_428_);
v___x_435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_435_, 0, v___x_433_);
lean_ctor_set(v___x_435_, 1, v___x_434_);
v___x_436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
lean_ctor_set(v___x_436_, 1, v___x_433_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 1, v_a_426_);
lean_ctor_set(v___x_431_, 0, v___x_436_);
v___x_438_ = v___x_431_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_436_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v_a_426_);
v___x_438_ = v_reuseFailAlloc_440_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
v_a_425_ = v_tail_429_;
v_a_426_ = v___x_438_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__3(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_445_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__2));
v___x_446_ = lean_unsigned_to_nat(14u);
v___x_447_ = lean_unsigned_to_nat(22u);
v___x_448_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__1));
v___x_449_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__0));
v___x_450_ = l_mkPanicMessageWithDecl(v___x_449_, v___x_448_, v___x_447_, v___x_446_, v___x_445_);
return v___x_450_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__5(void){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__4));
v___x_453_ = l_Lean_stringToMessageData(v___x_452_);
return v___x_453_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__7(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__6));
v___x_456_ = l_Lean_stringToMessageData(v___x_455_);
return v___x_456_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__9(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__8));
v___x_459_ = l_Lean_stringToMessageData(v___x_458_);
return v___x_459_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__11(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__10));
v___x_462_ = l_Lean_stringToMessageData(v___x_461_);
return v___x_462_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__13(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__12));
v___x_465_ = l_Lean_stringToMessageData(v___x_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__1(lean_object* v_body_466_, lean_object* v_ys_467_, lean_object* v_vars_468_, lean_object* v_extraParams_469_, uint8_t v_structural_470_, lean_object* v_ref_471_, lean_object* v_xs_472_, lean_object* v_type_x27_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_object* v___x_481_; uint8_t v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; uint8_t v___x_486_; lean_object* v___x_487_; 
v___x_481_ = lean_box(0);
v___x_482_ = 1;
v___x_483_ = lean_box(v___x_482_);
v___x_484_ = lean_box(v___x_482_);
v___x_485_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_485_, 0, v_body_466_);
lean_closure_set(v___x_485_, 1, v___x_481_);
lean_closure_set(v___x_485_, 2, v___x_483_);
lean_closure_set(v___x_485_, 3, v___x_484_);
lean_closure_set(v___x_485_, 4, v___x_481_);
v___x_486_ = 1;
v___x_487_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_485_, v___x_486_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_546_; 
v_a_488_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_546_ == 0)
{
v___x_490_ = v___x_487_;
v_isShared_491_ = v_isSharedCheck_546_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_487_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_546_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_492_; lean_object* v___f_493_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___y_501_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; 
v___x_492_ = lean_box(v___x_482_);
lean_inc(v_a_488_);
lean_inc_ref(v_xs_472_);
lean_inc_ref(v_ys_467_);
v___f_493_ = lean_alloc_closure((void*)(l_Lean_Elab_TerminationMeasure_elab___lam__0___boxed), 13, 4);
lean_closure_set(v___f_493_, 0, v_ys_467_);
lean_closure_set(v___f_493_, 1, v_xs_472_);
lean_closure_set(v___f_493_, 2, v_a_488_);
lean_closure_set(v___f_493_, 3, v___x_492_);
if (v_structural_470_ == 0)
{
lean_dec(v_a_488_);
lean_dec_ref(v_xs_472_);
lean_dec_ref(v_ys_467_);
v___y_510_ = v___y_474_;
v___y_511_ = v___y_475_;
v___y_512_ = v___y_476_;
v___y_513_ = v___y_477_;
v___y_514_ = v___y_478_;
v___y_515_ = v___y_479_;
goto v___jp_509_;
}
else
{
lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_519_ = l_Array_append___redArg(v_ys_467_, v_xs_472_);
lean_dec_ref(v_xs_472_);
v___x_520_ = l_Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2(v___x_519_, v_a_488_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_545_; 
lean_dec_ref(v___f_493_);
lean_del_object(v___x_490_);
lean_dec(v_type_x27_473_);
v___x_521_ = lean_array_to_list(v___x_519_);
v___x_522_ = lean_box(0);
v___x_523_ = l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3(v___x_521_, v___x_522_);
v___x_524_ = l_Lean_MessageData_andList(v___x_523_);
v___x_525_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__5, &l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__5_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__5);
v___x_526_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__7, &l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__7_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__7);
v___x_527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
lean_ctor_set(v___x_527_, 1, v___x_524_);
v___x_528_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__9, &l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__9_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__9);
v___x_529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_527_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
v___x_530_ = l_Lean_indentExpr(v_a_488_);
v___x_531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_529_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__11, &l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__11_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__11);
v___x_533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_531_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_525_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__13, &l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__13_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__13);
v___x_536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_534_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___redArg(v_ref_471_, v___x_536_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
v_a_538_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_545_ == 0)
{
v___x_540_ = v___x_537_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___x_537_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_538_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
else
{
lean_dec_ref(v___x_519_);
lean_dec(v_a_488_);
v___y_510_ = v___y_474_;
v___y_511_ = v___y_475_;
v___y_512_ = v___y_476_;
v___y_513_ = v___y_477_;
v___y_514_ = v___y_478_;
v___y_515_ = v___y_479_;
goto v___jp_509_;
}
}
v___jp_494_:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_502_ = lean_array_get_size(v_vars_468_);
v___x_503_ = lean_nat_sub(v_extraParams_469_, v___x_502_);
if (v_isShared_491_ == 0)
{
lean_ctor_set_tag(v___x_490_, 1);
lean_ctor_set(v___x_490_, 0, v___x_503_);
v___x_505_ = v___x_490_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_503_);
v___x_505_ = v_reuseFailAlloc_508_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
uint8_t v___x_506_; lean_object* v___x_507_; 
v___x_506_ = 0;
v___x_507_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___redArg(v___y_501_, v___x_505_, v___f_493_, v___x_506_, v___x_506_, v___y_496_, v___y_500_, v___y_499_, v___y_498_, v___y_495_, v___y_497_);
return v___x_507_;
}
}
v___jp_509_:
{
if (lean_obj_tag(v_type_x27_473_) == 0)
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__3, &l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__3_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__3);
v___x_517_ = l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__1(v___x_516_);
v___y_495_ = v___y_514_;
v___y_496_ = v___y_510_;
v___y_497_ = v___y_515_;
v___y_498_ = v___y_513_;
v___y_499_ = v___y_512_;
v___y_500_ = v___y_511_;
v___y_501_ = v___x_517_;
goto v___jp_494_;
}
else
{
lean_object* v_val_518_; 
v_val_518_ = lean_ctor_get(v_type_x27_473_, 0);
lean_inc(v_val_518_);
lean_dec_ref_known(v_type_x27_473_, 1);
v___y_495_ = v___y_514_;
v___y_496_ = v___y_510_;
v___y_497_ = v___y_515_;
v___y_498_ = v___y_513_;
v___y_499_ = v___y_512_;
v___y_500_ = v___y_511_;
v___y_501_ = v_val_518_;
goto v___jp_494_;
}
}
}
}
else
{
lean_dec(v_type_x27_473_);
lean_dec_ref(v_xs_472_);
lean_dec_ref(v_ys_467_);
return v___x_487_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__1___boxed(lean_object* v_body_547_, lean_object* v_ys_548_, lean_object* v_vars_549_, lean_object* v_extraParams_550_, lean_object* v_structural_551_, lean_object* v_ref_552_, lean_object* v_xs_553_, lean_object* v_type_x27_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
uint8_t v_structural_boxed_562_; lean_object* v_res_563_; 
v_structural_boxed_562_ = lean_unbox(v_structural_551_);
v_res_563_ = l_Lean_Elab_TerminationMeasure_elab___lam__1(v_body_547_, v_ys_548_, v_vars_549_, v_extraParams_550_, v_structural_boxed_562_, v_ref_552_, v_xs_553_, v_type_x27_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v_ref_552_);
lean_dec(v_extraParams_550_);
lean_dec_ref(v_vars_549_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__2(lean_object* v_hint_564_, lean_object* v_extraParams_565_, lean_object* v_ys_566_, lean_object* v_type_x27_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
lean_object* v_ref_575_; uint8_t v_structural_576_; lean_object* v_vars_577_; lean_object* v_body_578_; lean_object* v___x_579_; lean_object* v___f_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v_ref_575_ = lean_ctor_get(v_hint_564_, 0);
lean_inc(v_ref_575_);
v_structural_576_ = lean_ctor_get_uint8(v_hint_564_, sizeof(void*)*3);
v_vars_577_ = lean_ctor_get(v_hint_564_, 1);
lean_inc_ref_n(v_vars_577_, 2);
v_body_578_ = lean_ctor_get(v_hint_564_, 2);
lean_inc(v_body_578_);
lean_dec_ref(v_hint_564_);
v___x_579_ = lean_box(v_structural_576_);
v___f_580_ = lean_alloc_closure((void*)(l_Lean_Elab_TerminationMeasure_elab___lam__1___boxed), 15, 6);
lean_closure_set(v___f_580_, 0, v_body_578_);
lean_closure_set(v___f_580_, 1, v_ys_566_);
lean_closure_set(v___f_580_, 2, v_vars_577_);
lean_closure_set(v___f_580_, 3, v_extraParams_565_);
lean_closure_set(v___f_580_, 4, v___x_579_);
lean_closure_set(v___f_580_, 5, v_ref_575_);
v___x_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_581_, 0, v_type_x27_567_);
v___x_582_ = l_Lean_Elab_Term_elabFunBinders___redArg(v_vars_577_, v___x_581_, v___f_580_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
lean_dec_ref(v_vars_577_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__2___boxed(lean_object* v_hint_583_, lean_object* v_extraParams_584_, lean_object* v_ys_585_, lean_object* v_type_x27_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lean_Elab_TerminationMeasure_elab___lam__2(v_hint_583_, v_extraParams_584_, v_ys_585_, v_type_x27_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
return v_res_594_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__3(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_598_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__2));
v___x_599_ = lean_unsigned_to_nat(2u);
v___x_600_ = lean_unsigned_to_nat(54u);
v___x_601_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__1));
v___x_602_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__0));
v___x_603_ = l_mkPanicMessageWithDecl(v___x_602_, v___x_601_, v___x_600_, v___x_599_, v___x_598_);
return v___x_603_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__5(void){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__4));
v___x_606_ = l_Lean_stringToMessageData(v___x_605_);
return v___x_606_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__7(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__6));
v___x_609_ = l_Lean_stringToMessageData(v___x_608_);
return v___x_609_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__9(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__8));
v___x_612_ = l_Lean_stringToMessageData(v___x_611_);
return v___x_612_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__13(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__12));
v___x_618_ = l_Lean_stringToMessageData(v___x_617_);
return v___x_618_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__16(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__15));
v___x_623_ = l_Lean_MessageData_ofFormat(v___x_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__3(uint8_t v___x_624_, lean_object* v_hint_625_, lean_object* v_arity_626_, lean_object* v_extraParams_627_, lean_object* v_type_628_, lean_object* v___f_629_, lean_object* v_funName_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
if (v___x_624_ == 0)
{
lean_object* v___x_638_; lean_object* v___x_639_; 
lean_dec(v_funName_630_);
lean_dec_ref(v___f_629_);
lean_dec_ref(v_type_628_);
lean_dec(v_extraParams_627_);
v___x_638_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__3, &l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__3_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__3);
v___x_639_ = l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6(v___x_638_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
return v___x_639_;
}
else
{
lean_object* v_ref_640_; uint8_t v_structural_641_; lean_object* v_vars_642_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v_msg_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___x_702_; uint8_t v___x_703_; 
v_ref_640_ = lean_ctor_get(v_hint_625_, 0);
v_structural_641_ = lean_ctor_get_uint8(v_hint_625_, sizeof(void*)*3);
v_vars_642_ = lean_ctor_get(v_hint_625_, 1);
v___x_702_ = lean_array_get_size(v_vars_642_);
v___x_703_ = lean_nat_dec_lt(v_extraParams_627_, v___x_702_);
if (v___x_703_ == 0)
{
lean_dec(v_funName_630_);
v___y_644_ = v___y_631_;
v___y_645_ = v___y_632_;
v___y_646_ = v___y_633_;
v___y_647_ = v___y_634_;
v___y_648_ = v___y_635_;
v___y_649_ = v___y_636_;
goto v___jp_643_;
}
else
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v_msg_714_; lean_object* v___x_715_; lean_object* v_ident_716_; lean_object* v___x_717_; uint8_t v___x_718_; 
lean_dec_ref(v___f_629_);
lean_dec_ref(v_type_628_);
v___x_704_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters(v___x_702_);
v___x_705_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__5, &l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__5_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__5);
v___x_706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_704_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
lean_inc(v_funName_630_);
v___x_707_ = l_Lean_MessageData_ofName(v_funName_630_);
v___x_708_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__7, &l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__7_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__7);
v___x_709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_707_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
v___x_710_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters(v_extraParams_627_);
v___x_711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_709_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
v___x_712_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__9, &l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__9_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__9);
v___x_713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_713_, 0, v___x_711_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
v_msg_714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_714_, 0, v___x_706_);
lean_ctor_set(v_msg_714_, 1, v___x_713_);
v___x_715_ = lean_unsigned_to_nat(0u);
v_ident_716_ = lean_array_fget_borrowed(v_vars_642_, v___x_715_);
v___x_717_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__11));
lean_inc(v_ident_716_);
v___x_718_ = l_Lean_Syntax_isOfKind(v_ident_716_, v___x_717_);
if (v___x_718_ == 0)
{
lean_dec(v_funName_630_);
v_msg_686_ = v_msg_714_;
v___y_687_ = v___y_631_;
v___y_688_ = v___y_632_;
v___y_689_ = v___y_633_;
v___y_690_ = v___y_634_;
v___y_691_ = v___y_635_;
v___y_692_ = v___y_636_;
goto v___jp_685_;
}
else
{
lean_object* v___x_719_; uint8_t v___x_720_; 
v___x_719_ = l_Lean_TSyntax_getId(v_ident_716_);
v___x_720_ = l_Lean_Name_isSuffixOf(v___x_719_, v_funName_630_);
lean_dec(v_funName_630_);
lean_dec(v___x_719_);
if (v___x_720_ == 0)
{
v_msg_686_ = v_msg_714_;
v___y_687_ = v___y_631_;
v___y_688_ = v___y_632_;
v___y_689_ = v___y_633_;
v___y_690_ = v___y_634_;
v___y_691_ = v___y_635_;
v___y_692_ = v___y_636_;
goto v___jp_685_;
}
else
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v_msg_724_; 
v___x_721_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__13, &l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__13_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__13);
v___x_722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_722_, 0, v_msg_714_);
lean_ctor_set(v___x_722_, 1, v___x_721_);
v___x_723_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__16, &l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__16_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__16);
v_msg_724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_724_, 0, v___x_722_);
lean_ctor_set(v_msg_724_, 1, v___x_723_);
v_msg_686_ = v_msg_724_;
v___y_687_ = v___y_631_;
v___y_688_ = v___y_632_;
v___y_689_ = v___y_633_;
v___y_690_ = v___y_634_;
v___y_691_ = v___y_635_;
v___y_692_ = v___y_636_;
goto v___jp_685_;
}
}
}
v___jp_643_:
{
lean_object* v___x_650_; lean_object* v___x_651_; uint8_t v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_650_ = lean_nat_sub(v_arity_626_, v_extraParams_627_);
lean_dec(v_extraParams_627_);
v___x_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
v___x_652_ = 0;
v___x_653_ = lean_box(v___x_624_);
v___x_654_ = lean_box(v___x_652_);
v___x_655_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___boxed), 13, 6);
lean_closure_set(v___x_655_, 0, lean_box(0));
lean_closure_set(v___x_655_, 1, v_type_628_);
lean_closure_set(v___x_655_, 2, v___x_651_);
lean_closure_set(v___x_655_, 3, v___f_629_);
lean_closure_set(v___x_655_, 4, v___x_653_);
lean_closure_set(v___x_655_, 5, v___x_654_);
v___x_656_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_655_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_a_657_; uint8_t v___x_658_; lean_object* v___x_659_; 
v_a_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc_n(v_a_657_, 2);
lean_dec_ref_known(v___x_656_, 1);
v___x_658_ = 0;
v___x_659_ = l_Lean_Meta_check(v_a_657_, v___x_658_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_667_; 
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_667_ == 0)
{
lean_object* v_unused_668_; 
v_unused_668_ = lean_ctor_get(v___x_659_, 0);
lean_dec(v_unused_668_);
v___x_661_ = v___x_659_;
v_isShared_662_ = v_isSharedCheck_667_;
goto v_resetjp_660_;
}
else
{
lean_dec(v___x_659_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_667_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_663_; lean_object* v___x_665_; 
lean_inc(v_ref_640_);
v___x_663_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_663_, 0, v_ref_640_);
lean_ctor_set(v___x_663_, 1, v_a_657_);
lean_ctor_set_uint8(v___x_663_, sizeof(void*)*2, v_structural_641_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v___x_663_);
v___x_665_ = v___x_661_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v___x_663_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
else
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_676_; 
lean_dec(v_a_657_);
v_a_669_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_676_ == 0)
{
v___x_671_ = v___x_659_;
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_659_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_674_; 
if (v_isShared_672_ == 0)
{
v___x_674_ = v___x_671_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_a_669_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
else
{
lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_684_; 
v_a_677_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_684_ == 0)
{
v___x_679_ = v___x_656_;
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v___x_656_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_677_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
v___jp_685_:
{
lean_object* v___x_693_; lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_701_; 
v___x_693_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___redArg(v_ref_640_, v_msg_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
v_a_694_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_701_ == 0)
{
v___x_696_ = v___x_693_;
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_693_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_699_; 
if (v_isShared_697_ == 0)
{
v___x_699_ = v___x_696_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_694_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__3___boxed(lean_object* v___x_725_, lean_object* v_hint_726_, lean_object* v_arity_727_, lean_object* v_extraParams_728_, lean_object* v_type_729_, lean_object* v___f_730_, lean_object* v_funName_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
uint8_t v___x_6772__boxed_739_; lean_object* v_res_740_; 
v___x_6772__boxed_739_ = lean_unbox(v___x_725_);
v_res_740_ = l_Lean_Elab_TerminationMeasure_elab___lam__3(v___x_6772__boxed_739_, v_hint_726_, v_arity_727_, v_extraParams_728_, v_type_729_, v___f_730_, v_funName_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
lean_dec(v_arity_727_);
lean_dec_ref(v_hint_726_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab(lean_object* v_funName_741_, lean_object* v_type_742_, lean_object* v_arity_743_, lean_object* v_extraParams_744_, lean_object* v_hint_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_){
_start:
{
lean_object* v___f_753_; uint8_t v___x_754_; lean_object* v___x_755_; lean_object* v___y_756_; lean_object* v___x_757_; 
lean_inc(v_extraParams_744_);
lean_inc_ref(v_hint_745_);
v___f_753_ = lean_alloc_closure((void*)(l_Lean_Elab_TerminationMeasure_elab___lam__2___boxed), 11, 2);
lean_closure_set(v___f_753_, 0, v_hint_745_);
lean_closure_set(v___f_753_, 1, v_extraParams_744_);
v___x_754_ = lean_nat_dec_le(v_extraParams_744_, v_arity_743_);
v___x_755_ = lean_box(v___x_754_);
lean_inc(v_funName_741_);
v___y_756_ = lean_alloc_closure((void*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___boxed), 14, 7);
lean_closure_set(v___y_756_, 0, v___x_755_);
lean_closure_set(v___y_756_, 1, v_hint_745_);
lean_closure_set(v___y_756_, 2, v_arity_743_);
lean_closure_set(v___y_756_, 3, v_extraParams_744_);
lean_closure_set(v___y_756_, 4, v_type_742_);
lean_closure_set(v___y_756_, 5, v___f_753_);
lean_closure_set(v___y_756_, 6, v_funName_741_);
v___x_757_ = l_Lean_Elab_Term_withDeclName___redArg(v_funName_741_, v___y_756_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_);
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
lean_object* v___f_840_; lean_object* v___x_417__overap_841_; lean_object* v___x_842_; 
v___f_840_ = ((lean_object*)(l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1___closed__0));
v___x_417__overap_841_ = lean_panic_fn_borrowed(v___f_840_, v_msg_834_);
lean_inc(v___y_838_);
lean_inc_ref(v___y_837_);
lean_inc(v___y_836_);
lean_inc_ref(v___y_835_);
v___x_842_ = lean_apply_5(v___x_417__overap_841_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, lean_box(0));
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
uint8_t v___y_1084_; lean_object* v___x_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; uint8_t v___x_1091_; 
v___x_1088_ = lean_array_get_size(v_a_1081_);
v___x_1089_ = lean_unsigned_to_nat(0u);
v___x_1090_ = lean_nat_dec_eq(v___x_1088_, v___x_1089_);
v___x_1091_ = lean_bool_not(v___x_1090_);
if (v___x_1091_ == 0)
{
v___y_1084_ = v___x_1091_;
goto v___jp_1083_;
}
else
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; uint8_t v___x_1097_; 
v___x_1092_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4));
v___x_1093_ = lean_box(0);
v___x_1094_ = lean_unsigned_to_nat(1u);
v___x_1095_ = lean_nat_sub(v___x_1088_, v___x_1094_);
v___x_1096_ = lean_array_get_borrowed(v___x_1093_, v_a_1081_, v___x_1095_);
lean_dec(v___x_1095_);
lean_inc(v___x_1096_);
v___x_1097_ = l_Lean_Syntax_isOfKind(v___x_1096_, v___x_1092_);
v___y_1084_ = v___x_1097_;
goto v___jp_1083_;
}
v___jp_1083_:
{
if (v___y_1084_ == 0)
{
lean_object* v___x_1085_; 
v___x_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1085_, 0, v_a_1081_);
return v___x_1085_;
}
else
{
lean_object* v___x_1086_; 
v___x_1086_ = lean_array_pop(v_a_1081_);
v_a_1081_ = v___x_1086_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___boxed(lean_object* v_a_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg(v_a_1098_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__0(lean_object* v_a_1101_, lean_object* v___x_1102_, size_t v_sz_1103_, size_t v_i_1104_, lean_object* v_bs_1105_){
_start:
{
uint8_t v___x_1106_; 
v___x_1106_ = lean_usize_dec_lt(v_i_1104_, v_sz_1103_);
if (v___x_1106_ == 0)
{
lean_dec(v___x_1102_);
return v_bs_1105_;
}
else
{
lean_object* v_v_1107_; lean_object* v___x_1108_; lean_object* v_bs_x27_1109_; lean_object* v___y_1111_; lean_object* v___x_1116_; uint8_t v___x_1117_; 
v_v_1107_ = lean_array_uget(v_bs_1105_, v_i_1104_);
v___x_1108_ = lean_unsigned_to_nat(0u);
v_bs_x27_1109_ = lean_array_uset(v_bs_1105_, v_i_1104_, v___x_1108_);
v___x_1116_ = l_Lean_TSyntax_getId(v_v_1107_);
v___x_1117_ = l_Lean_Syntax_hasIdent(v___x_1116_, v_a_1101_);
lean_dec(v___x_1116_);
if (v___x_1117_ == 0)
{
lean_dec(v_v_1107_);
lean_inc(v___x_1102_);
v___y_1111_ = v___x_1102_;
goto v___jp_1110_;
}
else
{
v___y_1111_ = v_v_1107_;
goto v___jp_1110_;
}
v___jp_1110_:
{
size_t v___x_1112_; size_t v___x_1113_; lean_object* v___x_1114_; 
v___x_1112_ = ((size_t)1ULL);
v___x_1113_ = lean_usize_add(v_i_1104_, v___x_1112_);
v___x_1114_ = lean_array_uset(v_bs_x27_1109_, v_i_1104_, v___y_1111_);
v_i_1104_ = v___x_1113_;
v_bs_1105_ = v___x_1114_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__0___boxed(lean_object* v_a_1118_, lean_object* v___x_1119_, lean_object* v_sz_1120_, lean_object* v_i_1121_, lean_object* v_bs_1122_){
_start:
{
size_t v_sz_boxed_1123_; size_t v_i_boxed_1124_; lean_object* v_res_1125_; 
v_sz_boxed_1123_ = lean_unbox_usize(v_sz_1120_);
lean_dec(v_sz_1120_);
v_i_boxed_1124_ = lean_unbox_usize(v_i_1121_);
lean_dec(v_i_1121_);
v_res_1125_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__0(v_a_1118_, v___x_1119_, v_sz_boxed_1123_, v_i_boxed_1124_, v_bs_1122_);
lean_dec(v_a_1118_);
return v_res_1125_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7(void){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l_Array_mkArray0(lean_box(0));
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__1___boxed(lean_object* v_a_1141_, lean_object* v_measure_1142_, lean_object* v_n_1143_, lean_object* v_n_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__1(v_a_1141_, v_measure_1142_, v_n_1143_, v_n_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec(v_n_1143_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go(lean_object* v_measure_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_){
_start:
{
lean_object* v_zero_1163_; uint8_t v_isZero_1164_; 
v_zero_1163_ = lean_unsigned_to_nat(0u);
v_isZero_1164_ = lean_nat_dec_eq(v_a_1154_, v_zero_1163_);
if (v_isZero_1164_ == 1)
{
lean_object* v___x_1165_; 
v___x_1165_ = l_Lean_PrettyPrinter_Delaborator_delab(v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; lean_object* v_ref_1167_; lean_object* v___x_1168_; lean_object* v_a_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; size_t v_sz_1174_; size_t v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_a_1166_);
lean_dec_ref_known(v___x_1165_, 1);
v_ref_1167_ = lean_ctor_get(v_a_1160_, 5);
v___x_1168_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0(v_ref_1167_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
lean_inc_n(v_a_1169_, 2);
lean_dec_ref(v___x_1168_);
v___x_1170_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4));
v___x_1171_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__0));
v___x_1172_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1172_, 0, v_a_1169_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
v___x_1173_ = l_Lean_Syntax_node1(v_a_1169_, v___x_1170_, v___x_1172_);
v_sz_1174_ = lean_array_size(v_a_1155_);
v___x_1175_ = ((size_t)0ULL);
v___x_1176_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__0(v_a_1166_, v___x_1173_, v_sz_1174_, v___x_1175_, v_a_1155_);
v___x_1177_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg(v___x_1176_);
if (lean_obj_tag(v___x_1177_) == 0)
{
uint8_t v_structural_1178_; 
v_structural_1178_ = lean_ctor_get_uint8(v_measure_1153_, sizeof(void*)*2);
lean_dec_ref(v_measure_1153_);
if (v_structural_1178_ == 0)
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1217_; 
v_a_1179_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1181_ = v___x_1177_;
v_isShared_1182_ = v_isSharedCheck_1217_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1177_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1217_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1183_; uint8_t v___x_1184_; 
v___x_1183_ = lean_array_get_size(v_a_1179_);
v___x_1184_ = lean_nat_dec_eq(v___x_1183_, v_zero_1163_);
if (v___x_1184_ == 0)
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1199_; 
v___x_1185_ = l_Lean_SourceInfo_fromRef(v_ref_1167_, v___x_1184_);
v___x_1186_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3));
v___x_1187_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__4));
lean_inc_n(v___x_1185_, 5);
v___x_1188_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1185_);
lean_ctor_set(v___x_1188_, 1, v___x_1187_);
v___x_1189_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__6));
v___x_1190_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7, &l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7);
v___x_1191_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1185_);
lean_ctor_set(v___x_1191_, 1, v___x_1189_);
lean_ctor_set(v___x_1191_, 2, v___x_1190_);
v___x_1192_ = l_Array_append___redArg(v___x_1190_, v_a_1179_);
lean_dec(v_a_1179_);
v___x_1193_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1185_);
lean_ctor_set(v___x_1193_, 1, v___x_1189_);
lean_ctor_set(v___x_1193_, 2, v___x_1192_);
v___x_1194_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__8));
v___x_1195_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1185_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
v___x_1196_ = l_Lean_Syntax_node2(v___x_1185_, v___x_1189_, v___x_1193_, v___x_1195_);
v___x_1197_ = l_Lean_Syntax_node4(v___x_1185_, v___x_1186_, v___x_1188_, v___x_1191_, v___x_1196_, v_a_1166_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 0, v___x_1197_);
v___x_1199_ = v___x_1181_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
else
{
lean_object* v___x_1201_; lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1216_; 
lean_del_object(v___x_1181_);
lean_dec(v_a_1179_);
v___x_1201_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0(v_ref_1167_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
v_a_1202_ = lean_ctor_get(v___x_1201_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1204_ = v___x_1201_;
v_isShared_1205_ = v_isSharedCheck_1216_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1201_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1216_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1214_; 
v___x_1206_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3));
v___x_1207_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__4));
lean_inc_n(v_a_1202_, 2);
v___x_1208_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1208_, 0, v_a_1202_);
lean_ctor_set(v___x_1208_, 1, v___x_1207_);
v___x_1209_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__6));
v___x_1210_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7, &l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7);
v___x_1211_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1211_, 0, v_a_1202_);
lean_ctor_set(v___x_1211_, 1, v___x_1209_);
lean_ctor_set(v___x_1211_, 2, v___x_1210_);
lean_inc_ref(v___x_1211_);
v___x_1212_ = l_Lean_Syntax_node4(v_a_1202_, v___x_1206_, v___x_1208_, v___x_1211_, v___x_1211_, v_a_1166_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 0, v___x_1212_);
v___x_1214_ = v___x_1204_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1212_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
}
else
{
lean_object* v_a_1218_; lean_object* v___x_1219_; uint8_t v___x_1220_; 
v_a_1218_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_a_1218_);
lean_dec_ref_known(v___x_1177_, 1);
v___x_1219_ = lean_array_get_size(v_a_1218_);
v___x_1220_ = lean_nat_dec_eq(v___x_1219_, v_zero_1163_);
if (v___x_1220_ == 0)
{
lean_object* v___x_1221_; lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1243_; 
v___x_1221_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0(v_ref_1167_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1224_ = v___x_1221_;
v_isShared_1225_ = v_isSharedCheck_1243_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1221_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1243_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1241_; 
v___x_1226_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3));
v___x_1227_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__4));
lean_inc_n(v_a_1222_, 6);
v___x_1228_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1228_, 0, v_a_1222_);
lean_ctor_set(v___x_1228_, 1, v___x_1227_);
v___x_1229_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__6));
v___x_1230_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__9));
v___x_1231_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1231_, 0, v_a_1222_);
lean_ctor_set(v___x_1231_, 1, v___x_1230_);
v___x_1232_ = l_Lean_Syntax_node1(v_a_1222_, v___x_1229_, v___x_1231_);
v___x_1233_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7, &l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7);
v___x_1234_ = l_Array_append___redArg(v___x_1233_, v_a_1218_);
lean_dec(v_a_1218_);
v___x_1235_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1235_, 0, v_a_1222_);
lean_ctor_set(v___x_1235_, 1, v___x_1229_);
lean_ctor_set(v___x_1235_, 2, v___x_1234_);
v___x_1236_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__8));
v___x_1237_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1237_, 0, v_a_1222_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
v___x_1238_ = l_Lean_Syntax_node2(v_a_1222_, v___x_1229_, v___x_1235_, v___x_1237_);
v___x_1239_ = l_Lean_Syntax_node4(v_a_1222_, v___x_1226_, v___x_1228_, v___x_1232_, v___x_1238_, v_a_1166_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 0, v___x_1239_);
v___x_1241_ = v___x_1224_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1239_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
else
{
lean_object* v___x_1244_; lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1262_; 
lean_dec(v_a_1218_);
v___x_1244_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0(v_ref_1167_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1247_ = v___x_1244_;
v_isShared_1248_ = v_isSharedCheck_1262_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1244_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1262_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1260_; 
v___x_1249_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3));
v___x_1250_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__4));
lean_inc_n(v_a_1245_, 4);
v___x_1251_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1251_, 0, v_a_1245_);
lean_ctor_set(v___x_1251_, 1, v___x_1250_);
v___x_1252_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__6));
v___x_1253_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__9));
v___x_1254_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1254_, 0, v_a_1245_);
lean_ctor_set(v___x_1254_, 1, v___x_1253_);
v___x_1255_ = l_Lean_Syntax_node1(v_a_1245_, v___x_1252_, v___x_1254_);
v___x_1256_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7, &l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7);
v___x_1257_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1257_, 0, v_a_1245_);
lean_ctor_set(v___x_1257_, 1, v___x_1252_);
lean_ctor_set(v___x_1257_, 2, v___x_1256_);
v___x_1258_ = l_Lean_Syntax_node4(v_a_1245_, v___x_1249_, v___x_1251_, v___x_1255_, v___x_1257_, v_a_1166_);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 0, v___x_1258_);
v___x_1260_ = v___x_1247_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1258_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
}
else
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1270_; 
lean_dec(v_a_1166_);
lean_dec_ref(v_measure_1153_);
v_a_1263_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1265_ = v___x_1177_;
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1177_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1268_; 
if (v_isShared_1266_ == 0)
{
v___x_1268_ = v___x_1265_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1263_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
else
{
lean_dec_ref(v_a_1155_);
lean_dec_ref(v_measure_1153_);
return v___x_1165_;
}
}
else
{
lean_object* v___x_1271_; lean_object* v_a_1272_; uint8_t v___x_1273_; 
v___x_1271_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2___redArg(v_a_1156_);
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_a_1272_);
lean_dec_ref(v___x_1271_);
v___x_1273_ = l_Lean_Expr_isLambda(v_a_1272_);
lean_dec(v_a_1272_);
if (v___x_1273_ == 0)
{
v_a_1154_ = v_zero_1163_;
goto _start;
}
else
{
lean_object* v_one_1275_; lean_object* v_n_1276_; lean_object* v___f_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v_one_1275_ = lean_unsigned_to_nat(1u);
v_n_1276_ = lean_nat_sub(v_a_1154_, v_one_1275_);
v___f_1277_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__1___boxed), 11, 3);
lean_closure_set(v___f_1277_, 0, v_a_1155_);
lean_closure_set(v___f_1277_, 1, v_measure_1153_);
lean_closure_set(v___f_1277_, 2, v_n_1276_);
v___x_1278_ = l_Lean_NameSet_empty;
v___x_1279_ = l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg(v___f_1277_, v_isZero_1164_, v___x_1278_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
return v___x_1279_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__1(lean_object* v_a_1280_, lean_object* v_measure_1281_, lean_object* v_n_1282_, lean_object* v_n_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = lean_array_push(v_a_1280_, v_n_1283_);
v___x_1292_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go(v_measure_1281_, v_n_1282_, v___x_1291_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___boxed(lean_object* v_measure_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go(v_measure_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_);
lean_dec(v_a_1301_);
lean_dec_ref(v_a_1300_);
lean_dec(v_a_1299_);
lean_dec_ref(v_a_1298_);
lean_dec(v_a_1297_);
lean_dec_ref(v_a_1296_);
lean_dec(v_a_1294_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1(lean_object* v_inst_1304_, lean_object* v_a_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
lean_object* v___x_1313_; 
v___x_1313_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg(v_a_1305_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___boxed(lean_object* v_inst_1314_, lean_object* v_a_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1(v_inst_1314_, v_a_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter___redArg(lean_object* v_x_1324_, lean_object* v_x_1325_, lean_object* v_h__1_1326_, lean_object* v_h__2_1327_){
_start:
{
lean_object* v_zero_1328_; uint8_t v_isZero_1329_; 
v_zero_1328_ = lean_unsigned_to_nat(0u);
v_isZero_1329_ = lean_nat_dec_eq(v_x_1324_, v_zero_1328_);
if (v_isZero_1329_ == 1)
{
lean_object* v___x_1330_; 
lean_dec(v_h__2_1327_);
v___x_1330_ = lean_apply_1(v_h__1_1326_, v_x_1325_);
return v___x_1330_;
}
else
{
lean_object* v_one_1331_; lean_object* v_n_1332_; lean_object* v___x_1333_; 
lean_dec(v_h__1_1326_);
v_one_1331_ = lean_unsigned_to_nat(1u);
v_n_1332_ = lean_nat_sub(v_x_1324_, v_one_1331_);
v___x_1333_ = lean_apply_2(v_h__2_1327_, v_n_1332_, v_x_1325_);
return v___x_1333_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter___redArg___boxed(lean_object* v_x_1334_, lean_object* v_x_1335_, lean_object* v_h__1_1336_, lean_object* v_h__2_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter___redArg(v_x_1334_, v_x_1335_, v_h__1_1336_, v_h__2_1337_);
lean_dec(v_x_1334_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter(lean_object* v_motive_1339_, lean_object* v_x_1340_, lean_object* v_x_1341_, lean_object* v_h__1_1342_, lean_object* v_h__2_1343_){
_start:
{
lean_object* v_zero_1344_; uint8_t v_isZero_1345_; 
v_zero_1344_ = lean_unsigned_to_nat(0u);
v_isZero_1345_ = lean_nat_dec_eq(v_x_1340_, v_zero_1344_);
if (v_isZero_1345_ == 1)
{
lean_object* v___x_1346_; 
lean_dec(v_h__2_1343_);
v___x_1346_ = lean_apply_1(v_h__1_1342_, v_x_1341_);
return v___x_1346_;
}
else
{
lean_object* v_one_1347_; lean_object* v_n_1348_; lean_object* v___x_1349_; 
lean_dec(v_h__1_1342_);
v_one_1347_ = lean_unsigned_to_nat(1u);
v_n_1348_ = lean_nat_sub(v_x_1340_, v_one_1347_);
v___x_1349_ = lean_apply_2(v_h__2_1343_, v_n_1348_, v_x_1341_);
return v___x_1349_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter___boxed(lean_object* v_motive_1350_, lean_object* v_x_1351_, lean_object* v_x_1352_, lean_object* v_h__1_1353_, lean_object* v_h__2_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter(v_motive_1350_, v_x_1351_, v_x_1352_, v_h__1_1353_, v_h__2_1354_);
lean_dec(v_x_1351_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Array_map__unattach_match__1_splitter___redArg(lean_object* v_x_1356_, lean_object* v_h__1_1357_){
_start:
{
lean_object* v___x_1358_; 
v___x_1358_ = lean_apply_2(v_h__1_1357_, v_x_1356_, lean_box(0));
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Array_map__unattach_match__1_splitter(lean_object* v_00_u03b1_1359_, lean_object* v_P_1360_, lean_object* v_motive_1361_, lean_object* v_x_1362_, lean_object* v_h__1_1363_){
_start:
{
lean_object* v___x_1364_; 
v___x_1364_ = lean_apply_2(v_h__1_1363_, v_x_1362_, lean_box(0));
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___redArg(lean_object* v_e_1365_, lean_object* v_maxFVars_1366_, lean_object* v_k_1367_, uint8_t v_cleanupAnnotations_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v___f_1374_; uint8_t v___x_1375_; uint8_t v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___f_1374_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1374_, 0, v_k_1367_);
v___x_1375_ = 1;
v___x_1376_ = 0;
v___x_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1377_, 0, v_maxFVars_1366_);
v___x_1378_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1365_, v___x_1375_, v___x_1376_, v___x_1375_, v___x_1376_, v___x_1377_, v___f_1374_, v_cleanupAnnotations_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
lean_dec_ref_known(v___x_1377_, 1);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1378_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1378_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_a_1379_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
else
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
v_a_1387_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1378_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1378_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1387_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___redArg___boxed(lean_object* v_e_1395_, lean_object* v_maxFVars_1396_, lean_object* v_k_1397_, lean_object* v_cleanupAnnotations_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1404_; lean_object* v_res_1405_; 
v_cleanupAnnotations_boxed_1404_ = lean_unbox(v_cleanupAnnotations_1398_);
v_res_1405_ = l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___redArg(v_e_1395_, v_maxFVars_1396_, v_k_1397_, v_cleanupAnnotations_boxed_1404_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0(lean_object* v_00_u03b1_1406_, lean_object* v_e_1407_, lean_object* v_maxFVars_1408_, lean_object* v_k_1409_, uint8_t v_cleanupAnnotations_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v___x_1416_; 
v___x_1416_ = l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___redArg(v_e_1407_, v_maxFVars_1408_, v_k_1409_, v_cleanupAnnotations_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___boxed(lean_object* v_00_u03b1_1417_, lean_object* v_e_1418_, lean_object* v_maxFVars_1419_, lean_object* v_k_1420_, lean_object* v_cleanupAnnotations_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1427_; lean_object* v_res_1428_; 
v_cleanupAnnotations_boxed_1427_ = lean_unbox(v_cleanupAnnotations_1421_);
v_res_1428_ = l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0(v_00_u03b1_1417_, v_e_1418_, v_maxFVars_1419_, v_k_1420_, v_cleanupAnnotations_boxed_1427_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_delab___lam__0(lean_object* v_measure_1431_, lean_object* v_extraParams_1432_, lean_object* v___ys_1433_, lean_object* v_e_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1440_ = lean_box(1);
v___x_1441_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_delab___lam__0___closed__0));
v___x_1442_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___boxed), 10, 3);
lean_closure_set(v___x_1442_, 0, v_measure_1431_);
lean_closure_set(v___x_1442_, 1, v_extraParams_1432_);
lean_closure_set(v___x_1442_, 2, v___x_1441_);
v___x_1443_ = l_Lean_PrettyPrinter_delabCore___redArg(v_e_1434_, v___x_1440_, v___x_1442_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
if (lean_obj_tag(v___x_1443_) == 0)
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1452_; 
v_a_1444_ = lean_ctor_get(v___x_1443_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1446_ = v___x_1443_;
v_isShared_1447_ = v_isSharedCheck_1452_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1443_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1452_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v_fst_1448_; lean_object* v___x_1450_; 
v_fst_1448_ = lean_ctor_get(v_a_1444_, 0);
lean_inc(v_fst_1448_);
lean_dec(v_a_1444_);
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 0, v_fst_1448_);
v___x_1450_ = v___x_1446_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_fst_1448_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
else
{
lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1460_; 
v_a_1453_ = lean_ctor_get(v___x_1443_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1455_ = v___x_1443_;
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1443_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1458_; 
if (v_isShared_1456_ == 0)
{
v___x_1458_ = v___x_1455_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_a_1453_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_delab___lam__0___boxed(lean_object* v_measure_1461_, lean_object* v_extraParams_1462_, lean_object* v___ys_1463_, lean_object* v_e_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_Lean_Elab_TerminationMeasure_delab___lam__0(v_measure_1461_, v_extraParams_1462_, v___ys_1463_, v_e_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec_ref(v___ys_1463_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_delab(lean_object* v_arity_1471_, lean_object* v_extraParams_1472_, lean_object* v_measure_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_){
_start:
{
lean_object* v_fn_1479_; lean_object* v___f_1480_; lean_object* v___x_1481_; uint8_t v___x_1482_; lean_object* v___x_1483_; 
v_fn_1479_ = lean_ctor_get(v_measure_1473_, 1);
lean_inc_ref(v_fn_1479_);
lean_inc(v_extraParams_1472_);
v___f_1480_ = lean_alloc_closure((void*)(l_Lean_Elab_TerminationMeasure_delab___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1480_, 0, v_measure_1473_);
lean_closure_set(v___f_1480_, 1, v_extraParams_1472_);
v___x_1481_ = lean_nat_sub(v_arity_1471_, v_extraParams_1472_);
lean_dec(v_extraParams_1472_);
v___x_1482_ = 0;
v___x_1483_ = l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___redArg(v_fn_1479_, v___x_1481_, v___f_1480_, v___x_1482_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_delab___boxed(lean_object* v_arity_1484_, lean_object* v_extraParams_1485_, lean_object* v_measure_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Lean_Elab_TerminationMeasure_delab(v_arity_1484_, v_extraParams_1485_, v_measure_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_);
lean_dec(v_a_1490_);
lean_dec_ref(v_a_1489_);
lean_dec(v_a_1488_);
lean_dec_ref(v_a_1487_);
lean_dec(v_arity_1484_);
return v_res_1492_;
}
}
lean_object* runtime_initialize_Lean_Elab_Binders(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_TerminationMeasure(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
