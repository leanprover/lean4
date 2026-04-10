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
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
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
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__0_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__1_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__2_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__3 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__3_value;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4_value_aux_0),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4_value_aux_1),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4_value_aux_2),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__0_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "terminationBy"};
static const lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__2_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3_value_aux_0),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_169_; lean_object* v___x_3754__overap_170_; lean_object* v___x_171_; 
v___x_169_ = lean_obj_once(&l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6___closed__0, &l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6___closed__0_once, _init_l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6___closed__0);
v___x_3754__overap_170_ = lean_panic_fn_borrowed(v___x_169_, v_msg_161_);
lean_inc(v___y_167_);
lean_inc_ref(v___y_166_);
lean_inc(v___y_165_);
lean_inc_ref(v___y_164_);
lean_inc(v___y_163_);
lean_inc_ref(v___y_162_);
v___x_171_ = lean_apply_7(v___x_3754__overap_170_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, lean_box(0));
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
uint8_t v___x_6092__boxed_212_; lean_object* v_res_213_; 
v___x_6092__boxed_212_ = lean_unbox(v___x_202_);
v_res_213_ = l_Lean_Elab_TerminationMeasure_elab___lam__0(v_ys_199_, v_xs_200_, v_a_201_, v___x_6092__boxed_212_, v_zs_203_, v_x_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_);
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
lean_dec_ref(v___x_252_);
if (lean_obj_tag(v_val_254_) == 1)
{
uint8_t v_v_255_; 
v_v_255_ = lean_ctor_get_uint8(v_val_254_, 0);
lean_dec_ref(v_val_254_);
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
lean_object* v_options_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v_options_270_ = lean_ctor_get(v___y_268_, 2);
v___x_271_ = l_Lean_Elab_pp_macroStack;
v___x_272_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9_spec__10(v_options_270_, v___x_271_);
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
lean_object* v___x_304_; lean_object* v_env_305_; lean_object* v___x_306_; lean_object* v_mctx_307_; lean_object* v_lctx_308_; lean_object* v_options_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_304_ = lean_st_ref_get(v___y_302_);
v_env_305_ = lean_ctor_get(v___x_304_, 0);
lean_inc_ref(v_env_305_);
lean_dec(v___x_304_);
v___x_306_ = lean_st_ref_get(v___y_300_);
v_mctx_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc_ref(v_mctx_307_);
lean_dec(v___x_306_);
v_lctx_308_ = lean_ctor_get(v___y_299_, 2);
v_options_309_ = lean_ctor_get(v___y_301_, 2);
lean_inc_ref(v_options_309_);
lean_inc_ref(v_lctx_308_);
v___x_310_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_310_, 0, v_env_305_);
lean_ctor_set(v___x_310_, 1, v_mctx_307_);
lean_ctor_set(v___x_310_, 2, v_lctx_308_);
lean_ctor_set(v___x_310_, 3, v_options_309_);
v___x_311_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
lean_ctor_set(v___x_311_, 1, v_msgData_298_);
v___x_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__8___boxed(lean_object* v_msgData_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__8(v_msgData_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5___redArg(lean_object* v_msg_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
lean_object* v_ref_328_; lean_object* v___x_329_; lean_object* v_a_330_; lean_object* v_macroStack_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_342_; 
v_ref_328_ = lean_ctor_get(v___y_325_, 5);
v___x_329_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__8(v_msg_320_, v___y_323_, v___y_324_, v___y_325_, v___y_326_);
v_a_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_a_330_);
lean_dec_ref(v___x_329_);
v_macroStack_331_ = lean_ctor_get(v___y_321_, 1);
lean_inc_n(v_macroStack_331_, 2);
v___x_332_ = l_Lean_Elab_getBetterRef(v_ref_328_, v_macroStack_331_);
v___x_333_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg(v_a_330_, v_macroStack_331_, v___y_325_);
v_a_334_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_342_ == 0)
{
v___x_336_ = v___x_333_;
v_isShared_337_ = v_isSharedCheck_342_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_333_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_342_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_338_; lean_object* v___x_340_; 
v___x_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_332_);
lean_ctor_set(v___x_338_, 1, v_a_334_);
if (v_isShared_337_ == 0)
{
lean_ctor_set_tag(v___x_336_, 1);
lean_ctor_set(v___x_336_, 0, v___x_338_);
v___x_340_ = v___x_336_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_338_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5___redArg___boxed(lean_object* v_msg_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5___redArg(v_msg_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___redArg(lean_object* v_ref_352_, lean_object* v_msg_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v_fileName_361_; lean_object* v_fileMap_362_; lean_object* v_options_363_; lean_object* v_currRecDepth_364_; lean_object* v_maxRecDepth_365_; lean_object* v_ref_366_; lean_object* v_currNamespace_367_; lean_object* v_openDecls_368_; lean_object* v_initHeartbeats_369_; lean_object* v_maxHeartbeats_370_; lean_object* v_quotContext_371_; lean_object* v_currMacroScope_372_; uint8_t v_diag_373_; lean_object* v_cancelTk_x3f_374_; uint8_t v_suppressElabErrors_375_; lean_object* v_inheritedTraceOptions_376_; lean_object* v_ref_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v_fileName_361_ = lean_ctor_get(v___y_358_, 0);
v_fileMap_362_ = lean_ctor_get(v___y_358_, 1);
v_options_363_ = lean_ctor_get(v___y_358_, 2);
v_currRecDepth_364_ = lean_ctor_get(v___y_358_, 3);
v_maxRecDepth_365_ = lean_ctor_get(v___y_358_, 4);
v_ref_366_ = lean_ctor_get(v___y_358_, 5);
v_currNamespace_367_ = lean_ctor_get(v___y_358_, 6);
v_openDecls_368_ = lean_ctor_get(v___y_358_, 7);
v_initHeartbeats_369_ = lean_ctor_get(v___y_358_, 8);
v_maxHeartbeats_370_ = lean_ctor_get(v___y_358_, 9);
v_quotContext_371_ = lean_ctor_get(v___y_358_, 10);
v_currMacroScope_372_ = lean_ctor_get(v___y_358_, 11);
v_diag_373_ = lean_ctor_get_uint8(v___y_358_, sizeof(void*)*14);
v_cancelTk_x3f_374_ = lean_ctor_get(v___y_358_, 12);
v_suppressElabErrors_375_ = lean_ctor_get_uint8(v___y_358_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_376_ = lean_ctor_get(v___y_358_, 13);
v_ref_377_ = l_Lean_replaceRef(v_ref_352_, v_ref_366_);
lean_inc_ref(v_inheritedTraceOptions_376_);
lean_inc(v_cancelTk_x3f_374_);
lean_inc(v_currMacroScope_372_);
lean_inc(v_quotContext_371_);
lean_inc(v_maxHeartbeats_370_);
lean_inc(v_initHeartbeats_369_);
lean_inc(v_openDecls_368_);
lean_inc(v_currNamespace_367_);
lean_inc(v_maxRecDepth_365_);
lean_inc(v_currRecDepth_364_);
lean_inc_ref(v_options_363_);
lean_inc_ref(v_fileMap_362_);
lean_inc_ref(v_fileName_361_);
v___x_378_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_378_, 0, v_fileName_361_);
lean_ctor_set(v___x_378_, 1, v_fileMap_362_);
lean_ctor_set(v___x_378_, 2, v_options_363_);
lean_ctor_set(v___x_378_, 3, v_currRecDepth_364_);
lean_ctor_set(v___x_378_, 4, v_maxRecDepth_365_);
lean_ctor_set(v___x_378_, 5, v_ref_377_);
lean_ctor_set(v___x_378_, 6, v_currNamespace_367_);
lean_ctor_set(v___x_378_, 7, v_openDecls_368_);
lean_ctor_set(v___x_378_, 8, v_initHeartbeats_369_);
lean_ctor_set(v___x_378_, 9, v_maxHeartbeats_370_);
lean_ctor_set(v___x_378_, 10, v_quotContext_371_);
lean_ctor_set(v___x_378_, 11, v_currMacroScope_372_);
lean_ctor_set(v___x_378_, 12, v_cancelTk_x3f_374_);
lean_ctor_set(v___x_378_, 13, v_inheritedTraceOptions_376_);
lean_ctor_set_uint8(v___x_378_, sizeof(void*)*14, v_diag_373_);
lean_ctor_set_uint8(v___x_378_, sizeof(void*)*14 + 1, v_suppressElabErrors_375_);
v___x_379_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5___redArg(v_msg_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___x_378_, v___y_359_);
lean_dec_ref(v___x_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___redArg___boxed(lean_object* v_ref_380_, lean_object* v_msg_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___redArg(v_ref_380_, v_msg_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v_ref_380_);
return v_res_389_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2_spec__2(lean_object* v_a_390_, lean_object* v_as_391_, size_t v_i_392_, size_t v_stop_393_){
_start:
{
uint8_t v___x_394_; 
v___x_394_ = lean_usize_dec_eq(v_i_392_, v_stop_393_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_395_ = lean_array_uget_borrowed(v_as_391_, v_i_392_);
v___x_396_ = lean_expr_eqv(v_a_390_, v___x_395_);
if (v___x_396_ == 0)
{
size_t v___x_397_; size_t v___x_398_; 
v___x_397_ = ((size_t)1ULL);
v___x_398_ = lean_usize_add(v_i_392_, v___x_397_);
v_i_392_ = v___x_398_;
goto _start;
}
else
{
return v___x_396_;
}
}
else
{
uint8_t v___x_400_; 
v___x_400_ = 0;
return v___x_400_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2_spec__2___boxed(lean_object* v_a_401_, lean_object* v_as_402_, lean_object* v_i_403_, lean_object* v_stop_404_){
_start:
{
size_t v_i_boxed_405_; size_t v_stop_boxed_406_; uint8_t v_res_407_; lean_object* v_r_408_; 
v_i_boxed_405_ = lean_unbox_usize(v_i_403_);
lean_dec(v_i_403_);
v_stop_boxed_406_ = lean_unbox_usize(v_stop_404_);
lean_dec(v_stop_404_);
v_res_407_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2_spec__2(v_a_401_, v_as_402_, v_i_boxed_405_, v_stop_boxed_406_);
lean_dec_ref(v_as_402_);
lean_dec_ref(v_a_401_);
v_r_408_ = lean_box(v_res_407_);
return v_r_408_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2(lean_object* v_as_409_, lean_object* v_a_410_){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; uint8_t v___x_413_; 
v___x_411_ = lean_unsigned_to_nat(0u);
v___x_412_ = lean_array_get_size(v_as_409_);
v___x_413_ = lean_nat_dec_lt(v___x_411_, v___x_412_);
if (v___x_413_ == 0)
{
return v___x_413_;
}
else
{
if (v___x_413_ == 0)
{
return v___x_413_;
}
else
{
size_t v___x_414_; size_t v___x_415_; uint8_t v___x_416_; 
v___x_414_ = ((size_t)0ULL);
v___x_415_ = lean_usize_of_nat(v___x_412_);
v___x_416_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2_spec__2(v_a_410_, v_as_409_, v___x_414_, v___x_415_);
return v___x_416_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2___boxed(lean_object* v_as_417_, lean_object* v_a_418_){
_start:
{
uint8_t v_res_419_; lean_object* v_r_420_; 
v_res_419_ = l_Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2(v_as_417_, v_a_418_);
lean_dec_ref(v_a_418_);
lean_dec_ref(v_as_417_);
v_r_420_ = lean_box(v_res_419_);
return v_r_420_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3___closed__1(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3___closed__0));
v___x_423_ = l_Lean_stringToMessageData(v___x_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3(lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
if (lean_obj_tag(v_a_424_) == 0)
{
lean_object* v___x_426_; 
v___x_426_ = l_List_reverse___redArg(v_a_425_);
return v___x_426_;
}
else
{
lean_object* v_head_427_; lean_object* v_tail_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_440_; 
v_head_427_ = lean_ctor_get(v_a_424_, 0);
v_tail_428_ = lean_ctor_get(v_a_424_, 1);
v_isSharedCheck_440_ = !lean_is_exclusive(v_a_424_);
if (v_isSharedCheck_440_ == 0)
{
v___x_430_ = v_a_424_;
v_isShared_431_ = v_isSharedCheck_440_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_tail_428_);
lean_inc(v_head_427_);
lean_dec(v_a_424_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_440_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_437_; 
v___x_432_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3___closed__1, &l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3___closed__1);
v___x_433_ = l_Lean_MessageData_ofExpr(v_head_427_);
v___x_434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_432_);
lean_ctor_set(v___x_434_, 1, v___x_433_);
v___x_435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
lean_ctor_set(v___x_435_, 1, v___x_432_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 1, v_a_425_);
lean_ctor_set(v___x_430_, 0, v___x_435_);
v___x_437_ = v___x_430_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_435_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v_a_425_);
v___x_437_ = v_reuseFailAlloc_439_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
v_a_424_ = v_tail_428_;
v_a_425_ = v___x_437_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__3(void){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_444_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__2));
v___x_445_ = lean_unsigned_to_nat(14u);
v___x_446_ = lean_unsigned_to_nat(22u);
v___x_447_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__1));
v___x_448_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__0));
v___x_449_ = l_mkPanicMessageWithDecl(v___x_448_, v___x_447_, v___x_446_, v___x_445_, v___x_444_);
return v___x_449_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__5(void){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_451_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__4));
v___x_452_ = l_Lean_stringToMessageData(v___x_451_);
return v___x_452_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__7(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__6));
v___x_455_ = l_Lean_stringToMessageData(v___x_454_);
return v___x_455_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__9(void){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__8));
v___x_458_ = l_Lean_stringToMessageData(v___x_457_);
return v___x_458_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__11(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__10));
v___x_461_ = l_Lean_stringToMessageData(v___x_460_);
return v___x_461_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__13(void){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__12));
v___x_464_ = l_Lean_stringToMessageData(v___x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__1(lean_object* v_body_465_, lean_object* v_ys_466_, lean_object* v_vars_467_, lean_object* v_extraParams_468_, uint8_t v_structural_469_, lean_object* v_ref_470_, lean_object* v_xs_471_, lean_object* v_type_x27_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v___x_480_; uint8_t v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; uint8_t v___x_485_; lean_object* v___x_486_; 
v___x_480_ = lean_box(0);
v___x_481_ = 1;
v___x_482_ = lean_box(v___x_481_);
v___x_483_ = lean_box(v___x_481_);
v___x_484_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_484_, 0, v_body_465_);
lean_closure_set(v___x_484_, 1, v___x_480_);
lean_closure_set(v___x_484_, 2, v___x_482_);
lean_closure_set(v___x_484_, 3, v___x_483_);
lean_closure_set(v___x_484_, 4, v___x_480_);
v___x_485_ = 1;
v___x_486_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_484_, v___x_485_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_545_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_545_ == 0)
{
v___x_489_ = v___x_486_;
v_isShared_490_ = v_isSharedCheck_545_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_486_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_545_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_491_; lean_object* v___f_492_; lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; 
v___x_491_ = lean_box(v___x_481_);
lean_inc(v_a_487_);
lean_inc_ref(v_xs_471_);
lean_inc_ref(v_ys_466_);
v___f_492_ = lean_alloc_closure((void*)(l_Lean_Elab_TerminationMeasure_elab___lam__0___boxed), 13, 4);
lean_closure_set(v___f_492_, 0, v_ys_466_);
lean_closure_set(v___f_492_, 1, v_xs_471_);
lean_closure_set(v___f_492_, 2, v_a_487_);
lean_closure_set(v___f_492_, 3, v___x_491_);
if (v_structural_469_ == 0)
{
lean_dec(v_a_487_);
lean_dec_ref(v_xs_471_);
lean_dec_ref(v_ys_466_);
v___y_509_ = v___y_473_;
v___y_510_ = v___y_474_;
v___y_511_ = v___y_475_;
v___y_512_ = v___y_476_;
v___y_513_ = v___y_477_;
v___y_514_ = v___y_478_;
goto v___jp_508_;
}
else
{
lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_518_ = l_Array_append___redArg(v_ys_466_, v_xs_471_);
lean_dec_ref(v_xs_471_);
v___x_519_ = l_Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2(v___x_518_, v_a_487_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
lean_dec_ref(v___f_492_);
lean_del_object(v___x_489_);
lean_dec(v_type_x27_472_);
v___x_520_ = lean_array_to_list(v___x_518_);
v___x_521_ = lean_box(0);
v___x_522_ = l_List_mapTR_loop___at___00Lean_Elab_TerminationMeasure_elab_spec__3(v___x_520_, v___x_521_);
v___x_523_ = l_Lean_MessageData_andList(v___x_522_);
v___x_524_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__5, &l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__5_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__5);
v___x_525_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__7, &l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__7_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__7);
v___x_526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
lean_ctor_set(v___x_526_, 1, v___x_523_);
v___x_527_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__9, &l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__9_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__9);
v___x_528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_526_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
v___x_529_ = l_Lean_indentExpr(v_a_487_);
v___x_530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_528_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__11, &l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__11_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__11);
v___x_532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_530_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_524_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__13, &l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__13_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__13);
v___x_535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_533_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
v___x_536_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___redArg(v_ref_470_, v___x_535_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
v_a_537_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_544_ == 0)
{
v___x_539_ = v___x_536_;
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_536_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_537_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
else
{
lean_dec_ref(v___x_518_);
lean_dec(v_a_487_);
v___y_509_ = v___y_473_;
v___y_510_ = v___y_474_;
v___y_511_ = v___y_475_;
v___y_512_ = v___y_476_;
v___y_513_ = v___y_477_;
v___y_514_ = v___y_478_;
goto v___jp_508_;
}
}
v___jp_493_:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_504_; 
v___x_501_ = lean_array_get_size(v_vars_467_);
v___x_502_ = lean_nat_sub(v_extraParams_468_, v___x_501_);
if (v_isShared_490_ == 0)
{
lean_ctor_set_tag(v___x_489_, 1);
lean_ctor_set(v___x_489_, 0, v___x_502_);
v___x_504_ = v___x_489_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_502_);
v___x_504_ = v_reuseFailAlloc_507_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
uint8_t v___x_505_; lean_object* v___x_506_; 
v___x_505_ = 0;
v___x_506_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___redArg(v___y_500_, v___x_504_, v___f_492_, v___x_505_, v___x_505_, v___y_494_, v___y_495_, v___y_498_, v___y_499_, v___y_497_, v___y_496_);
return v___x_506_;
}
}
v___jp_508_:
{
if (lean_obj_tag(v_type_x27_472_) == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__3, &l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__3_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__3);
v___x_516_ = l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__1(v___x_515_);
v___y_494_ = v___y_509_;
v___y_495_ = v___y_510_;
v___y_496_ = v___y_514_;
v___y_497_ = v___y_513_;
v___y_498_ = v___y_511_;
v___y_499_ = v___y_512_;
v___y_500_ = v___x_516_;
goto v___jp_493_;
}
else
{
lean_object* v_val_517_; 
v_val_517_ = lean_ctor_get(v_type_x27_472_, 0);
lean_inc(v_val_517_);
lean_dec_ref(v_type_x27_472_);
v___y_494_ = v___y_509_;
v___y_495_ = v___y_510_;
v___y_496_ = v___y_514_;
v___y_497_ = v___y_513_;
v___y_498_ = v___y_511_;
v___y_499_ = v___y_512_;
v___y_500_ = v_val_517_;
goto v___jp_493_;
}
}
}
}
else
{
lean_dec(v_type_x27_472_);
lean_dec_ref(v_xs_471_);
lean_dec_ref(v_ys_466_);
return v___x_486_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__1___boxed(lean_object* v_body_546_, lean_object* v_ys_547_, lean_object* v_vars_548_, lean_object* v_extraParams_549_, lean_object* v_structural_550_, lean_object* v_ref_551_, lean_object* v_xs_552_, lean_object* v_type_x27_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
uint8_t v_structural_boxed_561_; lean_object* v_res_562_; 
v_structural_boxed_561_ = lean_unbox(v_structural_550_);
v_res_562_ = l_Lean_Elab_TerminationMeasure_elab___lam__1(v_body_546_, v_ys_547_, v_vars_548_, v_extraParams_549_, v_structural_boxed_561_, v_ref_551_, v_xs_552_, v_type_x27_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec(v_ref_551_);
lean_dec(v_extraParams_549_);
lean_dec_ref(v_vars_548_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__2(lean_object* v_hint_563_, lean_object* v_extraParams_564_, lean_object* v_ys_565_, lean_object* v_type_x27_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v_ref_574_; uint8_t v_structural_575_; lean_object* v_vars_576_; lean_object* v_body_577_; lean_object* v___x_578_; lean_object* v___f_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v_ref_574_ = lean_ctor_get(v_hint_563_, 0);
lean_inc(v_ref_574_);
v_structural_575_ = lean_ctor_get_uint8(v_hint_563_, sizeof(void*)*3);
v_vars_576_ = lean_ctor_get(v_hint_563_, 1);
lean_inc_ref_n(v_vars_576_, 2);
v_body_577_ = lean_ctor_get(v_hint_563_, 2);
lean_inc(v_body_577_);
lean_dec_ref(v_hint_563_);
v___x_578_ = lean_box(v_structural_575_);
v___f_579_ = lean_alloc_closure((void*)(l_Lean_Elab_TerminationMeasure_elab___lam__1___boxed), 15, 6);
lean_closure_set(v___f_579_, 0, v_body_577_);
lean_closure_set(v___f_579_, 1, v_ys_565_);
lean_closure_set(v___f_579_, 2, v_vars_576_);
lean_closure_set(v___f_579_, 3, v_extraParams_564_);
lean_closure_set(v___f_579_, 4, v___x_578_);
lean_closure_set(v___f_579_, 5, v_ref_574_);
v___x_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_580_, 0, v_type_x27_566_);
v___x_581_ = l_Lean_Elab_Term_elabFunBinders___redArg(v_vars_576_, v___x_580_, v___f_579_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
lean_dec_ref(v_vars_576_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__2___boxed(lean_object* v_hint_582_, lean_object* v_extraParams_583_, lean_object* v_ys_584_, lean_object* v_type_x27_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lean_Elab_TerminationMeasure_elab___lam__2(v_hint_582_, v_extraParams_583_, v_ys_584_, v_type_x27_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
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
lean_object* v_ref_639_; uint8_t v_structural_640_; lean_object* v_vars_641_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v_msg_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___x_700_; uint8_t v___x_701_; 
v_ref_639_ = lean_ctor_get(v_hint_624_, 0);
v_structural_640_ = lean_ctor_get_uint8(v_hint_624_, sizeof(void*)*3);
v_vars_641_ = lean_ctor_get(v_hint_624_, 1);
v___x_700_ = lean_array_get_size(v_vars_641_);
v___x_701_ = lean_nat_dec_lt(v_extraParams_626_, v___x_700_);
if (v___x_701_ == 0)
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
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v_msg_712_; lean_object* v___x_713_; lean_object* v_ident_714_; lean_object* v___x_715_; uint8_t v___x_716_; 
lean_dec_ref(v___f_628_);
lean_dec_ref(v_type_627_);
v___x_702_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters(v___x_700_);
v___x_703_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__5, &l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__5_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__5);
v___x_704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_702_);
lean_ctor_set(v___x_704_, 1, v___x_703_);
lean_inc(v_funName_629_);
v___x_705_ = l_Lean_MessageData_ofName(v_funName_629_);
v___x_706_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__7, &l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__7_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__7);
v___x_707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_705_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
v___x_708_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters(v_extraParams_626_);
v___x_709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_707_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
v___x_710_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__9, &l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__9_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__9);
v___x_711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_709_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
v_msg_712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_712_, 0, v___x_704_);
lean_ctor_set(v_msg_712_, 1, v___x_711_);
v___x_713_ = lean_unsigned_to_nat(0u);
v_ident_714_ = lean_array_fget_borrowed(v_vars_641_, v___x_713_);
v___x_715_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__11));
lean_inc(v_ident_714_);
v___x_716_ = l_Lean_Syntax_isOfKind(v_ident_714_, v___x_715_);
if (v___x_716_ == 0)
{
lean_dec(v_funName_629_);
v_msg_684_ = v_msg_712_;
v___y_685_ = v___y_630_;
v___y_686_ = v___y_631_;
v___y_687_ = v___y_632_;
v___y_688_ = v___y_633_;
v___y_689_ = v___y_634_;
v___y_690_ = v___y_635_;
goto v___jp_683_;
}
else
{
lean_object* v___x_717_; uint8_t v___x_718_; 
v___x_717_ = l_Lean_TSyntax_getId(v_ident_714_);
v___x_718_ = l_Lean_Name_isSuffixOf(v___x_717_, v_funName_629_);
lean_dec(v_funName_629_);
lean_dec(v___x_717_);
if (v___x_718_ == 0)
{
v_msg_684_ = v_msg_712_;
v___y_685_ = v___y_630_;
v___y_686_ = v___y_631_;
v___y_687_ = v___y_632_;
v___y_688_ = v___y_633_;
v___y_689_ = v___y_634_;
v___y_690_ = v___y_635_;
goto v___jp_683_;
}
else
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v_msg_722_; 
v___x_719_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__13, &l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__13_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__13);
v___x_720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_720_, 0, v_msg_712_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
v___x_721_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__16, &l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__16_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__16);
v_msg_722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_722_, 0, v___x_720_);
lean_ctor_set(v_msg_722_, 1, v___x_721_);
v_msg_684_ = v_msg_722_;
v___y_685_ = v___y_630_;
v___y_686_ = v___y_631_;
v___y_687_ = v___y_632_;
v___y_688_ = v___y_633_;
v___y_689_ = v___y_634_;
v___y_690_ = v___y_635_;
goto v___jp_683_;
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
lean_object* v_a_656_; lean_object* v___x_657_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc_n(v_a_656_, 2);
lean_dec_ref(v___x_655_);
v___x_657_ = l_Lean_Meta_check(v_a_656_, v___y_645_, v___y_646_, v___y_647_, v___y_648_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_665_; 
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_665_ == 0)
{
lean_object* v_unused_666_; 
v_unused_666_ = lean_ctor_get(v___x_657_, 0);
lean_dec(v_unused_666_);
v___x_659_ = v___x_657_;
v_isShared_660_ = v_isSharedCheck_665_;
goto v_resetjp_658_;
}
else
{
lean_dec(v___x_657_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_665_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_661_; lean_object* v___x_663_; 
lean_inc(v_ref_639_);
v___x_661_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_661_, 0, v_ref_639_);
lean_ctor_set(v___x_661_, 1, v_a_656_);
lean_ctor_set_uint8(v___x_661_, sizeof(void*)*2, v_structural_640_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v___x_661_);
v___x_663_ = v___x_659_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_661_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
else
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_674_; 
lean_dec(v_a_656_);
v_a_667_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_674_ == 0)
{
v___x_669_ = v___x_657_;
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_657_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_667_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
else
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_682_; 
v_a_675_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_682_ == 0)
{
v___x_677_ = v___x_655_;
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_655_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_678_ == 0)
{
v___x_680_ = v___x_677_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_a_675_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
v___jp_683_:
{
lean_object* v___x_691_; lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_699_; 
v___x_691_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___redArg(v_ref_639_, v_msg_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
v_a_692_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_699_ == 0)
{
v___x_694_ = v___x_691_;
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_691_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_a_692_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__3___boxed(lean_object* v___x_723_, lean_object* v_hint_724_, lean_object* v_arity_725_, lean_object* v_extraParams_726_, lean_object* v_type_727_, lean_object* v___f_728_, lean_object* v_funName_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
uint8_t v___x_6757__boxed_737_; lean_object* v_res_738_; 
v___x_6757__boxed_737_ = lean_unbox(v___x_723_);
v_res_738_ = l_Lean_Elab_TerminationMeasure_elab___lam__3(v___x_6757__boxed_737_, v_hint_724_, v_arity_725_, v_extraParams_726_, v_type_727_, v___f_728_, v_funName_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v_arity_725_);
lean_dec_ref(v_hint_724_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab(lean_object* v_funName_739_, lean_object* v_type_740_, lean_object* v_arity_741_, lean_object* v_extraParams_742_, lean_object* v_hint_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_){
_start:
{
lean_object* v___f_751_; uint8_t v___x_752_; lean_object* v___x_753_; lean_object* v___y_754_; lean_object* v___x_755_; 
lean_inc(v_extraParams_742_);
lean_inc_ref(v_hint_743_);
v___f_751_ = lean_alloc_closure((void*)(l_Lean_Elab_TerminationMeasure_elab___lam__2___boxed), 11, 2);
lean_closure_set(v___f_751_, 0, v_hint_743_);
lean_closure_set(v___f_751_, 1, v_extraParams_742_);
v___x_752_ = lean_nat_dec_le(v_extraParams_742_, v_arity_741_);
v___x_753_ = lean_box(v___x_752_);
lean_inc(v_funName_739_);
v___y_754_ = lean_alloc_closure((void*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___boxed), 14, 7);
lean_closure_set(v___y_754_, 0, v___x_753_);
lean_closure_set(v___y_754_, 1, v_hint_743_);
lean_closure_set(v___y_754_, 2, v_arity_741_);
lean_closure_set(v___y_754_, 3, v_extraParams_742_);
lean_closure_set(v___y_754_, 4, v_type_740_);
lean_closure_set(v___y_754_, 5, v___f_751_);
lean_closure_set(v___y_754_, 6, v_funName_739_);
v___x_755_ = l_Lean_Elab_Term_withDeclName___redArg(v_funName_739_, v___y_754_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___boxed(lean_object* v_funName_756_, lean_object* v_type_757_, lean_object* v_arity_758_, lean_object* v_extraParams_759_, lean_object* v_hint_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_Elab_TerminationMeasure_elab(v_funName_756_, v_type_757_, v_arity_758_, v_extraParams_759_, v_hint_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_);
lean_dec(v_a_766_);
lean_dec_ref(v_a_765_);
lean_dec(v_a_764_);
lean_dec_ref(v_a_763_);
lean_dec(v_a_762_);
lean_dec_ref(v_a_761_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4(lean_object* v_00_u03b1_769_, lean_object* v_ref_770_, lean_object* v_msg_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___redArg(v_ref_770_, v_msg_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___boxed(lean_object* v_00_u03b1_780_, lean_object* v_ref_781_, lean_object* v_msg_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4(v_00_u03b1_780_, v_ref_781_, v_msg_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v_ref_781_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5(lean_object* v_00_u03b1_791_, lean_object* v_msg_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5___redArg(v_msg_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5___boxed(lean_object* v_00_u03b1_801_, lean_object* v_msg_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5(v_00_u03b1_801_, v_msg_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9(lean_object* v_msgData_811_, lean_object* v_macroStack_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg(v_msgData_811_, v_macroStack_812_, v___y_817_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___boxed(lean_object* v_msgData_821_, lean_object* v_macroStack_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9(v_msgData_821_, v_macroStack_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1(lean_object* v_msg_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v___f_838_; lean_object* v___x_417__overap_839_; lean_object* v___x_840_; 
v___f_838_ = ((lean_object*)(l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1___closed__0));
v___x_417__overap_839_ = lean_panic_fn_borrowed(v___f_838_, v_msg_832_);
lean_inc(v___y_836_);
lean_inc_ref(v___y_835_);
lean_inc(v___y_834_);
lean_inc_ref(v___y_833_);
v___x_840_ = lean_apply_5(v___x_417__overap_839_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, lean_box(0));
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1___boxed(lean_object* v_msg_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1(v_msg_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg___lam__0(lean_object* v_k_848_, lean_object* v_b_849_, lean_object* v_c_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v___x_856_; 
lean_inc(v___y_854_);
lean_inc_ref(v___y_853_);
lean_inc(v___y_852_);
lean_inc_ref(v___y_851_);
v___x_856_ = lean_apply_7(v_k_848_, v_b_849_, v_c_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, lean_box(0));
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg___lam__0___boxed(lean_object* v_k_857_, lean_object* v_b_858_, lean_object* v_c_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg___lam__0(v_k_857_, v_b_858_, v_c_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg(lean_object* v_e_866_, lean_object* v_k_867_, uint8_t v_cleanupAnnotations_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
lean_object* v___f_874_; uint8_t v___x_875_; uint8_t v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v___f_874_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_874_, 0, v_k_867_);
v___x_875_ = 1;
v___x_876_ = 0;
v___x_877_ = lean_box(0);
v___x_878_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_866_, v___x_875_, v___x_876_, v___x_875_, v___x_876_, v___x_877_, v___f_874_, v_cleanupAnnotations_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_878_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_878_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
else
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_894_; 
v_a_887_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_894_ == 0)
{
v___x_889_ = v___x_878_;
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_878_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_890_ == 0)
{
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_887_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg___boxed(lean_object* v_e_895_, lean_object* v_k_896_, lean_object* v_cleanupAnnotations_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_903_; lean_object* v_res_904_; 
v_cleanupAnnotations_boxed_903_ = lean_unbox(v_cleanupAnnotations_897_);
v_res_904_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg(v_e_895_, v_k_896_, v_cleanupAnnotations_boxed_903_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2(lean_object* v_00_u03b1_905_, lean_object* v_e_906_, lean_object* v_k_907_, uint8_t v_cleanupAnnotations_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg(v_e_906_, v_k_907_, v_cleanupAnnotations_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___boxed(lean_object* v_00_u03b1_915_, lean_object* v_e_916_, lean_object* v_k_917_, lean_object* v_cleanupAnnotations_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_924_; lean_object* v_res_925_; 
v_cleanupAnnotations_boxed_924_ = lean_unbox(v_cleanupAnnotations_918_);
v_res_925_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2(v_00_u03b1_915_, v_e_916_, v_k_917_, v_cleanupAnnotations_boxed_924_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0_spec__3(lean_object* v_xs_926_, lean_object* v_v_927_, lean_object* v_i_928_){
_start:
{
lean_object* v___x_929_; uint8_t v___x_930_; 
v___x_929_ = lean_array_get_size(v_xs_926_);
v___x_930_ = lean_nat_dec_lt(v_i_928_, v___x_929_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; 
lean_dec(v_i_928_);
v___x_931_ = lean_box(0);
return v___x_931_;
}
else
{
lean_object* v___x_932_; uint8_t v___x_933_; 
v___x_932_ = lean_array_fget_borrowed(v_xs_926_, v_i_928_);
v___x_933_ = lean_expr_eqv(v___x_932_, v_v_927_);
if (v___x_933_ == 0)
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = lean_unsigned_to_nat(1u);
v___x_935_ = lean_nat_add(v_i_928_, v___x_934_);
lean_dec(v_i_928_);
v_i_928_ = v___x_935_;
goto _start;
}
else
{
lean_object* v___x_937_; 
v___x_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_937_, 0, v_i_928_);
return v___x_937_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0_spec__3___boxed(lean_object* v_xs_938_, lean_object* v_v_939_, lean_object* v_i_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0_spec__3(v_xs_938_, v_v_939_, v_i_940_);
lean_dec_ref(v_v_939_);
lean_dec_ref(v_xs_938_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0(lean_object* v_xs_942_, lean_object* v_v_943_){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = lean_unsigned_to_nat(0u);
v___x_945_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0_spec__3(v_xs_942_, v_v_943_, v___x_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0___boxed(lean_object* v_xs_946_, lean_object* v_v_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0(v_xs_946_, v_v_947_);
lean_dec_ref(v_v_947_);
lean_dec_ref(v_xs_946_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0(lean_object* v_xs_949_, lean_object* v_v_950_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0(v_xs_949_, v_v_950_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v___x_952_; 
v___x_952_ = lean_box(0);
return v___x_952_;
}
else
{
lean_object* v_val_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
v_val_953_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___x_951_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_val_953_);
lean_dec(v___x_951_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_val_953_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0___boxed(lean_object* v_xs_961_, lean_object* v_v_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0(v_xs_961_, v_v_962_);
lean_dec_ref(v_v_962_);
lean_dec_ref(v_xs_961_);
return v_res_963_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_966_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__1));
v___x_967_ = lean_unsigned_to_nat(8u);
v___x_968_ = lean_unsigned_to_nat(93u);
v___x_969_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__0));
v___x_970_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__0));
v___x_971_ = l_mkPanicMessageWithDecl(v___x_970_, v___x_969_, v___x_968_, v___x_967_, v___x_966_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_structuralArg___lam__0(lean_object* v_ys_972_, lean_object* v_e_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = l_Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0(v_ys_972_, v_e_973_);
if (lean_obj_tag(v___x_979_) == 1)
{
lean_object* v_val_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
v_val_980_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_979_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_val_980_);
lean_dec(v___x_979_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
lean_ctor_set_tag(v___x_982_, 0);
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_val_980_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
else
{
lean_object* v___x_988_; lean_object* v___x_989_; 
lean_dec(v___x_979_);
v___x_988_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__2, &l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__2_once, _init_l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__2);
v___x_989_ = l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1(v___x_988_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
return v___x_989_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___boxed(lean_object* v_ys_990_, lean_object* v_e_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Lean_Elab_TerminationMeasure_structuralArg___lam__0(v_ys_990_, v_e_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec_ref(v_e_991_);
lean_dec_ref(v_ys_990_);
return v_res_997_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_structuralArg___closed__1(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_999_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_structuralArg___closed__0));
v___x_1000_ = lean_unsigned_to_nat(2u);
v___x_1001_ = lean_unsigned_to_nat(90u);
v___x_1002_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__0));
v___x_1003_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__0));
v___x_1004_ = l_mkPanicMessageWithDecl(v___x_1003_, v___x_1002_, v___x_1001_, v___x_1000_, v___x_999_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_structuralArg(lean_object* v_measure_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_){
_start:
{
uint8_t v_structural_1012_; 
v_structural_1012_ = lean_ctor_get_uint8(v_measure_1006_, sizeof(void*)*2);
if (v_structural_1012_ == 0)
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
lean_dec_ref(v_measure_1006_);
v___x_1013_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_structuralArg___closed__1, &l_Lean_Elab_TerminationMeasure_structuralArg___closed__1_once, _init_l_Lean_Elab_TerminationMeasure_structuralArg___closed__1);
v___x_1014_ = l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1(v___x_1013_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_);
return v___x_1014_;
}
else
{
lean_object* v_fn_1015_; lean_object* v___f_1016_; uint8_t v___x_1017_; lean_object* v___x_1018_; 
v_fn_1015_ = lean_ctor_get(v_measure_1006_, 1);
lean_inc_ref(v_fn_1015_);
lean_dec_ref(v_measure_1006_);
v___f_1016_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_structuralArg___closed__2));
v___x_1017_ = 0;
v___x_1018_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg(v_fn_1015_, v___f_1016_, v___x_1017_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_);
return v___x_1018_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_structuralArg___boxed(lean_object* v_measure_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_Elab_TerminationMeasure_structuralArg(v_measure_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_);
lean_dec(v_a_1023_);
lean_dec_ref(v_a_1022_);
lean_dec(v_a_1021_);
lean_dec_ref(v_a_1020_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2___redArg(lean_object* v___y_1026_){
_start:
{
lean_object* v_subExpr_1028_; lean_object* v_expr_1029_; lean_object* v___x_1030_; 
v_subExpr_1028_ = lean_ctor_get(v___y_1026_, 3);
v_expr_1029_ = lean_ctor_get(v_subExpr_1028_, 0);
lean_inc_ref(v_expr_1029_);
v___x_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1030_, 0, v_expr_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2___redArg___boxed(lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2___redArg(v___y_1031_);
lean_dec_ref(v___y_1031_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2(lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2___redArg(v___y_1034_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2___boxed(lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2(v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0(lean_object* v_____do__lift_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
uint8_t v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1058_ = 0;
v___x_1059_ = l_Lean_SourceInfo_fromRef(v_____do__lift_1050_, v___x_1058_);
v___x_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0___boxed(lean_object* v_____do__lift_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0(v_____do__lift_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v_____do__lift_1061_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg(lean_object* v_b_1079_){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; uint8_t v___x_1083_; 
v___x_1081_ = lean_array_get_size(v_b_1079_);
v___x_1082_ = lean_unsigned_to_nat(0u);
v___x_1083_ = lean_nat_dec_eq(v___x_1081_, v___x_1082_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; uint8_t v___x_1089_; 
v___x_1084_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4));
v___x_1085_ = lean_box(0);
v___x_1086_ = lean_unsigned_to_nat(1u);
v___x_1087_ = lean_nat_sub(v___x_1081_, v___x_1086_);
v___x_1088_ = lean_array_get_borrowed(v___x_1085_, v_b_1079_, v___x_1087_);
lean_dec(v___x_1087_);
lean_inc(v___x_1088_);
v___x_1089_ = l_Lean_Syntax_isOfKind(v___x_1088_, v___x_1084_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; 
v___x_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1090_, 0, v_b_1079_);
return v___x_1090_;
}
else
{
lean_object* v___x_1091_; 
v___x_1091_ = lean_array_pop(v_b_1079_);
v_b_1079_ = v___x_1091_;
goto _start;
}
}
else
{
lean_object* v___x_1093_; 
v___x_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1093_, 0, v_b_1079_);
return v___x_1093_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___boxed(lean_object* v_b_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg(v_b_1094_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__0(lean_object* v_a_1097_, lean_object* v___x_1098_, size_t v_sz_1099_, size_t v_i_1100_, lean_object* v_bs_1101_){
_start:
{
uint8_t v___x_1102_; 
v___x_1102_ = lean_usize_dec_lt(v_i_1100_, v_sz_1099_);
if (v___x_1102_ == 0)
{
lean_dec(v___x_1098_);
return v_bs_1101_;
}
else
{
lean_object* v_v_1103_; lean_object* v___x_1104_; lean_object* v_bs_x27_1105_; lean_object* v___y_1107_; lean_object* v___x_1112_; uint8_t v___x_1113_; 
v_v_1103_ = lean_array_uget(v_bs_1101_, v_i_1100_);
v___x_1104_ = lean_unsigned_to_nat(0u);
v_bs_x27_1105_ = lean_array_uset(v_bs_1101_, v_i_1100_, v___x_1104_);
v___x_1112_ = l_Lean_TSyntax_getId(v_v_1103_);
v___x_1113_ = l_Lean_Syntax_hasIdent(v___x_1112_, v_a_1097_);
lean_dec(v___x_1112_);
if (v___x_1113_ == 0)
{
lean_dec(v_v_1103_);
lean_inc(v___x_1098_);
v___y_1107_ = v___x_1098_;
goto v___jp_1106_;
}
else
{
v___y_1107_ = v_v_1103_;
goto v___jp_1106_;
}
v___jp_1106_:
{
size_t v___x_1108_; size_t v___x_1109_; lean_object* v___x_1110_; 
v___x_1108_ = ((size_t)1ULL);
v___x_1109_ = lean_usize_add(v_i_1100_, v___x_1108_);
v___x_1110_ = lean_array_uset(v_bs_x27_1105_, v_i_1100_, v___y_1107_);
v_i_1100_ = v___x_1109_;
v_bs_1101_ = v___x_1110_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__0___boxed(lean_object* v_a_1114_, lean_object* v___x_1115_, lean_object* v_sz_1116_, lean_object* v_i_1117_, lean_object* v_bs_1118_){
_start:
{
size_t v_sz_boxed_1119_; size_t v_i_boxed_1120_; lean_object* v_res_1121_; 
v_sz_boxed_1119_ = lean_unbox_usize(v_sz_1116_);
lean_dec(v_sz_1116_);
v_i_boxed_1120_ = lean_unbox_usize(v_i_1117_);
lean_dec(v_i_1117_);
v_res_1121_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__0(v_a_1114_, v___x_1115_, v_sz_boxed_1119_, v_i_boxed_1120_, v_bs_1118_);
lean_dec(v_a_1114_);
return v_res_1121_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7(void){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = l_Array_mkArray0(lean_box(0));
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__1___boxed(lean_object* v_a_1137_, lean_object* v_measure_1138_, lean_object* v_n_1139_, lean_object* v_n_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__1(v_a_1137_, v_measure_1138_, v_n_1139_, v_n_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec(v_n_1139_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go(lean_object* v_measure_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_){
_start:
{
lean_object* v_zero_1159_; uint8_t v_isZero_1160_; 
v_zero_1159_ = lean_unsigned_to_nat(0u);
v_isZero_1160_ = lean_nat_dec_eq(v_a_1150_, v_zero_1159_);
if (v_isZero_1160_ == 1)
{
lean_object* v___x_1161_; 
v___x_1161_ = l_Lean_PrettyPrinter_Delaborator_delab(v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_a_1162_; lean_object* v_ref_1163_; lean_object* v___x_1164_; lean_object* v_a_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; size_t v_sz_1170_; size_t v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_a_1162_);
lean_dec_ref(v___x_1161_);
v_ref_1163_ = lean_ctor_get(v_a_1156_, 5);
v___x_1164_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0(v_ref_1163_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
lean_inc_n(v_a_1165_, 2);
lean_dec_ref(v___x_1164_);
v___x_1166_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4));
v___x_1167_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__0));
v___x_1168_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1168_, 0, v_a_1165_);
lean_ctor_set(v___x_1168_, 1, v___x_1167_);
v___x_1169_ = l_Lean_Syntax_node1(v_a_1165_, v___x_1166_, v___x_1168_);
v_sz_1170_ = lean_array_size(v_a_1151_);
v___x_1171_ = ((size_t)0ULL);
v___x_1172_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__0(v_a_1162_, v___x_1169_, v_sz_1170_, v___x_1171_, v_a_1151_);
v___x_1173_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg(v___x_1172_);
if (lean_obj_tag(v___x_1173_) == 0)
{
uint8_t v_structural_1174_; 
v_structural_1174_ = lean_ctor_get_uint8(v_measure_1149_, sizeof(void*)*2);
lean_dec_ref(v_measure_1149_);
if (v_structural_1174_ == 0)
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1213_; 
v_a_1175_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1177_ = v___x_1173_;
v_isShared_1178_ = v_isSharedCheck_1213_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1173_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1213_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1179_; uint8_t v___x_1180_; 
v___x_1179_ = lean_array_get_size(v_a_1175_);
v___x_1180_ = lean_nat_dec_eq(v___x_1179_, v_zero_1159_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1195_; 
v___x_1181_ = l_Lean_SourceInfo_fromRef(v_ref_1163_, v___x_1180_);
v___x_1182_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3));
v___x_1183_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__4));
lean_inc_n(v___x_1181_, 5);
v___x_1184_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1181_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
v___x_1185_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__6));
v___x_1186_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7, &l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7);
v___x_1187_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1181_);
lean_ctor_set(v___x_1187_, 1, v___x_1185_);
lean_ctor_set(v___x_1187_, 2, v___x_1186_);
v___x_1188_ = l_Array_append___redArg(v___x_1186_, v_a_1175_);
lean_dec(v_a_1175_);
v___x_1189_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1181_);
lean_ctor_set(v___x_1189_, 1, v___x_1185_);
lean_ctor_set(v___x_1189_, 2, v___x_1188_);
v___x_1190_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__8));
v___x_1191_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1181_);
lean_ctor_set(v___x_1191_, 1, v___x_1190_);
v___x_1192_ = l_Lean_Syntax_node2(v___x_1181_, v___x_1185_, v___x_1189_, v___x_1191_);
v___x_1193_ = l_Lean_Syntax_node4(v___x_1181_, v___x_1182_, v___x_1184_, v___x_1187_, v___x_1192_, v_a_1162_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v___x_1193_);
v___x_1195_ = v___x_1177_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v___x_1193_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
else
{
lean_object* v___x_1197_; lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1212_; 
lean_del_object(v___x_1177_);
lean_dec(v_a_1175_);
v___x_1197_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0(v_ref_1163_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
v_a_1198_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1200_ = v___x_1197_;
v_isShared_1201_ = v_isSharedCheck_1212_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1197_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1212_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1210_; 
v___x_1202_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3));
v___x_1203_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__4));
lean_inc_n(v_a_1198_, 2);
v___x_1204_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1204_, 0, v_a_1198_);
lean_ctor_set(v___x_1204_, 1, v___x_1203_);
v___x_1205_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__6));
v___x_1206_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7, &l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7);
v___x_1207_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1207_, 0, v_a_1198_);
lean_ctor_set(v___x_1207_, 1, v___x_1205_);
lean_ctor_set(v___x_1207_, 2, v___x_1206_);
lean_inc_ref(v___x_1207_);
v___x_1208_ = l_Lean_Syntax_node4(v_a_1198_, v___x_1202_, v___x_1204_, v___x_1207_, v___x_1207_, v_a_1162_);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 0, v___x_1208_);
v___x_1210_ = v___x_1200_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1208_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
}
else
{
lean_object* v_a_1214_; lean_object* v___x_1215_; uint8_t v___x_1216_; 
v_a_1214_ = lean_ctor_get(v___x_1173_, 0);
lean_inc(v_a_1214_);
lean_dec_ref(v___x_1173_);
v___x_1215_ = lean_array_get_size(v_a_1214_);
v___x_1216_ = lean_nat_dec_eq(v___x_1215_, v_zero_1159_);
if (v___x_1216_ == 0)
{
lean_object* v___x_1217_; lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1239_; 
v___x_1217_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0(v_ref_1163_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1220_ = v___x_1217_;
v_isShared_1221_ = v_isSharedCheck_1239_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1217_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1239_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1237_; 
v___x_1222_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3));
v___x_1223_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__4));
lean_inc_n(v_a_1218_, 6);
v___x_1224_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1224_, 0, v_a_1218_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
v___x_1225_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__6));
v___x_1226_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__9));
v___x_1227_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1227_, 0, v_a_1218_);
lean_ctor_set(v___x_1227_, 1, v___x_1226_);
v___x_1228_ = l_Lean_Syntax_node1(v_a_1218_, v___x_1225_, v___x_1227_);
v___x_1229_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7, &l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7);
v___x_1230_ = l_Array_append___redArg(v___x_1229_, v_a_1214_);
lean_dec(v_a_1214_);
v___x_1231_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1231_, 0, v_a_1218_);
lean_ctor_set(v___x_1231_, 1, v___x_1225_);
lean_ctor_set(v___x_1231_, 2, v___x_1230_);
v___x_1232_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__8));
v___x_1233_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1233_, 0, v_a_1218_);
lean_ctor_set(v___x_1233_, 1, v___x_1232_);
v___x_1234_ = l_Lean_Syntax_node2(v_a_1218_, v___x_1225_, v___x_1231_, v___x_1233_);
v___x_1235_ = l_Lean_Syntax_node4(v_a_1218_, v___x_1222_, v___x_1224_, v___x_1228_, v___x_1234_, v_a_1162_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 0, v___x_1235_);
v___x_1237_ = v___x_1220_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v___x_1235_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
else
{
lean_object* v___x_1240_; lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1258_; 
lean_dec(v_a_1214_);
v___x_1240_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0(v_ref_1163_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1243_ = v___x_1240_;
v_isShared_1244_ = v_isSharedCheck_1258_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1240_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1258_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1256_; 
v___x_1245_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3));
v___x_1246_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__4));
lean_inc_n(v_a_1241_, 4);
v___x_1247_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1247_, 0, v_a_1241_);
lean_ctor_set(v___x_1247_, 1, v___x_1246_);
v___x_1248_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__6));
v___x_1249_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__9));
v___x_1250_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1250_, 0, v_a_1241_);
lean_ctor_set(v___x_1250_, 1, v___x_1249_);
v___x_1251_ = l_Lean_Syntax_node1(v_a_1241_, v___x_1248_, v___x_1250_);
v___x_1252_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7, &l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7);
v___x_1253_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1253_, 0, v_a_1241_);
lean_ctor_set(v___x_1253_, 1, v___x_1248_);
lean_ctor_set(v___x_1253_, 2, v___x_1252_);
v___x_1254_ = l_Lean_Syntax_node4(v_a_1241_, v___x_1245_, v___x_1247_, v___x_1251_, v___x_1253_, v_a_1162_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 0, v___x_1254_);
v___x_1256_ = v___x_1243_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1254_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
}
else
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
lean_dec(v_a_1162_);
lean_dec_ref(v_measure_1149_);
v_a_1259_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1261_ = v___x_1173_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1173_);
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
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1259_);
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
else
{
lean_dec_ref(v_a_1151_);
lean_dec_ref(v_measure_1149_);
return v___x_1161_;
}
}
else
{
lean_object* v___x_1267_; lean_object* v_a_1268_; uint8_t v___x_1269_; 
v___x_1267_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2___redArg(v_a_1152_);
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1268_);
lean_dec_ref(v___x_1267_);
v___x_1269_ = l_Lean_Expr_isLambda(v_a_1268_);
lean_dec(v_a_1268_);
if (v___x_1269_ == 0)
{
v_a_1150_ = v_zero_1159_;
goto _start;
}
else
{
lean_object* v_one_1271_; lean_object* v_n_1272_; lean_object* v___f_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v_one_1271_ = lean_unsigned_to_nat(1u);
v_n_1272_ = lean_nat_sub(v_a_1150_, v_one_1271_);
v___f_1273_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__1___boxed), 11, 3);
lean_closure_set(v___f_1273_, 0, v_a_1151_);
lean_closure_set(v___f_1273_, 1, v_measure_1149_);
lean_closure_set(v___f_1273_, 2, v_n_1272_);
v___x_1274_ = l_Lean_NameSet_empty;
v___x_1275_ = l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg(v___f_1273_, v_isZero_1160_, v___x_1274_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
return v___x_1275_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__1(lean_object* v_a_1276_, lean_object* v_measure_1277_, lean_object* v_n_1278_, lean_object* v_n_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = lean_array_push(v_a_1276_, v_n_1279_);
v___x_1288_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go(v_measure_1277_, v_n_1278_, v___x_1287_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___boxed(lean_object* v_measure_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go(v_measure_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_);
lean_dec(v_a_1297_);
lean_dec_ref(v_a_1296_);
lean_dec(v_a_1295_);
lean_dec_ref(v_a_1294_);
lean_dec(v_a_1293_);
lean_dec_ref(v_a_1292_);
lean_dec(v_a_1290_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1(lean_object* v_b_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v___x_1308_; 
v___x_1308_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg(v_b_1300_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___boxed(lean_object* v_b_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1(v_b_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter___redArg(lean_object* v_x_1318_, lean_object* v_x_1319_, lean_object* v_h__1_1320_, lean_object* v_h__2_1321_){
_start:
{
lean_object* v_zero_1322_; uint8_t v_isZero_1323_; 
v_zero_1322_ = lean_unsigned_to_nat(0u);
v_isZero_1323_ = lean_nat_dec_eq(v_x_1318_, v_zero_1322_);
if (v_isZero_1323_ == 1)
{
lean_object* v___x_1324_; 
lean_dec(v_h__2_1321_);
v___x_1324_ = lean_apply_1(v_h__1_1320_, v_x_1319_);
return v___x_1324_;
}
else
{
lean_object* v_one_1325_; lean_object* v_n_1326_; lean_object* v___x_1327_; 
lean_dec(v_h__1_1320_);
v_one_1325_ = lean_unsigned_to_nat(1u);
v_n_1326_ = lean_nat_sub(v_x_1318_, v_one_1325_);
v___x_1327_ = lean_apply_2(v_h__2_1321_, v_n_1326_, v_x_1319_);
return v___x_1327_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter___redArg___boxed(lean_object* v_x_1328_, lean_object* v_x_1329_, lean_object* v_h__1_1330_, lean_object* v_h__2_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter___redArg(v_x_1328_, v_x_1329_, v_h__1_1330_, v_h__2_1331_);
lean_dec(v_x_1328_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter(lean_object* v_motive_1333_, lean_object* v_x_1334_, lean_object* v_x_1335_, lean_object* v_h__1_1336_, lean_object* v_h__2_1337_){
_start:
{
lean_object* v_zero_1338_; uint8_t v_isZero_1339_; 
v_zero_1338_ = lean_unsigned_to_nat(0u);
v_isZero_1339_ = lean_nat_dec_eq(v_x_1334_, v_zero_1338_);
if (v_isZero_1339_ == 1)
{
lean_object* v___x_1340_; 
lean_dec(v_h__2_1337_);
v___x_1340_ = lean_apply_1(v_h__1_1336_, v_x_1335_);
return v___x_1340_;
}
else
{
lean_object* v_one_1341_; lean_object* v_n_1342_; lean_object* v___x_1343_; 
lean_dec(v_h__1_1336_);
v_one_1341_ = lean_unsigned_to_nat(1u);
v_n_1342_ = lean_nat_sub(v_x_1334_, v_one_1341_);
v___x_1343_ = lean_apply_2(v_h__2_1337_, v_n_1342_, v_x_1335_);
return v___x_1343_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter___boxed(lean_object* v_motive_1344_, lean_object* v_x_1345_, lean_object* v_x_1346_, lean_object* v_h__1_1347_, lean_object* v_h__2_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter(v_motive_1344_, v_x_1345_, v_x_1346_, v_h__1_1347_, v_h__2_1348_);
lean_dec(v_x_1345_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Array_map__unattach_match__1_splitter___redArg(lean_object* v_x_1350_, lean_object* v_h__1_1351_){
_start:
{
lean_object* v___x_1352_; 
v___x_1352_ = lean_apply_2(v_h__1_1351_, v_x_1350_, lean_box(0));
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Array_map__unattach_match__1_splitter(lean_object* v_00_u03b1_1353_, lean_object* v_P_1354_, lean_object* v_motive_1355_, lean_object* v_x_1356_, lean_object* v_h__1_1357_){
_start:
{
lean_object* v___x_1358_; 
v___x_1358_ = lean_apply_2(v_h__1_1357_, v_x_1356_, lean_box(0));
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___redArg(lean_object* v_e_1359_, lean_object* v_maxFVars_1360_, lean_object* v_k_1361_, uint8_t v_cleanupAnnotations_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v___f_1368_; uint8_t v___x_1369_; uint8_t v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___f_1368_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1368_, 0, v_k_1361_);
v___x_1369_ = 1;
v___x_1370_ = 0;
v___x_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1371_, 0, v_maxFVars_1360_);
v___x_1372_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1359_, v___x_1369_, v___x_1370_, v___x_1369_, v___x_1370_, v___x_1371_, v___f_1368_, v_cleanupAnnotations_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
lean_dec_ref(v___x_1371_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1375_ = v___x_1372_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1372_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1376_ == 0)
{
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_a_1373_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
else
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
v_a_1381_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1383_ = v___x_1372_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1372_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1381_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___redArg___boxed(lean_object* v_e_1389_, lean_object* v_maxFVars_1390_, lean_object* v_k_1391_, lean_object* v_cleanupAnnotations_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1398_; lean_object* v_res_1399_; 
v_cleanupAnnotations_boxed_1398_ = lean_unbox(v_cleanupAnnotations_1392_);
v_res_1399_ = l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___redArg(v_e_1389_, v_maxFVars_1390_, v_k_1391_, v_cleanupAnnotations_boxed_1398_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0(lean_object* v_00_u03b1_1400_, lean_object* v_e_1401_, lean_object* v_maxFVars_1402_, lean_object* v_k_1403_, uint8_t v_cleanupAnnotations_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v___x_1410_; 
v___x_1410_ = l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___redArg(v_e_1401_, v_maxFVars_1402_, v_k_1403_, v_cleanupAnnotations_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___boxed(lean_object* v_00_u03b1_1411_, lean_object* v_e_1412_, lean_object* v_maxFVars_1413_, lean_object* v_k_1414_, lean_object* v_cleanupAnnotations_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1421_; lean_object* v_res_1422_; 
v_cleanupAnnotations_boxed_1421_ = lean_unbox(v_cleanupAnnotations_1415_);
v_res_1422_ = l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0(v_00_u03b1_1411_, v_e_1412_, v_maxFVars_1413_, v_k_1414_, v_cleanupAnnotations_boxed_1421_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_delab___lam__0(lean_object* v_measure_1425_, lean_object* v_extraParams_1426_, lean_object* v___ys_1427_, lean_object* v_e_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1434_ = lean_box(1);
v___x_1435_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_delab___lam__0___closed__0));
v___x_1436_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___boxed), 10, 3);
lean_closure_set(v___x_1436_, 0, v_measure_1425_);
lean_closure_set(v___x_1436_, 1, v_extraParams_1426_);
lean_closure_set(v___x_1436_, 2, v___x_1435_);
v___x_1437_ = l_Lean_PrettyPrinter_delabCore___redArg(v_e_1428_, v___x_1434_, v___x_1436_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1446_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1440_ = v___x_1437_;
v_isShared_1441_ = v_isSharedCheck_1446_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1437_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1446_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v_fst_1442_; lean_object* v___x_1444_; 
v_fst_1442_ = lean_ctor_get(v_a_1438_, 0);
lean_inc(v_fst_1442_);
lean_dec(v_a_1438_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 0, v_fst_1442_);
v___x_1444_ = v___x_1440_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_fst_1442_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
v_a_1447_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1437_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1437_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_delab___lam__0___boxed(lean_object* v_measure_1455_, lean_object* v_extraParams_1456_, lean_object* v___ys_1457_, lean_object* v_e_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l_Lean_Elab_TerminationMeasure_delab___lam__0(v_measure_1455_, v_extraParams_1456_, v___ys_1457_, v_e_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec_ref(v___ys_1457_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_delab(lean_object* v_arity_1465_, lean_object* v_extraParams_1466_, lean_object* v_measure_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_){
_start:
{
lean_object* v_fn_1473_; lean_object* v___f_1474_; lean_object* v___x_1475_; uint8_t v___x_1476_; lean_object* v___x_1477_; 
v_fn_1473_ = lean_ctor_get(v_measure_1467_, 1);
lean_inc_ref(v_fn_1473_);
lean_inc(v_extraParams_1466_);
v___f_1474_ = lean_alloc_closure((void*)(l_Lean_Elab_TerminationMeasure_delab___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1474_, 0, v_measure_1467_);
lean_closure_set(v___f_1474_, 1, v_extraParams_1466_);
v___x_1475_ = lean_nat_sub(v_arity_1465_, v_extraParams_1466_);
lean_dec(v_extraParams_1466_);
v___x_1476_ = 0;
v___x_1477_ = l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___redArg(v_fn_1473_, v___x_1475_, v___f_1474_, v___x_1476_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_delab___boxed(lean_object* v_arity_1478_, lean_object* v_extraParams_1479_, lean_object* v_measure_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Lean_Elab_TerminationMeasure_delab(v_arity_1478_, v_extraParams_1479_, v_measure_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_);
lean_dec(v_a_1484_);
lean_dec_ref(v_a_1483_);
lean_dec(v_a_1482_);
lean_dec_ref(v_a_1481_);
lean_dec(v_arity_1478_);
return v_res_1486_;
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
