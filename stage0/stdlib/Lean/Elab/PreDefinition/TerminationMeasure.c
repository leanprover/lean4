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
lean_object* v___x_169_; lean_object* v___x_3437__overap_170_; lean_object* v___x_171_; 
v___x_169_ = lean_obj_once(&l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6___closed__0, &l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6___closed__0_once, _init_l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6___closed__0);
v___x_3437__overap_170_ = lean_panic_fn_borrowed(v___x_169_, v_msg_161_);
lean_inc(v___y_167_);
lean_inc_ref(v___y_166_);
lean_inc(v___y_165_);
lean_inc_ref(v___y_164_);
lean_inc(v___y_163_);
lean_inc_ref(v___y_162_);
v___x_171_ = lean_apply_7(v___x_3437__overap_170_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, lean_box(0));
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
uint8_t v___x_5771__boxed_212_; lean_object* v_res_213_; 
v___x_5771__boxed_212_ = lean_unbox(v___x_202_);
v_res_213_ = l_Lean_Elab_TerminationMeasure_elab___lam__0(v_ys_199_, v_xs_200_, v_a_201_, v___x_5771__boxed_212_, v_zs_203_, v_x_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_);
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
v___x_332_ = l_Lean_Elab_getBetterRef(v_ref_328_, v_macroStack_331_);
lean_inc(v_macroStack_331_);
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
lean_dec_ref_known(v___x_378_, 14);
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
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__1(lean_object* v_body_465_, uint8_t v___x_466_, lean_object* v_ys_467_, lean_object* v_vars_468_, lean_object* v_extraParams_469_, uint8_t v_structural_470_, lean_object* v_ref_471_, lean_object* v_xs_472_, lean_object* v_type_x27_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; uint8_t v___x_485_; lean_object* v___x_486_; 
v___x_481_ = lean_box(0);
v___x_482_ = lean_box(v___x_466_);
v___x_483_ = lean_box(v___x_466_);
v___x_484_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_484_, 0, v_body_465_);
lean_closure_set(v___x_484_, 1, v___x_481_);
lean_closure_set(v___x_484_, 2, v___x_482_);
lean_closure_set(v___x_484_, 3, v___x_483_);
lean_closure_set(v___x_484_, 4, v___x_481_);
v___x_485_ = 1;
v___x_486_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_484_, v___x_485_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
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
v___x_491_ = lean_box(v___x_466_);
lean_inc(v_a_487_);
lean_inc_ref(v_xs_472_);
lean_inc_ref(v_ys_467_);
v___f_492_ = lean_alloc_closure((void*)(l_Lean_Elab_TerminationMeasure_elab___lam__0___boxed), 13, 4);
lean_closure_set(v___f_492_, 0, v_ys_467_);
lean_closure_set(v___f_492_, 1, v_xs_472_);
lean_closure_set(v___f_492_, 2, v_a_487_);
lean_closure_set(v___f_492_, 3, v___x_491_);
if (v_structural_470_ == 0)
{
lean_dec(v_a_487_);
lean_dec_ref(v_xs_472_);
lean_dec_ref(v_ys_467_);
v___y_509_ = v___y_474_;
v___y_510_ = v___y_475_;
v___y_511_ = v___y_476_;
v___y_512_ = v___y_477_;
v___y_513_ = v___y_478_;
v___y_514_ = v___y_479_;
goto v___jp_508_;
}
else
{
lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_518_ = l_Array_append___redArg(v_ys_467_, v_xs_472_);
lean_dec_ref(v_xs_472_);
v___x_519_ = l_Array_contains___at___00Lean_Elab_TerminationMeasure_elab_spec__2(v___x_518_, v_a_487_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
lean_dec_ref(v___f_492_);
lean_del_object(v___x_489_);
lean_dec(v_type_x27_473_);
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
v___x_536_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___redArg(v_ref_471_, v___x_535_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
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
v___y_509_ = v___y_474_;
v___y_510_ = v___y_475_;
v___y_511_ = v___y_476_;
v___y_512_ = v___y_477_;
v___y_513_ = v___y_478_;
v___y_514_ = v___y_479_;
goto v___jp_508_;
}
}
v___jp_493_:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_504_; 
v___x_501_ = lean_array_get_size(v_vars_468_);
v___x_502_ = lean_nat_sub(v_extraParams_469_, v___x_501_);
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
v___x_506_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___redArg(v___y_500_, v___x_504_, v___f_492_, v___x_505_, v___x_505_, v___y_498_, v___y_497_, v___y_495_, v___y_496_, v___y_494_, v___y_499_);
return v___x_506_;
}
}
v___jp_508_:
{
if (lean_obj_tag(v_type_x27_473_) == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__3, &l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__3_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__1___closed__3);
v___x_516_ = l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__1(v___x_515_);
v___y_494_ = v___y_513_;
v___y_495_ = v___y_511_;
v___y_496_ = v___y_512_;
v___y_497_ = v___y_510_;
v___y_498_ = v___y_509_;
v___y_499_ = v___y_514_;
v___y_500_ = v___x_516_;
goto v___jp_493_;
}
else
{
lean_object* v_val_517_; 
v_val_517_ = lean_ctor_get(v_type_x27_473_, 0);
lean_inc(v_val_517_);
lean_dec_ref_known(v_type_x27_473_, 1);
v___y_494_ = v___y_513_;
v___y_495_ = v___y_511_;
v___y_496_ = v___y_512_;
v___y_497_ = v___y_510_;
v___y_498_ = v___y_509_;
v___y_499_ = v___y_514_;
v___y_500_ = v_val_517_;
goto v___jp_493_;
}
}
}
}
else
{
lean_dec(v_type_x27_473_);
lean_dec_ref(v_xs_472_);
lean_dec_ref(v_ys_467_);
return v___x_486_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__1___boxed(lean_object* v_body_546_, lean_object* v___x_547_, lean_object* v_ys_548_, lean_object* v_vars_549_, lean_object* v_extraParams_550_, lean_object* v_structural_551_, lean_object* v_ref_552_, lean_object* v_xs_553_, lean_object* v_type_x27_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
uint8_t v___x_6170__boxed_562_; uint8_t v_structural_boxed_563_; lean_object* v_res_564_; 
v___x_6170__boxed_562_ = lean_unbox(v___x_547_);
v_structural_boxed_563_ = lean_unbox(v_structural_551_);
v_res_564_ = l_Lean_Elab_TerminationMeasure_elab___lam__1(v_body_546_, v___x_6170__boxed_562_, v_ys_548_, v_vars_549_, v_extraParams_550_, v_structural_boxed_563_, v_ref_552_, v_xs_553_, v_type_x27_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v_ref_552_);
lean_dec(v_extraParams_550_);
lean_dec_ref(v_vars_549_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__2(lean_object* v_hint_565_, uint8_t v___x_566_, lean_object* v_extraParams_567_, lean_object* v_ys_568_, lean_object* v_type_x27_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
lean_object* v_ref_577_; uint8_t v_structural_578_; lean_object* v_vars_579_; lean_object* v_body_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___f_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v_ref_577_ = lean_ctor_get(v_hint_565_, 0);
lean_inc(v_ref_577_);
v_structural_578_ = lean_ctor_get_uint8(v_hint_565_, sizeof(void*)*3);
v_vars_579_ = lean_ctor_get(v_hint_565_, 1);
lean_inc_ref_n(v_vars_579_, 2);
v_body_580_ = lean_ctor_get(v_hint_565_, 2);
lean_inc(v_body_580_);
lean_dec_ref(v_hint_565_);
v___x_581_ = lean_box(v___x_566_);
v___x_582_ = lean_box(v_structural_578_);
v___f_583_ = lean_alloc_closure((void*)(l_Lean_Elab_TerminationMeasure_elab___lam__1___boxed), 16, 7);
lean_closure_set(v___f_583_, 0, v_body_580_);
lean_closure_set(v___f_583_, 1, v___x_581_);
lean_closure_set(v___f_583_, 2, v_ys_568_);
lean_closure_set(v___f_583_, 3, v_vars_579_);
lean_closure_set(v___f_583_, 4, v_extraParams_567_);
lean_closure_set(v___f_583_, 5, v___x_582_);
lean_closure_set(v___f_583_, 6, v_ref_577_);
v___x_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_584_, 0, v_type_x27_569_);
v___x_585_ = l_Lean_Elab_Term_elabFunBinders___redArg(v_vars_579_, v___x_584_, v___f_583_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
lean_dec_ref(v_vars_579_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__2___boxed(lean_object* v_hint_586_, lean_object* v___x_587_, lean_object* v_extraParams_588_, lean_object* v_ys_589_, lean_object* v_type_x27_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
uint8_t v___x_6350__boxed_598_; lean_object* v_res_599_; 
v___x_6350__boxed_598_ = lean_unbox(v___x_587_);
v_res_599_ = l_Lean_Elab_TerminationMeasure_elab___lam__2(v_hint_586_, v___x_6350__boxed_598_, v_extraParams_588_, v_ys_589_, v_type_x27_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
return v_res_599_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__3(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_603_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__2));
v___x_604_ = lean_unsigned_to_nat(2u);
v___x_605_ = lean_unsigned_to_nat(54u);
v___x_606_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__1));
v___x_607_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__0));
v___x_608_ = l_mkPanicMessageWithDecl(v___x_607_, v___x_606_, v___x_605_, v___x_604_, v___x_603_);
return v___x_608_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__5(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__4));
v___x_611_ = l_Lean_stringToMessageData(v___x_610_);
return v___x_611_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__7(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__6));
v___x_614_ = l_Lean_stringToMessageData(v___x_613_);
return v___x_614_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__9(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__8));
v___x_617_ = l_Lean_stringToMessageData(v___x_616_);
return v___x_617_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__13(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__12));
v___x_623_ = l_Lean_stringToMessageData(v___x_622_);
return v___x_623_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__16(void){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__15));
v___x_628_ = l_Lean_MessageData_ofFormat(v___x_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__3(uint8_t v___x_629_, lean_object* v_hint_630_, lean_object* v_arity_631_, lean_object* v_extraParams_632_, lean_object* v_type_633_, lean_object* v___f_634_, lean_object* v_funName_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
if (v___x_629_ == 0)
{
lean_object* v___x_643_; lean_object* v___x_644_; 
lean_dec(v_funName_635_);
lean_dec_ref(v___f_634_);
lean_dec_ref(v_type_633_);
lean_dec(v_extraParams_632_);
v___x_643_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__3, &l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__3_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__3);
v___x_644_ = l_panic___at___00Lean_Elab_TerminationMeasure_elab_spec__6(v___x_643_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
return v___x_644_;
}
else
{
lean_object* v_ref_645_; uint8_t v_structural_646_; lean_object* v_vars_647_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v_msg_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___x_707_; uint8_t v___x_708_; 
v_ref_645_ = lean_ctor_get(v_hint_630_, 0);
v_structural_646_ = lean_ctor_get_uint8(v_hint_630_, sizeof(void*)*3);
v_vars_647_ = lean_ctor_get(v_hint_630_, 1);
v___x_707_ = lean_array_get_size(v_vars_647_);
v___x_708_ = lean_nat_dec_lt(v_extraParams_632_, v___x_707_);
if (v___x_708_ == 0)
{
lean_dec(v_funName_635_);
v___y_649_ = v___y_636_;
v___y_650_ = v___y_637_;
v___y_651_ = v___y_638_;
v___y_652_ = v___y_639_;
v___y_653_ = v___y_640_;
v___y_654_ = v___y_641_;
goto v___jp_648_;
}
else
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v_msg_719_; lean_object* v___x_720_; lean_object* v_ident_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
lean_dec_ref(v___f_634_);
lean_dec_ref(v_type_633_);
v___x_709_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters(v___x_707_);
v___x_710_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__5, &l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__5_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__5);
v___x_711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_709_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
lean_inc(v_funName_635_);
v___x_712_ = l_Lean_MessageData_ofName(v_funName_635_);
v___x_713_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__7, &l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__7_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__7);
v___x_714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_712_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
v___x_715_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_elab_parameters(v_extraParams_632_);
v___x_716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_716_, 0, v___x_714_);
lean_ctor_set(v___x_716_, 1, v___x_715_);
v___x_717_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__9, &l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__9_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__9);
v___x_718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_716_);
lean_ctor_set(v___x_718_, 1, v___x_717_);
v_msg_719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_719_, 0, v___x_711_);
lean_ctor_set(v_msg_719_, 1, v___x_718_);
v___x_720_ = lean_unsigned_to_nat(0u);
v_ident_721_ = lean_array_fget_borrowed(v_vars_647_, v___x_720_);
v___x_722_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__11));
lean_inc(v_ident_721_);
v___x_723_ = l_Lean_Syntax_isOfKind(v_ident_721_, v___x_722_);
if (v___x_723_ == 0)
{
lean_dec(v_funName_635_);
v_msg_691_ = v_msg_719_;
v___y_692_ = v___y_636_;
v___y_693_ = v___y_637_;
v___y_694_ = v___y_638_;
v___y_695_ = v___y_639_;
v___y_696_ = v___y_640_;
v___y_697_ = v___y_641_;
goto v___jp_690_;
}
else
{
lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_724_ = l_Lean_TSyntax_getId(v_ident_721_);
v___x_725_ = l_Lean_Name_isSuffixOf(v___x_724_, v_funName_635_);
lean_dec(v_funName_635_);
lean_dec(v___x_724_);
if (v___x_725_ == 0)
{
v_msg_691_ = v_msg_719_;
v___y_692_ = v___y_636_;
v___y_693_ = v___y_637_;
v___y_694_ = v___y_638_;
v___y_695_ = v___y_639_;
v___y_696_ = v___y_640_;
v___y_697_ = v___y_641_;
goto v___jp_690_;
}
else
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v_msg_729_; 
v___x_726_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__13, &l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__13_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__13);
v___x_727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_727_, 0, v_msg_719_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
v___x_728_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__16, &l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__16_once, _init_l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__16);
v_msg_729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_729_, 0, v___x_727_);
lean_ctor_set(v_msg_729_, 1, v___x_728_);
v_msg_691_ = v_msg_729_;
v___y_692_ = v___y_636_;
v___y_693_ = v___y_637_;
v___y_694_ = v___y_638_;
v___y_695_ = v___y_639_;
v___y_696_ = v___y_640_;
v___y_697_ = v___y_641_;
goto v___jp_690_;
}
}
}
v___jp_648_:
{
lean_object* v___x_655_; lean_object* v___x_656_; uint8_t v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_655_ = lean_nat_sub(v_arity_631_, v_extraParams_632_);
lean_dec(v_extraParams_632_);
v___x_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
v___x_657_ = 0;
v___x_658_ = lean_box(v___x_629_);
v___x_659_ = lean_box(v___x_657_);
v___x_660_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_TerminationMeasure_elab_spec__0___boxed), 13, 6);
lean_closure_set(v___x_660_, 0, lean_box(0));
lean_closure_set(v___x_660_, 1, v_type_633_);
lean_closure_set(v___x_660_, 2, v___x_656_);
lean_closure_set(v___x_660_, 3, v___f_634_);
lean_closure_set(v___x_660_, 4, v___x_658_);
lean_closure_set(v___x_660_, 5, v___x_659_);
v___x_661_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_660_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; uint8_t v___x_663_; lean_object* v___x_664_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc_n(v_a_662_, 2);
lean_dec_ref_known(v___x_661_, 1);
v___x_663_ = 0;
v___x_664_ = l_Lean_Meta_check(v_a_662_, v___x_663_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_672_; 
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_672_ == 0)
{
lean_object* v_unused_673_; 
v_unused_673_ = lean_ctor_get(v___x_664_, 0);
lean_dec(v_unused_673_);
v___x_666_ = v___x_664_;
v_isShared_667_ = v_isSharedCheck_672_;
goto v_resetjp_665_;
}
else
{
lean_dec(v___x_664_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_672_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_668_; lean_object* v___x_670_; 
lean_inc(v_ref_645_);
v___x_668_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_668_, 0, v_ref_645_);
lean_ctor_set(v___x_668_, 1, v_a_662_);
lean_ctor_set_uint8(v___x_668_, sizeof(void*)*2, v_structural_646_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_668_);
v___x_670_ = v___x_666_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_668_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
else
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
lean_dec(v_a_662_);
v_a_674_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___x_664_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_664_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_a_674_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
else
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
v_a_682_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_661_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_661_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
v___jp_690_:
{
lean_object* v___x_698_; lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
v___x_698_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___redArg(v_ref_645_, v_msg_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
v_a_699_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_698_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_698_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_a_699_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___lam__3___boxed(lean_object* v___x_730_, lean_object* v_hint_731_, lean_object* v_arity_732_, lean_object* v_extraParams_733_, lean_object* v_type_734_, lean_object* v___f_735_, lean_object* v_funName_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
uint8_t v___x_6442__boxed_744_; lean_object* v_res_745_; 
v___x_6442__boxed_744_ = lean_unbox(v___x_730_);
v_res_745_ = l_Lean_Elab_TerminationMeasure_elab___lam__3(v___x_6442__boxed_744_, v_hint_731_, v_arity_732_, v_extraParams_733_, v_type_734_, v___f_735_, v_funName_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v_arity_732_);
lean_dec_ref(v_hint_731_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab(lean_object* v_funName_746_, lean_object* v_type_747_, lean_object* v_arity_748_, lean_object* v_extraParams_749_, lean_object* v_hint_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_){
_start:
{
uint8_t v___x_758_; lean_object* v___x_759_; lean_object* v___f_760_; lean_object* v___x_761_; lean_object* v___y_762_; lean_object* v___x_763_; 
v___x_758_ = lean_nat_dec_le(v_extraParams_749_, v_arity_748_);
v___x_759_ = lean_box(v___x_758_);
lean_inc(v_extraParams_749_);
lean_inc_ref(v_hint_750_);
v___f_760_ = lean_alloc_closure((void*)(l_Lean_Elab_TerminationMeasure_elab___lam__2___boxed), 12, 3);
lean_closure_set(v___f_760_, 0, v_hint_750_);
lean_closure_set(v___f_760_, 1, v___x_759_);
lean_closure_set(v___f_760_, 2, v_extraParams_749_);
v___x_761_ = lean_box(v___x_758_);
lean_inc(v_funName_746_);
v___y_762_ = lean_alloc_closure((void*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___boxed), 14, 7);
lean_closure_set(v___y_762_, 0, v___x_761_);
lean_closure_set(v___y_762_, 1, v_hint_750_);
lean_closure_set(v___y_762_, 2, v_arity_748_);
lean_closure_set(v___y_762_, 3, v_extraParams_749_);
lean_closure_set(v___y_762_, 4, v_type_747_);
lean_closure_set(v___y_762_, 5, v___f_760_);
lean_closure_set(v___y_762_, 6, v_funName_746_);
v___x_763_ = l_Lean_Elab_Term_withDeclName___redArg(v_funName_746_, v___y_762_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_elab___boxed(lean_object* v_funName_764_, lean_object* v_type_765_, lean_object* v_arity_766_, lean_object* v_extraParams_767_, lean_object* v_hint_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Lean_Elab_TerminationMeasure_elab(v_funName_764_, v_type_765_, v_arity_766_, v_extraParams_767_, v_hint_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_);
lean_dec(v_a_774_);
lean_dec_ref(v_a_773_);
lean_dec(v_a_772_);
lean_dec_ref(v_a_771_);
lean_dec(v_a_770_);
lean_dec_ref(v_a_769_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4(lean_object* v_00_u03b1_777_, lean_object* v_ref_778_, lean_object* v_msg_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___redArg(v_ref_778_, v_msg_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4___boxed(lean_object* v_00_u03b1_788_, lean_object* v_ref_789_, lean_object* v_msg_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4(v_00_u03b1_788_, v_ref_789_, v_msg_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v_ref_789_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5(lean_object* v_00_u03b1_799_, lean_object* v_msg_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5___redArg(v_msg_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5___boxed(lean_object* v_00_u03b1_809_, lean_object* v_msg_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5(v_00_u03b1_809_, v_msg_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9(lean_object* v_msgData_819_, lean_object* v_macroStack_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___redArg(v_msgData_819_, v_macroStack_820_, v___y_825_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9___boxed(lean_object* v_msgData_829_, lean_object* v_macroStack_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationMeasure_elab_spec__4_spec__5_spec__9(v_msgData_829_, v_macroStack_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1(lean_object* v_msg_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v___f_846_; lean_object* v___x_288__overap_847_; lean_object* v___x_848_; 
v___f_846_ = ((lean_object*)(l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1___closed__0));
v___x_288__overap_847_ = lean_panic_fn_borrowed(v___f_846_, v_msg_840_);
lean_inc(v___y_844_);
lean_inc_ref(v___y_843_);
lean_inc(v___y_842_);
lean_inc_ref(v___y_841_);
v___x_848_ = lean_apply_5(v___x_288__overap_847_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, lean_box(0));
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1___boxed(lean_object* v_msg_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1(v_msg_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg___lam__0(lean_object* v_k_856_, lean_object* v_b_857_, lean_object* v_c_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v___x_864_; 
lean_inc(v___y_862_);
lean_inc_ref(v___y_861_);
lean_inc(v___y_860_);
lean_inc_ref(v___y_859_);
v___x_864_ = lean_apply_7(v_k_856_, v_b_857_, v_c_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, lean_box(0));
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg___lam__0___boxed(lean_object* v_k_865_, lean_object* v_b_866_, lean_object* v_c_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg___lam__0(v_k_865_, v_b_866_, v_c_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg(lean_object* v_e_874_, lean_object* v_k_875_, uint8_t v_cleanupAnnotations_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v___f_882_; uint8_t v___x_883_; uint8_t v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v___f_882_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_882_, 0, v_k_875_);
v___x_883_ = 1;
v___x_884_ = 0;
v___x_885_ = lean_box(0);
v___x_886_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_874_, v___x_883_, v___x_884_, v___x_883_, v___x_884_, v___x_885_, v___f_882_, v_cleanupAnnotations_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_894_; 
v_a_887_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_894_ == 0)
{
v___x_889_ = v___x_886_;
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_886_);
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
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
v_a_895_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_886_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_886_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg___boxed(lean_object* v_e_903_, lean_object* v_k_904_, lean_object* v_cleanupAnnotations_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_911_; lean_object* v_res_912_; 
v_cleanupAnnotations_boxed_911_ = lean_unbox(v_cleanupAnnotations_905_);
v_res_912_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg(v_e_903_, v_k_904_, v_cleanupAnnotations_boxed_911_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2(lean_object* v_00_u03b1_913_, lean_object* v_e_914_, lean_object* v_k_915_, uint8_t v_cleanupAnnotations_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg(v_e_914_, v_k_915_, v_cleanupAnnotations_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___boxed(lean_object* v_00_u03b1_923_, lean_object* v_e_924_, lean_object* v_k_925_, lean_object* v_cleanupAnnotations_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_932_; lean_object* v_res_933_; 
v_cleanupAnnotations_boxed_932_ = lean_unbox(v_cleanupAnnotations_926_);
v_res_933_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2(v_00_u03b1_923_, v_e_924_, v_k_925_, v_cleanupAnnotations_boxed_932_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0_spec__3(lean_object* v_xs_934_, lean_object* v_v_935_, lean_object* v_i_936_){
_start:
{
lean_object* v___x_937_; uint8_t v___x_938_; 
v___x_937_ = lean_array_get_size(v_xs_934_);
v___x_938_ = lean_nat_dec_lt(v_i_936_, v___x_937_);
if (v___x_938_ == 0)
{
lean_object* v___x_939_; 
lean_dec(v_i_936_);
v___x_939_ = lean_box(0);
return v___x_939_;
}
else
{
lean_object* v___x_940_; uint8_t v___x_941_; 
v___x_940_ = lean_array_fget_borrowed(v_xs_934_, v_i_936_);
v___x_941_ = lean_expr_eqv(v___x_940_, v_v_935_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = lean_unsigned_to_nat(1u);
v___x_943_ = lean_nat_add(v_i_936_, v___x_942_);
lean_dec(v_i_936_);
v_i_936_ = v___x_943_;
goto _start;
}
else
{
lean_object* v___x_945_; 
v___x_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_945_, 0, v_i_936_);
return v___x_945_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0_spec__3___boxed(lean_object* v_xs_946_, lean_object* v_v_947_, lean_object* v_i_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0_spec__3(v_xs_946_, v_v_947_, v_i_948_);
lean_dec_ref(v_v_947_);
lean_dec_ref(v_xs_946_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0(lean_object* v_xs_950_, lean_object* v_v_951_){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = lean_unsigned_to_nat(0u);
v___x_953_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0_spec__3(v_xs_950_, v_v_951_, v___x_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0___boxed(lean_object* v_xs_954_, lean_object* v_v_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0(v_xs_954_, v_v_955_);
lean_dec_ref(v_v_955_);
lean_dec_ref(v_xs_954_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0(lean_object* v_xs_957_, lean_object* v_v_958_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0_spec__0(v_xs_957_, v_v_958_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v___x_960_; 
v___x_960_ = lean_box(0);
return v___x_960_;
}
else
{
lean_object* v_val_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_968_; 
v_val_961_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_968_ == 0)
{
v___x_963_ = v___x_959_;
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_val_961_);
lean_dec(v___x_959_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_964_ == 0)
{
v___x_966_ = v___x_963_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_val_961_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0___boxed(lean_object* v_xs_969_, lean_object* v_v_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0(v_xs_969_, v_v_970_);
lean_dec_ref(v_v_970_);
lean_dec_ref(v_xs_969_);
return v_res_971_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_974_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__1));
v___x_975_ = lean_unsigned_to_nat(8u);
v___x_976_ = lean_unsigned_to_nat(93u);
v___x_977_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__0));
v___x_978_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__0));
v___x_979_ = l_mkPanicMessageWithDecl(v___x_978_, v___x_977_, v___x_976_, v___x_975_, v___x_974_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_structuralArg___lam__0(lean_object* v_ys_980_, lean_object* v_e_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_Array_idxOf_x3f___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__0(v_ys_980_, v_e_981_);
if (lean_obj_tag(v___x_987_) == 1)
{
lean_object* v_val_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
v_val_988_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_987_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_val_988_);
lean_dec(v___x_987_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
lean_ctor_set_tag(v___x_990_, 0);
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_val_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
else
{
lean_object* v___x_996_; lean_object* v___x_997_; 
lean_dec(v___x_987_);
v___x_996_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__2, &l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__2_once, _init_l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__2);
v___x_997_ = l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1(v___x_996_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
return v___x_997_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___boxed(lean_object* v_ys_998_, lean_object* v_e_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Lean_Elab_TerminationMeasure_structuralArg___lam__0(v_ys_998_, v_e_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec_ref(v_e_999_);
lean_dec_ref(v_ys_998_);
return v_res_1005_;
}
}
static lean_object* _init_l_Lean_Elab_TerminationMeasure_structuralArg___closed__1(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1007_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_structuralArg___closed__0));
v___x_1008_ = lean_unsigned_to_nat(2u);
v___x_1009_ = lean_unsigned_to_nat(90u);
v___x_1010_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_structuralArg___lam__0___closed__0));
v___x_1011_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_elab___lam__3___closed__0));
v___x_1012_ = l_mkPanicMessageWithDecl(v___x_1011_, v___x_1010_, v___x_1009_, v___x_1008_, v___x_1007_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_structuralArg(lean_object* v_measure_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_){
_start:
{
uint8_t v_structural_1020_; 
v_structural_1020_ = lean_ctor_get_uint8(v_measure_1014_, sizeof(void*)*2);
if (v_structural_1020_ == 0)
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
lean_dec_ref(v_measure_1014_);
v___x_1021_ = lean_obj_once(&l_Lean_Elab_TerminationMeasure_structuralArg___closed__1, &l_Lean_Elab_TerminationMeasure_structuralArg___closed__1_once, _init_l_Lean_Elab_TerminationMeasure_structuralArg___closed__1);
v___x_1022_ = l_panic___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__1(v___x_1021_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
return v___x_1022_;
}
else
{
lean_object* v_fn_1023_; lean_object* v___f_1024_; uint8_t v___x_1025_; lean_object* v___x_1026_; 
v_fn_1023_ = lean_ctor_get(v_measure_1014_, 1);
lean_inc_ref(v_fn_1023_);
lean_dec_ref(v_measure_1014_);
v___f_1024_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_structuralArg___closed__2));
v___x_1025_ = 0;
v___x_1026_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg(v_fn_1023_, v___f_1024_, v___x_1025_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
return v___x_1026_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_structuralArg___boxed(lean_object* v_measure_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Lean_Elab_TerminationMeasure_structuralArg(v_measure_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_);
lean_dec(v_a_1031_);
lean_dec_ref(v_a_1030_);
lean_dec(v_a_1029_);
lean_dec_ref(v_a_1028_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2___redArg(lean_object* v___y_1034_){
_start:
{
lean_object* v_subExpr_1036_; lean_object* v_expr_1037_; lean_object* v___x_1038_; 
v_subExpr_1036_ = lean_ctor_get(v___y_1034_, 3);
v_expr_1037_ = lean_ctor_get(v_subExpr_1036_, 0);
lean_inc_ref(v_expr_1037_);
v___x_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1038_, 0, v_expr_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2___redArg___boxed(lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2___redArg(v___y_1039_);
lean_dec_ref(v___y_1039_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2(lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2___redArg(v___y_1042_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2___boxed(lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2(v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0(lean_object* v_____do__lift_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
uint8_t v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1066_ = 0;
v___x_1067_ = l_Lean_SourceInfo_fromRef(v_____do__lift_1058_, v___x_1066_);
v___x_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0___boxed(lean_object* v_____do__lift_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0(v_____do__lift_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v_____do__lift_1069_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg(lean_object* v_a_1087_){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; uint8_t v___x_1091_; 
v___x_1089_ = lean_array_get_size(v_a_1087_);
v___x_1090_ = lean_unsigned_to_nat(0u);
v___x_1091_ = lean_nat_dec_eq(v___x_1089_, v___x_1090_);
if (v___x_1091_ == 0)
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; uint8_t v___x_1097_; 
v___x_1092_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4));
v___x_1093_ = lean_box(0);
v___x_1094_ = lean_unsigned_to_nat(1u);
v___x_1095_ = lean_nat_sub(v___x_1089_, v___x_1094_);
v___x_1096_ = lean_array_get_borrowed(v___x_1093_, v_a_1087_, v___x_1095_);
lean_dec(v___x_1095_);
lean_inc(v___x_1096_);
v___x_1097_ = l_Lean_Syntax_isOfKind(v___x_1096_, v___x_1092_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; 
v___x_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1098_, 0, v_a_1087_);
return v___x_1098_;
}
else
{
lean_object* v___x_1099_; 
v___x_1099_ = lean_array_pop(v_a_1087_);
v_a_1087_ = v___x_1099_;
goto _start;
}
}
else
{
lean_object* v___x_1101_; 
v___x_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1101_, 0, v_a_1087_);
return v___x_1101_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___boxed(lean_object* v_a_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg(v_a_1102_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__0(lean_object* v_a_1105_, lean_object* v___x_1106_, size_t v_sz_1107_, size_t v_i_1108_, lean_object* v_bs_1109_){
_start:
{
uint8_t v___x_1110_; 
v___x_1110_ = lean_usize_dec_lt(v_i_1108_, v_sz_1107_);
if (v___x_1110_ == 0)
{
lean_dec(v___x_1106_);
return v_bs_1109_;
}
else
{
lean_object* v_v_1111_; lean_object* v___x_1112_; lean_object* v_bs_x27_1113_; lean_object* v___y_1115_; lean_object* v___x_1120_; uint8_t v___x_1121_; 
v_v_1111_ = lean_array_uget(v_bs_1109_, v_i_1108_);
v___x_1112_ = lean_unsigned_to_nat(0u);
v_bs_x27_1113_ = lean_array_uset(v_bs_1109_, v_i_1108_, v___x_1112_);
v___x_1120_ = l_Lean_TSyntax_getId(v_v_1111_);
v___x_1121_ = l_Lean_Syntax_hasIdent(v___x_1120_, v_a_1105_);
lean_dec(v___x_1120_);
if (v___x_1121_ == 0)
{
lean_dec(v_v_1111_);
lean_inc(v___x_1106_);
v___y_1115_ = v___x_1106_;
goto v___jp_1114_;
}
else
{
v___y_1115_ = v_v_1111_;
goto v___jp_1114_;
}
v___jp_1114_:
{
size_t v___x_1116_; size_t v___x_1117_; lean_object* v___x_1118_; 
v___x_1116_ = ((size_t)1ULL);
v___x_1117_ = lean_usize_add(v_i_1108_, v___x_1116_);
v___x_1118_ = lean_array_uset(v_bs_x27_1113_, v_i_1108_, v___y_1115_);
v_i_1108_ = v___x_1117_;
v_bs_1109_ = v___x_1118_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__0___boxed(lean_object* v_a_1122_, lean_object* v___x_1123_, lean_object* v_sz_1124_, lean_object* v_i_1125_, lean_object* v_bs_1126_){
_start:
{
size_t v_sz_boxed_1127_; size_t v_i_boxed_1128_; lean_object* v_res_1129_; 
v_sz_boxed_1127_ = lean_unbox_usize(v_sz_1124_);
lean_dec(v_sz_1124_);
v_i_boxed_1128_ = lean_unbox_usize(v_i_1125_);
lean_dec(v_i_1125_);
v_res_1129_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__0(v_a_1122_, v___x_1123_, v_sz_boxed_1127_, v_i_boxed_1128_, v_bs_1126_);
lean_dec(v_a_1122_);
return v_res_1129_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7(void){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = l_Array_mkArray0(lean_box(0));
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__1___boxed(lean_object* v_a_1145_, lean_object* v_measure_1146_, lean_object* v_n_1147_, lean_object* v_n_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__1(v_a_1145_, v_measure_1146_, v_n_1147_, v_n_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec(v_n_1147_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go(lean_object* v_measure_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_){
_start:
{
lean_object* v_zero_1167_; uint8_t v_isZero_1168_; 
v_zero_1167_ = lean_unsigned_to_nat(0u);
v_isZero_1168_ = lean_nat_dec_eq(v_a_1158_, v_zero_1167_);
if (v_isZero_1168_ == 1)
{
lean_object* v___x_1169_; 
v___x_1169_ = l_Lean_PrettyPrinter_Delaborator_delab(v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_a_1170_; lean_object* v_ref_1171_; lean_object* v___x_1172_; lean_object* v_a_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; size_t v_sz_1178_; size_t v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
lean_inc(v_a_1170_);
lean_dec_ref_known(v___x_1169_, 1);
v_ref_1171_ = lean_ctor_get(v_a_1164_, 5);
v___x_1172_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0(v_ref_1171_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc_n(v_a_1173_, 2);
lean_dec_ref(v___x_1172_);
v___x_1174_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg___closed__4));
v___x_1175_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__0));
v___x_1176_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1176_, 0, v_a_1173_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
v___x_1177_ = l_Lean_Syntax_node1(v_a_1173_, v___x_1174_, v___x_1176_);
v_sz_1178_ = lean_array_size(v_a_1159_);
v___x_1179_ = ((size_t)0ULL);
v___x_1180_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__0(v_a_1170_, v___x_1177_, v_sz_1178_, v___x_1179_, v_a_1159_);
v___x_1181_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg(v___x_1180_);
if (lean_obj_tag(v___x_1181_) == 0)
{
uint8_t v_structural_1182_; 
v_structural_1182_ = lean_ctor_get_uint8(v_measure_1157_, sizeof(void*)*2);
lean_dec_ref(v_measure_1157_);
if (v_structural_1182_ == 0)
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1221_; 
v_a_1183_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1185_ = v___x_1181_;
v_isShared_1186_ = v_isSharedCheck_1221_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1181_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1221_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1187_; uint8_t v___x_1188_; 
v___x_1187_ = lean_array_get_size(v_a_1183_);
v___x_1188_ = lean_nat_dec_eq(v___x_1187_, v_zero_1167_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1203_; 
v___x_1189_ = l_Lean_SourceInfo_fromRef(v_ref_1171_, v___x_1188_);
v___x_1190_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3));
v___x_1191_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__4));
lean_inc_n(v___x_1189_, 5);
v___x_1192_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1189_);
lean_ctor_set(v___x_1192_, 1, v___x_1191_);
v___x_1193_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__6));
v___x_1194_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7, &l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7);
v___x_1195_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1189_);
lean_ctor_set(v___x_1195_, 1, v___x_1193_);
lean_ctor_set(v___x_1195_, 2, v___x_1194_);
v___x_1196_ = l_Array_append___redArg(v___x_1194_, v_a_1183_);
lean_dec(v_a_1183_);
v___x_1197_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1189_);
lean_ctor_set(v___x_1197_, 1, v___x_1193_);
lean_ctor_set(v___x_1197_, 2, v___x_1196_);
v___x_1198_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__8));
v___x_1199_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1189_);
lean_ctor_set(v___x_1199_, 1, v___x_1198_);
v___x_1200_ = l_Lean_Syntax_node2(v___x_1189_, v___x_1193_, v___x_1197_, v___x_1199_);
v___x_1201_ = l_Lean_Syntax_node4(v___x_1189_, v___x_1190_, v___x_1192_, v___x_1195_, v___x_1200_, v_a_1170_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v___x_1201_);
v___x_1203_ = v___x_1185_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1201_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
else
{
lean_object* v___x_1205_; lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1220_; 
lean_del_object(v___x_1185_);
lean_dec(v_a_1183_);
v___x_1205_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0(v_ref_1171_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1208_ = v___x_1205_;
v_isShared_1209_ = v_isSharedCheck_1220_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1205_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1220_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1218_; 
v___x_1210_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3));
v___x_1211_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__4));
lean_inc_n(v_a_1206_, 2);
v___x_1212_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1212_, 0, v_a_1206_);
lean_ctor_set(v___x_1212_, 1, v___x_1211_);
v___x_1213_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__6));
v___x_1214_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7, &l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7);
v___x_1215_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1215_, 0, v_a_1206_);
lean_ctor_set(v___x_1215_, 1, v___x_1213_);
lean_ctor_set(v___x_1215_, 2, v___x_1214_);
lean_inc_ref(v___x_1215_);
v___x_1216_ = l_Lean_Syntax_node4(v_a_1206_, v___x_1210_, v___x_1212_, v___x_1215_, v___x_1215_, v_a_1170_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v___x_1216_);
v___x_1218_ = v___x_1208_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1216_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
}
else
{
lean_object* v_a_1222_; lean_object* v___x_1223_; uint8_t v___x_1224_; 
v_a_1222_ = lean_ctor_get(v___x_1181_, 0);
lean_inc(v_a_1222_);
lean_dec_ref_known(v___x_1181_, 1);
v___x_1223_ = lean_array_get_size(v_a_1222_);
v___x_1224_ = lean_nat_dec_eq(v___x_1223_, v_zero_1167_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1247_; 
v___x_1225_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0(v_ref_1171_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1228_ = v___x_1225_;
v_isShared_1229_ = v_isSharedCheck_1247_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1225_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1247_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1245_; 
v___x_1230_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3));
v___x_1231_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__4));
lean_inc_n(v_a_1226_, 6);
v___x_1232_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1232_, 0, v_a_1226_);
lean_ctor_set(v___x_1232_, 1, v___x_1231_);
v___x_1233_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__6));
v___x_1234_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__9));
v___x_1235_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1235_, 0, v_a_1226_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
v___x_1236_ = l_Lean_Syntax_node1(v_a_1226_, v___x_1233_, v___x_1235_);
v___x_1237_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7, &l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7);
v___x_1238_ = l_Array_append___redArg(v___x_1237_, v_a_1222_);
lean_dec(v_a_1222_);
v___x_1239_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1239_, 0, v_a_1226_);
lean_ctor_set(v___x_1239_, 1, v___x_1233_);
lean_ctor_set(v___x_1239_, 2, v___x_1238_);
v___x_1240_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__8));
v___x_1241_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1241_, 0, v_a_1226_);
lean_ctor_set(v___x_1241_, 1, v___x_1240_);
v___x_1242_ = l_Lean_Syntax_node2(v_a_1226_, v___x_1233_, v___x_1239_, v___x_1241_);
v___x_1243_ = l_Lean_Syntax_node4(v_a_1226_, v___x_1230_, v___x_1232_, v___x_1236_, v___x_1242_, v_a_1170_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 0, v___x_1243_);
v___x_1245_ = v___x_1228_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v___x_1243_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
else
{
lean_object* v___x_1248_; lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1266_; 
lean_dec(v_a_1222_);
v___x_1248_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__0(v_ref_1171_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1251_ = v___x_1248_;
v_isShared_1252_ = v_isSharedCheck_1266_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1248_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1266_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1264_; 
v___x_1253_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__3));
v___x_1254_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__4));
lean_inc_n(v_a_1249_, 4);
v___x_1255_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1255_, 0, v_a_1249_);
lean_ctor_set(v___x_1255_, 1, v___x_1254_);
v___x_1256_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__6));
v___x_1257_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__9));
v___x_1258_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1258_, 0, v_a_1249_);
lean_ctor_set(v___x_1258_, 1, v___x_1257_);
v___x_1259_ = l_Lean_Syntax_node1(v_a_1249_, v___x_1256_, v___x_1258_);
v___x_1260_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7, &l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___closed__7);
v___x_1261_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1261_, 0, v_a_1249_);
lean_ctor_set(v___x_1261_, 1, v___x_1256_);
lean_ctor_set(v___x_1261_, 2, v___x_1260_);
v___x_1262_ = l_Lean_Syntax_node4(v_a_1249_, v___x_1253_, v___x_1255_, v___x_1259_, v___x_1261_, v_a_1170_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v___x_1262_);
v___x_1264_ = v___x_1251_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1262_);
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
}
else
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
lean_dec(v_a_1170_);
lean_dec_ref(v_measure_1157_);
v_a_1267_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v___x_1181_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1181_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
else
{
lean_dec_ref(v_a_1159_);
lean_dec_ref(v_measure_1157_);
return v___x_1169_;
}
}
else
{
lean_object* v___x_1275_; lean_object* v_a_1276_; uint8_t v___x_1277_; 
v___x_1275_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__2___redArg(v_a_1160_);
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
lean_inc(v_a_1276_);
lean_dec_ref(v___x_1275_);
v___x_1277_ = l_Lean_Expr_isLambda(v_a_1276_);
lean_dec(v_a_1276_);
if (v___x_1277_ == 0)
{
v_a_1158_ = v_zero_1167_;
goto _start;
}
else
{
lean_object* v_one_1279_; lean_object* v_n_1280_; lean_object* v___f_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v_one_1279_ = lean_unsigned_to_nat(1u);
v_n_1280_ = lean_nat_sub(v_a_1158_, v_one_1279_);
v___f_1281_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__1___boxed), 11, 3);
lean_closure_set(v___f_1281_, 0, v_a_1159_);
lean_closure_set(v___f_1281_, 1, v_measure_1157_);
lean_closure_set(v___f_1281_, 2, v_n_1280_);
v___x_1282_ = l_Lean_NameSet_empty;
v___x_1283_ = l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg(v___f_1281_, v_isZero_1168_, v___x_1282_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
return v___x_1283_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___lam__1(lean_object* v_a_1284_, lean_object* v_measure_1285_, lean_object* v_n_1286_, lean_object* v_n_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = lean_array_push(v_a_1284_, v_n_1287_);
v___x_1296_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go(v_measure_1285_, v_n_1286_, v___x_1295_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___boxed(lean_object* v_measure_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go(v_measure_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_);
lean_dec(v_a_1305_);
lean_dec_ref(v_a_1304_);
lean_dec(v_a_1303_);
lean_dec_ref(v_a_1302_);
lean_dec(v_a_1301_);
lean_dec_ref(v_a_1300_);
lean_dec(v_a_1298_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1(lean_object* v_inst_1308_, lean_object* v_a_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___redArg(v_a_1309_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1___boxed(lean_object* v_inst_1318_, lean_object* v_a_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_spec__1(v_inst_1318_, v_a_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter___redArg(lean_object* v_x_1328_, lean_object* v_x_1329_, lean_object* v_h__1_1330_, lean_object* v_h__2_1331_){
_start:
{
lean_object* v_zero_1332_; uint8_t v_isZero_1333_; 
v_zero_1332_ = lean_unsigned_to_nat(0u);
v_isZero_1333_ = lean_nat_dec_eq(v_x_1328_, v_zero_1332_);
if (v_isZero_1333_ == 1)
{
lean_object* v___x_1334_; 
lean_dec(v_h__2_1331_);
v___x_1334_ = lean_apply_1(v_h__1_1330_, v_x_1329_);
return v___x_1334_;
}
else
{
lean_object* v_one_1335_; lean_object* v_n_1336_; lean_object* v___x_1337_; 
lean_dec(v_h__1_1330_);
v_one_1335_ = lean_unsigned_to_nat(1u);
v_n_1336_ = lean_nat_sub(v_x_1328_, v_one_1335_);
v___x_1337_ = lean_apply_2(v_h__2_1331_, v_n_1336_, v_x_1329_);
return v___x_1337_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter___redArg___boxed(lean_object* v_x_1338_, lean_object* v_x_1339_, lean_object* v_h__1_1340_, lean_object* v_h__2_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter___redArg(v_x_1338_, v_x_1339_, v_h__1_1340_, v_h__2_1341_);
lean_dec(v_x_1338_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter(lean_object* v_motive_1343_, lean_object* v_x_1344_, lean_object* v_x_1345_, lean_object* v_h__1_1346_, lean_object* v_h__2_1347_){
_start:
{
lean_object* v_zero_1348_; uint8_t v_isZero_1349_; 
v_zero_1348_ = lean_unsigned_to_nat(0u);
v_isZero_1349_ = lean_nat_dec_eq(v_x_1344_, v_zero_1348_);
if (v_isZero_1349_ == 1)
{
lean_object* v___x_1350_; 
lean_dec(v_h__2_1347_);
v___x_1350_ = lean_apply_1(v_h__1_1346_, v_x_1345_);
return v___x_1350_;
}
else
{
lean_object* v_one_1351_; lean_object* v_n_1352_; lean_object* v___x_1353_; 
lean_dec(v_h__1_1346_);
v_one_1351_ = lean_unsigned_to_nat(1u);
v_n_1352_ = lean_nat_sub(v_x_1344_, v_one_1351_);
v___x_1353_ = lean_apply_2(v_h__2_1347_, v_n_1352_, v_x_1345_);
return v___x_1353_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter___boxed(lean_object* v_motive_1354_, lean_object* v_x_1355_, lean_object* v_x_1356_, lean_object* v_h__1_1357_, lean_object* v_h__2_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go_match__1_splitter(v_motive_1354_, v_x_1355_, v_x_1356_, v_h__1_1357_, v_h__2_1358_);
lean_dec(v_x_1355_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Array_map__unattach_match__1_splitter___redArg(lean_object* v_x_1360_, lean_object* v_h__1_1361_){
_start:
{
lean_object* v___x_1362_; 
v___x_1362_ = lean_apply_2(v_h__1_1361_, v_x_1360_, lean_box(0));
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Array_map__unattach_match__1_splitter(lean_object* v_00_u03b1_1363_, lean_object* v_P_1364_, lean_object* v_motive_1365_, lean_object* v_x_1366_, lean_object* v_h__1_1367_){
_start:
{
lean_object* v___x_1368_; 
v___x_1368_ = lean_apply_2(v_h__1_1367_, v_x_1366_, lean_box(0));
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___redArg(lean_object* v_e_1369_, lean_object* v_maxFVars_1370_, lean_object* v_k_1371_, uint8_t v_cleanupAnnotations_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v___f_1378_; uint8_t v___x_1379_; uint8_t v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___f_1378_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_TerminationMeasure_structuralArg_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1378_, 0, v_k_1371_);
v___x_1379_ = 1;
v___x_1380_ = 0;
v___x_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1381_, 0, v_maxFVars_1370_);
v___x_1382_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1369_, v___x_1379_, v___x_1380_, v___x_1379_, v___x_1380_, v___x_1381_, v___f_1378_, v_cleanupAnnotations_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_);
lean_dec_ref_known(v___x_1381_, 1);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1390_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1385_ = v___x_1382_;
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1382_);
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
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_a_1383_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
else
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1398_; 
v_a_1391_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1393_ = v___x_1382_;
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1382_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1394_ == 0)
{
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_a_1391_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___redArg___boxed(lean_object* v_e_1399_, lean_object* v_maxFVars_1400_, lean_object* v_k_1401_, lean_object* v_cleanupAnnotations_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1408_; lean_object* v_res_1409_; 
v_cleanupAnnotations_boxed_1408_ = lean_unbox(v_cleanupAnnotations_1402_);
v_res_1409_ = l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___redArg(v_e_1399_, v_maxFVars_1400_, v_k_1401_, v_cleanupAnnotations_boxed_1408_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0(lean_object* v_00_u03b1_1410_, lean_object* v_e_1411_, lean_object* v_maxFVars_1412_, lean_object* v_k_1413_, uint8_t v_cleanupAnnotations_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___redArg(v_e_1411_, v_maxFVars_1412_, v_k_1413_, v_cleanupAnnotations_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___boxed(lean_object* v_00_u03b1_1421_, lean_object* v_e_1422_, lean_object* v_maxFVars_1423_, lean_object* v_k_1424_, lean_object* v_cleanupAnnotations_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1431_; lean_object* v_res_1432_; 
v_cleanupAnnotations_boxed_1431_ = lean_unbox(v_cleanupAnnotations_1425_);
v_res_1432_ = l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0(v_00_u03b1_1421_, v_e_1422_, v_maxFVars_1423_, v_k_1424_, v_cleanupAnnotations_boxed_1431_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_delab___lam__0(lean_object* v_measure_1435_, lean_object* v_extraParams_1436_, lean_object* v___ys_1437_, lean_object* v_e_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1444_ = lean_box(1);
v___x_1445_ = ((lean_object*)(l_Lean_Elab_TerminationMeasure_delab___lam__0___closed__0));
v___x_1446_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_TerminationMeasure_0__Lean_Elab_TerminationMeasure_delab_go___boxed), 10, 3);
lean_closure_set(v___x_1446_, 0, v_measure_1435_);
lean_closure_set(v___x_1446_, 1, v_extraParams_1436_);
lean_closure_set(v___x_1446_, 2, v___x_1445_);
v___x_1447_ = l_Lean_PrettyPrinter_delabCore___redArg(v_e_1438_, v___x_1444_, v___x_1446_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1456_; 
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1450_ = v___x_1447_;
v_isShared_1451_ = v_isSharedCheck_1456_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1447_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1456_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v_fst_1452_; lean_object* v___x_1454_; 
v_fst_1452_ = lean_ctor_get(v_a_1448_, 0);
lean_inc(v_fst_1452_);
lean_dec(v_a_1448_);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 0, v_fst_1452_);
v___x_1454_ = v___x_1450_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_fst_1452_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
else
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
v_a_1457_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___x_1447_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1447_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1457_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_delab___lam__0___boxed(lean_object* v_measure_1465_, lean_object* v_extraParams_1466_, lean_object* v___ys_1467_, lean_object* v_e_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Lean_Elab_TerminationMeasure_delab___lam__0(v_measure_1465_, v_extraParams_1466_, v___ys_1467_, v_e_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec_ref(v___ys_1467_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_delab(lean_object* v_arity_1475_, lean_object* v_extraParams_1476_, lean_object* v_measure_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_){
_start:
{
lean_object* v_fn_1483_; lean_object* v___f_1484_; lean_object* v___x_1485_; uint8_t v___x_1486_; lean_object* v___x_1487_; 
v_fn_1483_ = lean_ctor_get(v_measure_1477_, 1);
lean_inc_ref(v_fn_1483_);
lean_inc(v_extraParams_1476_);
v___f_1484_ = lean_alloc_closure((void*)(l_Lean_Elab_TerminationMeasure_delab___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1484_, 0, v_measure_1477_);
lean_closure_set(v___f_1484_, 1, v_extraParams_1476_);
v___x_1485_ = lean_nat_sub(v_arity_1475_, v_extraParams_1476_);
lean_dec(v_extraParams_1476_);
v___x_1486_ = 0;
v___x_1487_ = l_Lean_Meta_lambdaBoundedTelescope___at___00Lean_Elab_TerminationMeasure_delab_spec__0___redArg(v_fn_1483_, v___x_1485_, v___f_1484_, v___x_1486_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationMeasure_delab___boxed(lean_object* v_arity_1488_, lean_object* v_extraParams_1489_, lean_object* v_measure_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l_Lean_Elab_TerminationMeasure_delab(v_arity_1488_, v_extraParams_1489_, v_measure_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_);
lean_dec(v_a_1494_);
lean_dec_ref(v_a_1493_);
lean_dec(v_a_1492_);
lean_dec_ref(v_a_1491_);
lean_dec(v_arity_1488_);
return v_res_1496_;
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
