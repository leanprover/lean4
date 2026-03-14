// Lean compiler output
// Module: Lean.Elab.Deriving.ToExpr
// Imports: import Lean.Elab.Deriving.Basic import Lean.Elab.Deriving.Util
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
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_instQuoteNameMkStr1___private__1(lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedInductiveVal_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_unzip___redArg(lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Elab_Deriving_mkDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkInductArgNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_Elab_Deriving_mkImplicitBinders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkInductiveApp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkContext(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkInstImplicitBinders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkInstName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withFreshMacroScope___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_autoImplicit;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withScope___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isInductiveCore(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_registerDerivingHandler(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Expr.app"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__6;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Expr"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(237, 218, 74, 184, 29, 214, 185, 80)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__8_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(163, 34, 173, 94, 44, 171, 142, 212)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__8_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__9_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(84, 208, 74, 211, 93, 83, 88, 82)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__9_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(134, 107, 4, 185, 254, 245, 50, 185)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__9_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__9_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__11_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__12_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__11_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__12_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__13_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__10_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__13_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__14_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__15_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__15_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "(internal error) expecting output of `mkInductiveApp`"};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__1;
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "explicit"};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(141, 201, 75, 195, 250, 223, 114, 184)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "explicitUniv"};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__6_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__5_value),LEAN_SCALAR_PTR_LITERAL(206, 217, 218, 63, 82, 102, 26, 62)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__6 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ".{"};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8;
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__9 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__10_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "toExpr"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 52, 227, 116, 90, 76, 120, 122)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ToExpr"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(221, 154, 161, 209, 228, 24, 88, 219)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(22, 159, 230, 112, 213, 72, 142, 157)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "toTypeExpr"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__7_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(87, 150, 145, 173, 219, 15, 141, 51)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__9_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__10_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(221, 154, 161, 209, 228, 24, 88, 219)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__10_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(33, 208, 59, 56, 123, 20, 70, 1)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__11_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__12_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Expr.const"};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__2;
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "const"};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(237, 218, 74, 184, 29, 214, 185, 80)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(147, 193, 172, 35, 150, 162, 194, 40)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(84, 208, 74, 211, 93, 83, 88, 82)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(22, 248, 240, 94, 191, 251, 149, 49)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__7_value),((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__8_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__9 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__6_value),((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__9_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term[_]"};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__11 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(86, 147, 168, 74, 195, 98, 232, 161)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__12 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__13 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__13_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__14 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__14_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.toLevel"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "toLevel"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(206, 60, 165, 28, 60, 216, 251, 208)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ToLevel"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(120, 83, 23, 100, 237, 86, 220, 93)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__5_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(72, 79, 140, 234, 59, 98, 175, 182)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__7_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___boxed__const__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___boxed__const__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 149, 207, 196, 17, 4, 77, 74)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__3;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(199, 20, 136, 12, 168, 217, 46, 241)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__4_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__5 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__5_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__6 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__3;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__4_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__5 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__5_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__6 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__6_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__1_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__1_value_aux_2),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__1_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__2_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__3;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__4_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___boxed(lean_object**);
static const lean_closure_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6___boxed(lean_object**);
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 208, 235, 82, 91, 230, 203, 159)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__3_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__0___redArg(lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "localinst"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(49, 72, 186, 87, 62, 92, 205, 11)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(61, 47, 121, 206, 37, 68, 134, 111)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letIdDecl"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__6_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__6_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(82, 96, 243, 36, 251, 209, 136, 237)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "letId"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__8_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__8_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__8_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(67, 92, 92, 51, 38, 250, 60, 190)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__9_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__10_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__10_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__10_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__10_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__11_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__12;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(100, 160, 234, 56, 97, 119, 7, 185)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__13_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__14_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(221, 154, 161, 209, 228, 24, 88, 219)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__14_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__15_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__16_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Deriving"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__17 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__17_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__18_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__18_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(230, 230, 99, 85, 138, 169, 166, 218)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__18_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(189, 81, 243, 137, 46, 3, 139, 245)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__18 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__18_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__18_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__19 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__19_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__14_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__20 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__20_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__20_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__21 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__21_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__19_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__21_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__22 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__22_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__19_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__22_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__23 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__23_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__19_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__23_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__24 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__24_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__19_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__24_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__25 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__25_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__15_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__25_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__26 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__26_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__27 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__27_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structInst"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__28 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__28_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__29_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__29_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__29_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(50, 43, 73, 62, 118, 124, 31, 28)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__29 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__29_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__30 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__30_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__31 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__31_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__32_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__32_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__32_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__32_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__31_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__32 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__32_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "structInstField"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__33 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__33_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__34_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__34_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__34_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(50, 77, 20, 88, 28, 210, 230, 84)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__34 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__34_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "structInstLVal"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__35 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__35_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__36_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__36_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__36_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__36_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(185, 133, 6, 147, 6, 183, 100, 198)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__36 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__36_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "structInstFieldDef"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__37 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__37_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__38_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__38_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__38_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__38_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__38_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__37_value),LEAN_SCALAR_PTR_LITERAL(81, 102, 39, 227, 176, 252, 65, 103)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__38 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__38_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "optEllipsis"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__39 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__39_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__40_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__40_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__40_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__40_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__40_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__39_value),LEAN_SCALAR_PTR_LITERAL(13, 1, 242, 203, 207, 188, 181, 160)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__40 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__40_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "inst"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(170, 188, 240, 205, 110, 63, 170, 91)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "explicitBinder"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 119, 193, 23, 170, 93, 183, 238)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__5;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(201, 247, 24, 34, 181, 234, 144, 103)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__7_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(120, 83, 23, 100, 237, 86, 220, 93)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__8_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__7_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__9_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__9_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__10_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__11_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__8_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__11_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__12_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__13_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__6 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__7;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(237, 218, 74, 184, 29, 214, 185, 80)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__9_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(84, 208, 74, 211, 93, 83, 88, 82)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__9 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__9_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__11 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__12 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__11_value),((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__12_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__13 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__10_value),((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__13_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__14 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__14_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__15 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__15_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__16 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__16_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__17 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__17_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "partial"};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__18 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__18_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "(internal error) expecting inst binder"};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__19 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__19_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mutual"};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions___closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 205, 8, 5, 164, 77, 17, 1)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "end"};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instBinder"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 219, 89, 171, 221, 95, 22, 227)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__0_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__0_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instance"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(37, 156, 84, 218, 244, 57, 142, 153)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__5_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__5_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__5_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declSig"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__8_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__8_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__7_value),LEAN_SCALAR_PTR_LITERAL(22, 101, 130, 251, 183, 19, 113, 82)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "whereStructInst"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__9_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__10_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__10_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__9_value),LEAN_SCALAR_PTR_LITERAL(164, 171, 248, 18, 201, 160, 43, 108)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__10_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "where"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__11_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__0_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(195, 196, 35, 37, 101, 57, 52, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__0_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 5, 156, 161, 41, 140, 236, 158)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1_spec__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__0_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__0_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__0_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__1_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__1_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__1_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__2_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__1_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__2_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__2_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__3_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__2_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__3_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__3_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__4_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__3_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__4_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__4_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__5_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__4_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(202, 58, 65, 192, 197, 114, 188, 72)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__5_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__5_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__6_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__5_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(9, 114, 41, 44, 174, 156, 17, 156)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__6_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__6_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__7_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__6_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(204, 141, 175, 151, 211, 220, 110, 94)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__7_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__7_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__8_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__7_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(77, 144, 227, 10, 107, 98, 192, 23)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__8_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__8_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__9_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__8_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(155, 91, 16, 179, 101, 62, 122, 113)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__9_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__9_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__10_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__9_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(117, 86, 203, 66, 217, 138, 21, 201)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__10_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__10_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__11_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__10_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(34, 122, 104, 224, 63, 144, 254, 96)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__11_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__11_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__12_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__12_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__12_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__13_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__11_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__12_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(151, 242, 59, 9, 38, 110, 105, 82)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__13_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__13_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__14_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__14_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__14_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__15_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__13_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__14_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(82, 193, 114, 250, 204, 188, 175, 215)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__15_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__15_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__16_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__15_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(83, 157, 79, 6, 2, 36, 201, 111)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__16_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__16_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__17_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__16_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(197, 23, 104, 165, 21, 163, 11, 100)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__17_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__17_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__18_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__17_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(171, 12, 144, 225, 172, 226, 198, 153)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__18_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__18_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__19_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__18_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(20, 137, 34, 255, 44, 40, 13, 227)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__19_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__19_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__20_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__19_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1932707508) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(227, 156, 239, 173, 217, 236, 151, 54)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__20_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__20_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__21_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__21_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__21_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__22_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__20_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__21_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(56, 37, 182, 186, 86, 37, 193, 0)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__22_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__22_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__23_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__23_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__23_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__24_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__22_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__23_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(220, 254, 148, 151, 34, 181, 169, 122)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__24_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__24_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__25_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__24_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(69, 27, 159, 213, 224, 40, 169, 200)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__25_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__25_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__6(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__5));
v___x_12_ = l_String_toRawSubstring_x27(v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg(lean_object* v_as_38_, size_t v_i_39_, size_t v_stop_40_, lean_object* v_b_41_, lean_object* v___y_42_){
_start:
{
uint8_t v___x_44_; 
v___x_44_ = lean_usize_dec_eq(v_i_39_, v_stop_40_);
if (v___x_44_ == 0)
{
lean_object* v_ref_45_; lean_object* v_quotContext_46_; lean_object* v_currMacroScope_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; size_t v___x_59_; size_t v___x_60_; 
v_ref_45_ = lean_ctor_get(v___y_42_, 5);
v_quotContext_46_ = lean_ctor_get(v___y_42_, 10);
v_currMacroScope_47_ = lean_ctor_get(v___y_42_, 11);
v___x_48_ = lean_array_uget_borrowed(v_as_38_, v_i_39_);
v___x_49_ = l_Lean_SourceInfo_fromRef(v_ref_45_, v___x_44_);
v___x_50_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_51_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__6, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__6);
v___x_52_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__8));
lean_inc(v_currMacroScope_47_);
lean_inc(v_quotContext_46_);
v___x_53_ = l_Lean_addMacroScope(v_quotContext_46_, v___x_52_, v_currMacroScope_47_);
v___x_54_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__14));
lean_inc(v___x_49_);
v___x_55_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_55_, 0, v___x_49_);
lean_ctor_set(v___x_55_, 1, v___x_51_);
lean_ctor_set(v___x_55_, 2, v___x_53_);
lean_ctor_set(v___x_55_, 3, v___x_54_);
v___x_56_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
lean_inc(v___x_48_);
lean_inc(v___x_49_);
v___x_57_ = l_Lean_Syntax_node2(v___x_49_, v___x_56_, v_b_41_, v___x_48_);
v___x_58_ = l_Lean_Syntax_node2(v___x_49_, v___x_50_, v___x_55_, v___x_57_);
v___x_59_ = ((size_t)1ULL);
v___x_60_ = lean_usize_add(v_i_39_, v___x_59_);
v_i_39_ = v___x_60_;
v_b_41_ = v___x_58_;
goto _start;
}
else
{
lean_object* v___x_62_; 
lean_dec_ref(v___y_42_);
v___x_62_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_62_, 0, v_b_41_);
return v___x_62_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___boxed(lean_object* v_as_63_, lean_object* v_i_64_, lean_object* v_stop_65_, lean_object* v_b_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
size_t v_i_boxed_69_; size_t v_stop_boxed_70_; lean_object* v_res_71_; 
v_i_boxed_69_ = lean_unbox_usize(v_i_64_);
lean_dec(v_i_64_);
v_stop_boxed_70_ = lean_unbox_usize(v_stop_65_);
lean_dec(v_stop_65_);
v_res_71_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg(v_as_63_, v_i_boxed_69_, v_stop_boxed_70_, v_b_66_, v___y_67_);
lean_dec_ref(v_as_63_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm(lean_object* v_f_72_, lean_object* v_args_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; uint8_t v___x_81_; 
v___x_79_ = lean_unsigned_to_nat(0u);
v___x_80_ = lean_array_get_size(v_args_73_);
v___x_81_ = lean_nat_dec_lt(v___x_79_, v___x_80_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; 
lean_dec_ref(v_a_76_);
v___x_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_82_, 0, v_f_72_);
return v___x_82_;
}
else
{
uint8_t v___x_83_; 
v___x_83_ = lean_nat_dec_le(v___x_80_, v___x_80_);
if (v___x_83_ == 0)
{
if (v___x_81_ == 0)
{
lean_object* v___x_84_; 
lean_dec_ref(v_a_76_);
v___x_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_84_, 0, v_f_72_);
return v___x_84_;
}
else
{
size_t v___x_85_; size_t v___x_86_; lean_object* v___x_87_; 
v___x_85_ = ((size_t)0ULL);
v___x_86_ = lean_usize_of_nat(v___x_80_);
v___x_87_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg(v_args_73_, v___x_85_, v___x_86_, v_f_72_, v_a_76_);
return v___x_87_;
}
}
else
{
size_t v___x_88_; size_t v___x_89_; lean_object* v___x_90_; 
v___x_88_ = ((size_t)0ULL);
v___x_89_ = lean_usize_of_nat(v___x_80_);
v___x_90_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg(v_args_73_, v___x_88_, v___x_89_, v_f_72_, v_a_76_);
return v___x_90_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm___boxed(lean_object* v_f_91_, lean_object* v_args_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm(v_f_91_, v_args_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_);
lean_dec(v_a_96_);
lean_dec(v_a_94_);
lean_dec_ref(v_a_93_);
lean_dec_ref(v_args_92_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0(lean_object* v_as_99_, size_t v_i_100_, size_t v_stop_101_, lean_object* v_b_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg(v_as_99_, v_i_100_, v_stop_101_, v_b_102_, v___y_105_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___boxed(lean_object* v_as_109_, lean_object* v_i_110_, lean_object* v_stop_111_, lean_object* v_b_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
size_t v_i_boxed_118_; size_t v_stop_boxed_119_; lean_object* v_res_120_; 
v_i_boxed_118_ = lean_unbox_usize(v_i_110_);
lean_dec(v_i_110_);
v_stop_boxed_119_ = lean_unbox_usize(v_stop_111_);
lean_dec(v_stop_111_);
v_res_120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0(v_as_109_, v_i_boxed_118_, v_stop_boxed_119_, v_b_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_);
lean_dec(v___y_116_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec_ref(v_as_109_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__2(size_t v_sz_121_, size_t v_i_122_, lean_object* v_bs_123_){
_start:
{
uint8_t v___x_124_; 
v___x_124_ = lean_usize_dec_lt(v_i_122_, v_sz_121_);
if (v___x_124_ == 0)
{
return v_bs_123_;
}
else
{
lean_object* v_v_125_; lean_object* v___x_126_; lean_object* v_bs_x27_127_; size_t v___x_128_; size_t v___x_129_; lean_object* v___x_130_; 
v_v_125_ = lean_array_uget(v_bs_123_, v_i_122_);
v___x_126_ = lean_unsigned_to_nat(0u);
v_bs_x27_127_ = lean_array_uset(v_bs_123_, v_i_122_, v___x_126_);
v___x_128_ = ((size_t)1ULL);
v___x_129_ = lean_usize_add(v_i_122_, v___x_128_);
v___x_130_ = lean_array_uset(v_bs_x27_127_, v_i_122_, v_v_125_);
v_i_122_ = v___x_129_;
v_bs_123_ = v___x_130_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__2___boxed(lean_object* v_sz_132_, lean_object* v_i_133_, lean_object* v_bs_134_){
_start:
{
size_t v_sz_boxed_135_; size_t v_i_boxed_136_; lean_object* v_res_137_; 
v_sz_boxed_135_ = lean_unbox_usize(v_sz_132_);
lean_dec(v_sz_132_);
v_i_boxed_136_ = lean_unbox_usize(v_i_133_);
lean_dec(v_i_133_);
v_res_137_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__2(v_sz_boxed_135_, v_i_boxed_136_, v_bs_134_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__1(size_t v_sz_138_, size_t v_i_139_, lean_object* v_bs_140_){
_start:
{
uint8_t v___x_141_; 
v___x_141_ = lean_usize_dec_lt(v_i_139_, v_sz_138_);
if (v___x_141_ == 0)
{
return v_bs_140_;
}
else
{
lean_object* v_v_142_; lean_object* v___x_143_; lean_object* v_bs_x27_144_; lean_object* v___x_145_; size_t v___x_146_; size_t v___x_147_; lean_object* v___x_148_; 
v_v_142_ = lean_array_uget(v_bs_140_, v_i_139_);
v___x_143_ = lean_unsigned_to_nat(0u);
v_bs_x27_144_ = lean_array_uset(v_bs_140_, v_i_139_, v___x_143_);
v___x_145_ = lean_mk_syntax_ident(v_v_142_);
v___x_146_ = ((size_t)1ULL);
v___x_147_ = lean_usize_add(v_i_139_, v___x_146_);
v___x_148_ = lean_array_uset(v_bs_x27_144_, v_i_139_, v___x_145_);
v_i_139_ = v___x_147_;
v_bs_140_ = v___x_148_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__1___boxed(lean_object* v_sz_150_, lean_object* v_i_151_, lean_object* v_bs_152_){
_start:
{
size_t v_sz_boxed_153_; size_t v_i_boxed_154_; lean_object* v_res_155_; 
v_sz_boxed_153_ = lean_unbox_usize(v_sz_150_);
lean_dec(v_sz_150_);
v_i_boxed_154_ = lean_unbox_usize(v_i_151_);
lean_dec(v_i_151_);
v_res_155_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__1(v_sz_boxed_153_, v_i_boxed_154_, v_bs_152_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__0(lean_object* v_msgData_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_){
_start:
{
lean_object* v___x_162_; lean_object* v_env_163_; lean_object* v___x_164_; lean_object* v_mctx_165_; lean_object* v_lctx_166_; lean_object* v_options_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_162_ = lean_st_ref_get(v___y_160_);
v_env_163_ = lean_ctor_get(v___x_162_, 0);
lean_inc_ref(v_env_163_);
lean_dec(v___x_162_);
v___x_164_ = lean_st_ref_get(v___y_158_);
v_mctx_165_ = lean_ctor_get(v___x_164_, 0);
lean_inc_ref(v_mctx_165_);
lean_dec(v___x_164_);
v_lctx_166_ = lean_ctor_get(v___y_157_, 2);
v_options_167_ = lean_ctor_get(v___y_159_, 2);
lean_inc_ref(v_options_167_);
lean_inc_ref(v_lctx_166_);
v___x_168_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_168_, 0, v_env_163_);
lean_ctor_set(v___x_168_, 1, v_mctx_165_);
lean_ctor_set(v___x_168_, 2, v_lctx_166_);
lean_ctor_set(v___x_168_, 3, v_options_167_);
v___x_169_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
lean_ctor_set(v___x_169_, 1, v_msgData_156_);
v___x_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__0___boxed(lean_object* v_msgData_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__0(v_msgData_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
return v_res_177_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = lean_box(1);
v___x_179_ = l_Lean_MessageData_ofFormat(v___x_178_);
return v___x_179_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__2));
v___x_184_ = l_Lean_MessageData_ofFormat(v___x_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3(lean_object* v_x_185_, lean_object* v_x_186_){
_start:
{
if (lean_obj_tag(v_x_186_) == 0)
{
return v_x_185_;
}
else
{
lean_object* v_head_187_; lean_object* v_tail_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_210_; 
v_head_187_ = lean_ctor_get(v_x_186_, 0);
v_tail_188_ = lean_ctor_get(v_x_186_, 1);
v_isSharedCheck_210_ = !lean_is_exclusive(v_x_186_);
if (v_isSharedCheck_210_ == 0)
{
v___x_190_ = v_x_186_;
v_isShared_191_ = v_isSharedCheck_210_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_tail_188_);
lean_inc(v_head_187_);
lean_dec(v_x_186_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_210_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v_before_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_208_; 
v_before_192_ = lean_ctor_get(v_head_187_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v_head_187_);
if (v_isSharedCheck_208_ == 0)
{
lean_object* v_unused_209_; 
v_unused_209_ = lean_ctor_get(v_head_187_, 1);
lean_dec(v_unused_209_);
v___x_194_ = v_head_187_;
v_isShared_195_ = v_isSharedCheck_208_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_before_192_);
lean_dec(v_head_187_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_208_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_196_; lean_object* v___x_198_; 
v___x_196_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_195_ == 0)
{
lean_ctor_set_tag(v___x_194_, 7);
lean_ctor_set(v___x_194_, 1, v___x_196_);
lean_ctor_set(v___x_194_, 0, v_x_185_);
v___x_198_ = v___x_194_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_x_185_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v___x_196_);
v___x_198_ = v_reuseFailAlloc_207_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
lean_object* v___x_199_; lean_object* v___x_201_; 
v___x_199_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__3);
if (v_isShared_191_ == 0)
{
lean_ctor_set_tag(v___x_190_, 7);
lean_ctor_set(v___x_190_, 1, v___x_199_);
lean_ctor_set(v___x_190_, 0, v___x_198_);
v___x_201_ = v___x_190_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_198_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v___x_199_);
v___x_201_ = v_reuseFailAlloc_206_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_202_ = l_Lean_MessageData_ofSyntax(v_before_192_);
v___x_203_ = l_Lean_indentD(v___x_202_);
v___x_204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_201_);
lean_ctor_set(v___x_204_, 1, v___x_203_);
v_x_185_ = v___x_204_;
v_x_186_ = v_tail_188_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__2(lean_object* v_opts_211_, lean_object* v_opt_212_){
_start:
{
lean_object* v_name_213_; lean_object* v_defValue_214_; lean_object* v_map_215_; lean_object* v___x_216_; 
v_name_213_ = lean_ctor_get(v_opt_212_, 0);
v_defValue_214_ = lean_ctor_get(v_opt_212_, 1);
v_map_215_ = lean_ctor_get(v_opts_211_, 0);
v___x_216_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_215_, v_name_213_);
if (lean_obj_tag(v___x_216_) == 0)
{
uint8_t v___x_217_; 
v___x_217_ = lean_unbox(v_defValue_214_);
return v___x_217_;
}
else
{
lean_object* v_val_218_; 
v_val_218_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_val_218_);
lean_dec_ref(v___x_216_);
if (lean_obj_tag(v_val_218_) == 1)
{
uint8_t v_v_219_; 
v_v_219_ = lean_ctor_get_uint8(v_val_218_, 0);
lean_dec_ref(v_val_218_);
return v_v_219_;
}
else
{
uint8_t v___x_220_; 
lean_dec(v_val_218_);
v___x_220_ = lean_unbox(v_defValue_214_);
return v___x_220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__2___boxed(lean_object* v_opts_221_, lean_object* v_opt_222_){
_start:
{
uint8_t v_res_223_; lean_object* v_r_224_; 
v_res_223_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__2(v_opts_221_, v_opt_222_);
lean_dec_ref(v_opt_222_);
lean_dec_ref(v_opts_221_);
v_r_224_ = lean_box(v_res_223_);
return v_r_224_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg___closed__1));
v___x_229_ = l_Lean_MessageData_ofFormat(v___x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg(lean_object* v_msgData_230_, lean_object* v_macroStack_231_, lean_object* v___y_232_){
_start:
{
lean_object* v_options_234_; lean_object* v___x_235_; uint8_t v___x_236_; 
v_options_234_ = lean_ctor_get(v___y_232_, 2);
v___x_235_ = l_Lean_Elab_pp_macroStack;
v___x_236_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__2(v_options_234_, v___x_235_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; 
lean_dec(v_macroStack_231_);
v___x_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_237_, 0, v_msgData_230_);
return v___x_237_;
}
else
{
if (lean_obj_tag(v_macroStack_231_) == 0)
{
lean_object* v___x_238_; 
v___x_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_238_, 0, v_msgData_230_);
return v___x_238_;
}
else
{
lean_object* v_head_239_; lean_object* v_after_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_255_; 
v_head_239_ = lean_ctor_get(v_macroStack_231_, 0);
lean_inc(v_head_239_);
v_after_240_ = lean_ctor_get(v_head_239_, 1);
v_isSharedCheck_255_ = !lean_is_exclusive(v_head_239_);
if (v_isSharedCheck_255_ == 0)
{
lean_object* v_unused_256_; 
v_unused_256_ = lean_ctor_get(v_head_239_, 0);
lean_dec(v_unused_256_);
v___x_242_ = v_head_239_;
v_isShared_243_ = v_isSharedCheck_255_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_after_240_);
lean_dec(v_head_239_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_255_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_244_; lean_object* v___x_246_; 
v___x_244_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_243_ == 0)
{
lean_ctor_set_tag(v___x_242_, 7);
lean_ctor_set(v___x_242_, 1, v___x_244_);
lean_ctor_set(v___x_242_, 0, v_msgData_230_);
v___x_246_ = v___x_242_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_msgData_230_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v___x_244_);
v___x_246_ = v_reuseFailAlloc_254_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v_msgData_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_247_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg___closed__2);
v___x_248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_246_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
v___x_249_ = l_Lean_MessageData_ofSyntax(v_after_240_);
v___x_250_ = l_Lean_indentD(v___x_249_);
v_msgData_251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_251_, 0, v___x_248_);
lean_ctor_set(v_msgData_251_, 1, v___x_250_);
v___x_252_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3(v_msgData_251_, v_macroStack_231_);
v___x_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
return v___x_253_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_257_, lean_object* v_macroStack_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg(v_msgData_257_, v_macroStack_258_, v___y_259_);
lean_dec_ref(v___y_259_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(lean_object* v_msg_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
lean_object* v_ref_270_; lean_object* v___x_271_; lean_object* v_a_272_; lean_object* v_macroStack_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_284_; 
v_ref_270_ = lean_ctor_get(v___y_267_, 5);
v___x_271_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__0(v_msg_262_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
v_a_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc(v_a_272_);
lean_dec_ref(v___x_271_);
v_macroStack_273_ = lean_ctor_get(v___y_263_, 1);
lean_inc(v_macroStack_273_);
lean_dec_ref(v___y_263_);
lean_inc(v_macroStack_273_);
v___x_274_ = l_Lean_Elab_getBetterRef(v_ref_270_, v_macroStack_273_);
v___x_275_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg(v_a_272_, v_macroStack_273_, v___y_267_);
v_a_276_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_284_ == 0)
{
v___x_278_ = v___x_275_;
v_isShared_279_ = v_isSharedCheck_284_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_275_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_284_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_274_);
lean_ctor_set(v___x_280_, 1, v_a_276_);
if (v_isShared_279_ == 0)
{
lean_ctor_set_tag(v___x_278_, 1);
lean_ctor_set(v___x_278_, 0, v___x_280_);
v___x_282_ = v___x_278_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_280_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg___boxed(lean_object* v_msg_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v_msg_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec(v___y_287_);
return v_res_293_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__1(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__0));
v___x_296_ = l_Lean_stringToMessageData(v___x_295_);
return v___x_296_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8(void){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = l_Array_mkArray0(lean_box(0));
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType(lean_object* v_indVal_314_, lean_object* v_t_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_){
_start:
{
lean_object* v_toConstantVal_323_; lean_object* v_levelParams_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_372_; 
v_toConstantVal_323_ = lean_ctor_get(v_indVal_314_, 0);
lean_inc_ref(v_toConstantVal_323_);
lean_dec_ref(v_indVal_314_);
v_levelParams_324_ = lean_ctor_get(v_toConstantVal_323_, 1);
v_isSharedCheck_372_ = !lean_is_exclusive(v_toConstantVal_323_);
if (v_isSharedCheck_372_ == 0)
{
lean_object* v_unused_373_; lean_object* v_unused_374_; 
v_unused_373_ = lean_ctor_get(v_toConstantVal_323_, 2);
lean_dec(v_unused_373_);
v_unused_374_ = lean_ctor_get(v_toConstantVal_323_, 0);
lean_dec(v_unused_374_);
v___x_326_ = v_toConstantVal_323_;
v_isShared_327_ = v_isSharedCheck_372_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_levelParams_324_);
lean_dec(v_toConstantVal_323_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_372_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_328_; uint8_t v___x_329_; 
v___x_328_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
lean_inc(v_t_315_);
v___x_329_ = l_Lean_Syntax_isOfKind(v_t_315_, v___x_328_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; lean_object* v___x_331_; 
lean_del_object(v___x_326_);
lean_dec(v_levelParams_324_);
lean_dec(v_t_315_);
v___x_330_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__1, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__1_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__1);
v___x_331_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v___x_330_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_);
return v___x_331_;
}
else
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_332_ = lean_unsigned_to_nat(0u);
v___x_333_ = l_Lean_Syntax_getArg(v_t_315_, v___x_332_);
v___x_334_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__3));
lean_inc(v___x_333_);
v___x_335_ = l_Lean_Syntax_isOfKind(v___x_333_, v___x_334_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; lean_object* v___x_337_; 
lean_dec(v___x_333_);
lean_del_object(v___x_326_);
lean_dec(v_levelParams_324_);
lean_dec(v_t_315_);
v___x_336_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__1, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__1_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__1);
v___x_337_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v___x_336_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_);
return v___x_337_;
}
else
{
lean_object* v_ref_338_; lean_object* v___x_339_; size_t v_sz_340_; size_t v___x_341_; lean_object* v_levels_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v_args_346_; uint8_t v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; size_t v_sz_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_362_; 
lean_dec_ref(v_a_316_);
v_ref_338_ = lean_ctor_get(v_a_320_, 5);
v___x_339_ = lean_array_mk(v_levelParams_324_);
v_sz_340_ = lean_array_size(v___x_339_);
v___x_341_ = ((size_t)0ULL);
v_levels_342_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__1(v_sz_340_, v___x_341_, v___x_339_);
v___x_343_ = lean_unsigned_to_nat(1u);
v___x_344_ = l_Lean_Syntax_getArg(v___x_333_, v___x_343_);
lean_dec(v___x_333_);
v___x_345_ = l_Lean_Syntax_getArg(v_t_315_, v___x_343_);
lean_dec(v_t_315_);
v_args_346_ = l_Lean_Syntax_getArgs(v___x_345_);
lean_dec(v___x_345_);
v___x_347_ = 0;
v___x_348_ = l_Lean_SourceInfo_fromRef(v_ref_338_, v___x_347_);
v___x_349_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__4));
lean_inc(v___x_348_);
v___x_350_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_348_);
lean_ctor_set(v___x_350_, 1, v___x_349_);
v___x_351_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__6));
v___x_352_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__7));
lean_inc(v___x_348_);
v___x_353_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_348_);
lean_ctor_set(v___x_353_, 1, v___x_352_);
v___x_354_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_355_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_356_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__9));
v_sz_357_ = lean_array_size(v_levels_342_);
v___x_358_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__2(v_sz_357_, v___x_341_, v_levels_342_);
v___x_359_ = l_Lean_Syntax_SepArray_ofElems(v___x_356_, v___x_358_);
lean_dec_ref(v___x_358_);
v___x_360_ = l_Array_append___redArg(v___x_355_, v___x_359_);
lean_dec_ref(v___x_359_);
lean_inc(v___x_348_);
if (v_isShared_327_ == 0)
{
lean_ctor_set_tag(v___x_326_, 1);
lean_ctor_set(v___x_326_, 2, v___x_360_);
lean_ctor_set(v___x_326_, 1, v___x_354_);
lean_ctor_set(v___x_326_, 0, v___x_348_);
v___x_362_ = v___x_326_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_348_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v___x_354_);
lean_ctor_set(v_reuseFailAlloc_371_, 2, v___x_360_);
v___x_362_ = v_reuseFailAlloc_371_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_363_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__10));
lean_inc(v___x_348_);
v___x_364_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_348_);
lean_ctor_set(v___x_364_, 1, v___x_363_);
lean_inc(v___x_348_);
v___x_365_ = l_Lean_Syntax_node4(v___x_348_, v___x_351_, v___x_344_, v___x_353_, v___x_362_, v___x_364_);
lean_inc(v___x_348_);
v___x_366_ = l_Lean_Syntax_node2(v___x_348_, v___x_334_, v___x_350_, v___x_365_);
v___x_367_ = l_Array_append___redArg(v___x_355_, v_args_346_);
lean_dec_ref(v_args_346_);
lean_inc(v___x_348_);
v___x_368_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_368_, 0, v___x_348_);
lean_ctor_set(v___x_368_, 1, v___x_354_);
lean_ctor_set(v___x_368_, 2, v___x_367_);
v___x_369_ = l_Lean_Syntax_node2(v___x_348_, v___x_328_, v___x_366_, v___x_368_);
v___x_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
return v___x_370_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___boxed(lean_object* v_indVal_375_, lean_object* v_t_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType(v_indVal_375_, v_t_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
lean_dec(v_a_382_);
lean_dec_ref(v_a_381_);
lean_dec(v_a_380_);
lean_dec_ref(v_a_379_);
lean_dec(v_a_378_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0(lean_object* v_00_u03b1_385_, lean_object* v_msg_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v_msg_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___boxed(lean_object* v_00_u03b1_395_, lean_object* v_msg_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0(v_00_u03b1_395_, v_msg_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1(lean_object* v_msgData_405_, lean_object* v_macroStack_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg(v_msgData_405_, v_macroStack_406_, v___y_411_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___boxed(lean_object* v_msgData_415_, lean_object* v_macroStack_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1(v_msgData_415_, v_macroStack_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg___lam__0(lean_object* v_k_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v_b_428_, lean_object* v_c_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = lean_apply_9(v_k_425_, v_b_428_, v_c_429_, v___y_426_, v___y_427_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, lean_box(0));
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg___lam__0___boxed(lean_object* v_k_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v_b_439_, lean_object* v_c_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg___lam__0(v_k_436_, v___y_437_, v___y_438_, v_b_439_, v_c_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg(lean_object* v_type_447_, lean_object* v_k_448_, uint8_t v_cleanupAnnotations_449_, uint8_t v_whnfType_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v___f_458_; lean_object* v___x_459_; 
v___f_458_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_458_, 0, v_k_448_);
lean_closure_set(v___f_458_, 1, v___y_451_);
lean_closure_set(v___f_458_, 2, v___y_452_);
v___x_459_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_447_, v___f_458_, v_cleanupAnnotations_449_, v_whnfType_450_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
if (lean_obj_tag(v___x_459_) == 0)
{
return v___x_459_;
}
else
{
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_467_; 
v_a_460_ = lean_ctor_get(v___x_459_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_467_ == 0)
{
v___x_462_ = v___x_459_;
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v___x_459_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_465_; 
if (v_isShared_463_ == 0)
{
v___x_465_ = v___x_462_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_a_460_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg___boxed(lean_object* v_type_468_, lean_object* v_k_469_, lean_object* v_cleanupAnnotations_470_, lean_object* v_whnfType_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_479_; uint8_t v_whnfType_boxed_480_; lean_object* v_res_481_; 
v_cleanupAnnotations_boxed_479_ = lean_unbox(v_cleanupAnnotations_470_);
v_whnfType_boxed_480_ = lean_unbox(v_whnfType_471_);
v_res_481_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg(v_type_468_, v_k_469_, v_cleanupAnnotations_boxed_479_, v_whnfType_boxed_480_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2(lean_object* v_00_u03b1_482_, lean_object* v_type_483_, lean_object* v_k_484_, uint8_t v_cleanupAnnotations_485_, uint8_t v_whnfType_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg(v_type_483_, v_k_484_, v_cleanupAnnotations_485_, v_whnfType_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___boxed(lean_object* v_00_u03b1_495_, lean_object* v_type_496_, lean_object* v_k_497_, lean_object* v_cleanupAnnotations_498_, lean_object* v_whnfType_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_507_; uint8_t v_whnfType_boxed_508_; lean_object* v_res_509_; 
v_cleanupAnnotations_boxed_507_ = lean_unbox(v_cleanupAnnotations_498_);
v_whnfType_boxed_508_ = lean_unbox(v_whnfType_499_);
v_res_509_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2(v_00_u03b1_495_, v_type_496_, v_k_497_, v_cleanupAnnotations_boxed_507_, v_whnfType_boxed_508_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
return v_res_509_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__0));
v___x_512_ = l_String_toRawSubstring_x27(v___x_511_);
return v___x_512_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8(void){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__7));
v___x_528_ = l_String_toRawSubstring_x27(v___x_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg(lean_object* v_as_541_, size_t v_sz_542_, size_t v_i_543_, lean_object* v_b_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
uint8_t v___x_550_; 
v___x_550_ = lean_usize_dec_lt(v_i_543_, v_sz_542_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; 
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
v___x_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_551_, 0, v_b_544_);
return v___x_551_;
}
else
{
lean_object* v_snd_552_; lean_object* v_fst_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_632_; 
v_snd_552_ = lean_ctor_get(v_b_544_, 1);
v_fst_553_ = lean_ctor_get(v_b_544_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v_b_544_);
if (v_isSharedCheck_632_ == 0)
{
v___x_555_ = v_b_544_;
v_isShared_556_ = v_isSharedCheck_632_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_snd_552_);
lean_inc(v_fst_553_);
lean_dec(v_b_544_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_632_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v_array_557_; lean_object* v_start_558_; lean_object* v_stop_559_; uint8_t v___x_560_; 
v_array_557_ = lean_ctor_get(v_snd_552_, 0);
v_start_558_ = lean_ctor_get(v_snd_552_, 1);
v_stop_559_ = lean_ctor_get(v_snd_552_, 2);
v___x_560_ = lean_nat_dec_lt(v_start_558_, v_stop_559_);
if (v___x_560_ == 0)
{
lean_object* v___x_562_; 
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
if (v_isShared_556_ == 0)
{
v___x_562_ = v___x_555_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_fst_553_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_snd_552_);
v___x_562_ = v_reuseFailAlloc_564_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
lean_object* v___x_563_; 
v___x_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
return v___x_563_;
}
}
else
{
lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_628_; 
lean_inc(v_stop_559_);
lean_inc(v_start_558_);
lean_inc_ref(v_array_557_);
v_isSharedCheck_628_ = !lean_is_exclusive(v_snd_552_);
if (v_isSharedCheck_628_ == 0)
{
lean_object* v_unused_629_; lean_object* v_unused_630_; lean_object* v_unused_631_; 
v_unused_629_ = lean_ctor_get(v_snd_552_, 2);
lean_dec(v_unused_629_);
v_unused_630_ = lean_ctor_get(v_snd_552_, 1);
lean_dec(v_unused_630_);
v_unused_631_ = lean_ctor_get(v_snd_552_, 0);
lean_dec(v_unused_631_);
v___x_566_ = v_snd_552_;
v_isShared_567_ = v_isSharedCheck_628_;
goto v_resetjp_565_;
}
else
{
lean_dec(v_snd_552_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_628_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = lean_array_fget_borrowed(v_array_557_, v_start_558_);
lean_inc(v___y_548_);
lean_inc_ref(v___y_547_);
lean_inc(v___y_546_);
lean_inc_ref(v___y_545_);
lean_inc(v___x_568_);
v___x_569_ = l_Lean_Meta_isType(v___x_568_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; lean_object* v_a_572_; lean_object* v_a_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_580_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_a_570_);
lean_dec_ref(v___x_569_);
v_a_576_ = lean_array_uget_borrowed(v_as_541_, v_i_543_);
v___x_577_ = lean_unsigned_to_nat(1u);
v___x_578_ = lean_nat_add(v_start_558_, v___x_577_);
lean_dec(v_start_558_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 1, v___x_578_);
v___x_580_ = v___x_566_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_array_557_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v___x_578_);
lean_ctor_set(v_reuseFailAlloc_619_, 2, v_stop_559_);
v___x_580_ = v_reuseFailAlloc_619_;
goto v_reusejp_579_;
}
v___jp_571_:
{
size_t v___x_573_; size_t v___x_574_; 
v___x_573_ = ((size_t)1ULL);
v___x_574_ = lean_usize_add(v_i_543_, v___x_573_);
v_i_543_ = v___x_574_;
v_b_544_ = v_a_572_;
goto _start;
}
v_reusejp_579_:
{
lean_object* v___x_581_; uint8_t v___x_582_; 
lean_inc(v_a_576_);
v___x_581_ = lean_mk_syntax_ident(v_a_576_);
v___x_582_ = lean_unbox(v_a_570_);
if (v___x_582_ == 0)
{
lean_object* v_ref_583_; lean_object* v_quotContext_584_; lean_object* v_currMacroScope_585_; uint8_t v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_599_; 
v_ref_583_ = lean_ctor_get(v___y_547_, 5);
v_quotContext_584_ = lean_ctor_get(v___y_547_, 10);
v_currMacroScope_585_ = lean_ctor_get(v___y_547_, 11);
v___x_586_ = lean_unbox(v_a_570_);
lean_dec(v_a_570_);
v___x_587_ = l_Lean_SourceInfo_fromRef(v_ref_583_, v___x_586_);
v___x_588_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_589_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1);
v___x_590_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__2));
lean_inc(v_currMacroScope_585_);
lean_inc(v_quotContext_584_);
v___x_591_ = l_Lean_addMacroScope(v_quotContext_584_, v___x_590_, v_currMacroScope_585_);
v___x_592_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__6));
lean_inc(v___x_587_);
v___x_593_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_593_, 0, v___x_587_);
lean_ctor_set(v___x_593_, 1, v___x_589_);
lean_ctor_set(v___x_593_, 2, v___x_591_);
lean_ctor_set(v___x_593_, 3, v___x_592_);
v___x_594_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
lean_inc(v___x_587_);
v___x_595_ = l_Lean_Syntax_node1(v___x_587_, v___x_594_, v___x_581_);
v___x_596_ = l_Lean_Syntax_node2(v___x_587_, v___x_588_, v___x_593_, v___x_595_);
v___x_597_ = lean_array_push(v_fst_553_, v___x_596_);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 1, v___x_580_);
lean_ctor_set(v___x_555_, 0, v___x_597_);
v___x_599_ = v___x_555_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_597_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v___x_580_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
v_a_572_ = v___x_599_;
goto v___jp_571_;
}
}
else
{
lean_object* v_ref_601_; lean_object* v_quotContext_602_; lean_object* v_currMacroScope_603_; uint8_t v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_617_; 
lean_dec(v_a_570_);
v_ref_601_ = lean_ctor_get(v___y_547_, 5);
v_quotContext_602_ = lean_ctor_get(v___y_547_, 10);
v_currMacroScope_603_ = lean_ctor_get(v___y_547_, 11);
v___x_604_ = 0;
v___x_605_ = l_Lean_SourceInfo_fromRef(v_ref_601_, v___x_604_);
v___x_606_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_607_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8);
v___x_608_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__9));
lean_inc(v_currMacroScope_603_);
lean_inc(v_quotContext_602_);
v___x_609_ = l_Lean_addMacroScope(v_quotContext_602_, v___x_608_, v_currMacroScope_603_);
v___x_610_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__12));
lean_inc(v___x_605_);
v___x_611_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_611_, 0, v___x_605_);
lean_ctor_set(v___x_611_, 1, v___x_607_);
lean_ctor_set(v___x_611_, 2, v___x_609_);
lean_ctor_set(v___x_611_, 3, v___x_610_);
v___x_612_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
lean_inc(v___x_605_);
v___x_613_ = l_Lean_Syntax_node1(v___x_605_, v___x_612_, v___x_581_);
v___x_614_ = l_Lean_Syntax_node2(v___x_605_, v___x_606_, v___x_611_, v___x_613_);
v___x_615_ = lean_array_push(v_fst_553_, v___x_614_);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 1, v___x_580_);
lean_ctor_set(v___x_555_, 0, v___x_615_);
v___x_617_ = v___x_555_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_615_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v___x_580_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
v_a_572_ = v___x_617_;
goto v___jp_571_;
}
}
}
}
else
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
lean_del_object(v___x_566_);
lean_dec(v_stop_559_);
lean_dec(v_start_558_);
lean_dec_ref(v_array_557_);
lean_del_object(v___x_555_);
lean_dec(v_fst_553_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
v_a_620_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_627_ == 0)
{
v___x_622_ = v___x_569_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_569_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___boxed(lean_object* v_as_633_, lean_object* v_sz_634_, lean_object* v_i_635_, lean_object* v_b_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
size_t v_sz_boxed_642_; size_t v_i_boxed_643_; lean_object* v_res_644_; 
v_sz_boxed_642_ = lean_unbox_usize(v_sz_634_);
lean_dec(v_sz_634_);
v_i_boxed_643_ = lean_unbox_usize(v_i_635_);
lean_dec(v_i_635_);
v_res_644_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg(v_as_633_, v_sz_boxed_642_, v_i_boxed_643_, v_b_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
lean_dec_ref(v_as_633_);
return v_res_644_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__1));
v___x_649_ = l_String_toRawSubstring_x27(v___x_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0(lean_object* v_argNames_677_, size_t v___x_678_, lean_object* v_name_679_, lean_object* v_a_680_, lean_object* v_xs_681_, lean_object* v_x_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; size_t v_sz_695_; lean_object* v___x_696_; 
v___x_690_ = lean_unsigned_to_nat(0u);
v___x_691_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__0));
v___x_692_ = lean_array_get_size(v_xs_681_);
v___x_693_ = l_Array_toSubarray___redArg(v_xs_681_, v___x_690_, v___x_692_);
v___x_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_691_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
v_sz_695_ = lean_array_size(v_argNames_677_);
lean_inc(v___y_688_);
lean_inc_ref(v___y_687_);
lean_inc(v___y_686_);
lean_inc_ref(v___y_685_);
v___x_696_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg(v_argNames_677_, v_sz_695_, v___x_678_, v___x_694_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v_a_697_; lean_object* v_fst_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_731_; 
v_a_697_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_a_697_);
lean_dec_ref(v___x_696_);
v_fst_698_ = lean_ctor_get(v_a_697_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v_a_697_);
if (v_isSharedCheck_731_ == 0)
{
lean_object* v_unused_732_; 
v_unused_732_ = lean_ctor_get(v_a_697_, 1);
lean_dec(v_unused_732_);
v___x_700_ = v_a_697_;
v_isShared_701_ = v_isSharedCheck_731_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_fst_698_);
lean_dec(v_a_697_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_731_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v_ref_702_; lean_object* v_quotContext_703_; lean_object* v_currMacroScope_704_; uint8_t v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_718_; 
v_ref_702_ = lean_ctor_get(v___y_687_, 5);
v_quotContext_703_ = lean_ctor_get(v___y_687_, 10);
v_currMacroScope_704_ = lean_ctor_get(v___y_687_, 11);
v___x_705_ = 0;
v___x_706_ = l_Lean_SourceInfo_fromRef(v_ref_702_, v___x_705_);
v___x_707_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_708_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__2, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__2_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__2);
v___x_709_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__4));
lean_inc(v_currMacroScope_704_);
lean_inc(v_quotContext_703_);
v___x_710_ = l_Lean_addMacroScope(v_quotContext_703_, v___x_709_, v_currMacroScope_704_);
v___x_711_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__10));
lean_inc(v___x_706_);
v___x_712_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_712_, 0, v___x_706_);
lean_ctor_set(v___x_712_, 1, v___x_708_);
lean_ctor_set(v___x_712_, 2, v___x_710_);
lean_ctor_set(v___x_712_, 3, v___x_711_);
v___x_713_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_714_ = l_Lean_instQuoteNameMkStr1___private__1(v_name_679_);
v___x_715_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__12));
v___x_716_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__13));
lean_inc(v___x_706_);
if (v_isShared_701_ == 0)
{
lean_ctor_set_tag(v___x_700_, 2);
lean_ctor_set(v___x_700_, 1, v___x_716_);
lean_ctor_set(v___x_700_, 0, v___x_706_);
v___x_718_ = v___x_700_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_706_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v___x_716_);
v___x_718_ = v_reuseFailAlloc_730_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_719_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_720_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__9));
v___x_721_ = l_Lean_Syntax_SepArray_ofElems(v___x_720_, v_a_680_);
v___x_722_ = l_Array_append___redArg(v___x_719_, v___x_721_);
lean_dec_ref(v___x_721_);
lean_inc(v___x_706_);
v___x_723_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_723_, 0, v___x_706_);
lean_ctor_set(v___x_723_, 1, v___x_713_);
lean_ctor_set(v___x_723_, 2, v___x_722_);
v___x_724_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__14));
lean_inc(v___x_706_);
v___x_725_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_725_, 0, v___x_706_);
lean_ctor_set(v___x_725_, 1, v___x_724_);
lean_inc(v___x_706_);
v___x_726_ = l_Lean_Syntax_node3(v___x_706_, v___x_715_, v___x_718_, v___x_723_, v___x_725_);
lean_inc(v___x_706_);
v___x_727_ = l_Lean_Syntax_node2(v___x_706_, v___x_713_, v___x_714_, v___x_726_);
v___x_728_ = l_Lean_Syntax_node2(v___x_706_, v___x_707_, v___x_712_, v___x_727_);
v___x_729_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm(v___x_728_, v_fst_698_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
lean_dec(v___y_688_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v_fst_698_);
return v___x_729_;
}
}
}
else
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_740_; 
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v_name_679_);
v_a_733_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_740_ == 0)
{
v___x_735_ = v___x_696_;
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_696_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_738_; 
if (v_isShared_736_ == 0)
{
v___x_738_ = v___x_735_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_a_733_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___boxed(lean_object* v_argNames_741_, lean_object* v___x_742_, lean_object* v_name_743_, lean_object* v_a_744_, lean_object* v_xs_745_, lean_object* v_x_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
size_t v___x_11428__boxed_754_; lean_object* v_res_755_; 
v___x_11428__boxed_754_ = lean_unbox_usize(v___x_742_);
lean_dec(v___x_742_);
v_res_755_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0(v_argNames_741_, v___x_11428__boxed_754_, v_name_743_, v_a_744_, v_xs_745_, v_x_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec_ref(v_x_746_);
lean_dec_ref(v_a_744_);
lean_dec_ref(v_argNames_741_);
return v_res_755_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_757_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__0));
v___x_758_ = l_String_toRawSubstring_x27(v___x_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg(size_t v_sz_774_, size_t v_i_775_, lean_object* v_bs_776_, lean_object* v___y_777_){
_start:
{
uint8_t v___x_779_; 
v___x_779_ = lean_usize_dec_lt(v_i_775_, v_sz_774_);
if (v___x_779_ == 0)
{
lean_object* v___x_780_; 
lean_dec_ref(v___y_777_);
v___x_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_780_, 0, v_bs_776_);
return v___x_780_;
}
else
{
lean_object* v_ref_781_; lean_object* v_quotContext_782_; lean_object* v_currMacroScope_783_; lean_object* v_v_784_; lean_object* v___x_785_; lean_object* v_bs_x27_786_; uint8_t v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; size_t v___x_803_; size_t v___x_804_; lean_object* v___x_805_; 
v_ref_781_ = lean_ctor_get(v___y_777_, 5);
v_quotContext_782_ = lean_ctor_get(v___y_777_, 10);
v_currMacroScope_783_ = lean_ctor_get(v___y_777_, 11);
v_v_784_ = lean_array_uget(v_bs_776_, v_i_775_);
v___x_785_ = lean_unsigned_to_nat(0u);
v_bs_x27_786_ = lean_array_uset(v_bs_776_, v_i_775_, v___x_785_);
v___x_787_ = 0;
v___x_788_ = l_Lean_SourceInfo_fromRef(v_ref_781_, v___x_787_);
v___x_789_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__6));
v___x_790_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__1);
v___x_791_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__3));
lean_inc(v_currMacroScope_783_);
lean_inc(v_quotContext_782_);
v___x_792_ = l_Lean_addMacroScope(v_quotContext_782_, v___x_791_, v_currMacroScope_783_);
v___x_793_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__7));
lean_inc(v___x_788_);
v___x_794_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_794_, 0, v___x_788_);
lean_ctor_set(v___x_794_, 1, v___x_790_);
lean_ctor_set(v___x_794_, 2, v___x_792_);
lean_ctor_set(v___x_794_, 3, v___x_793_);
v___x_795_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__7));
lean_inc(v___x_788_);
v___x_796_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_788_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_798_ = lean_mk_syntax_ident(v_v_784_);
lean_inc(v___x_788_);
v___x_799_ = l_Lean_Syntax_node1(v___x_788_, v___x_797_, v___x_798_);
v___x_800_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__10));
lean_inc(v___x_788_);
v___x_801_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_801_, 0, v___x_788_);
lean_ctor_set(v___x_801_, 1, v___x_800_);
v___x_802_ = l_Lean_Syntax_node4(v___x_788_, v___x_789_, v___x_794_, v___x_796_, v___x_799_, v___x_801_);
v___x_803_ = ((size_t)1ULL);
v___x_804_ = lean_usize_add(v_i_775_, v___x_803_);
v___x_805_ = lean_array_uset(v_bs_x27_786_, v_i_775_, v___x_802_);
v_i_775_ = v___x_804_;
v_bs_776_ = v___x_805_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___boxed(lean_object* v_sz_807_, lean_object* v_i_808_, lean_object* v_bs_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
size_t v_sz_boxed_812_; size_t v_i_boxed_813_; lean_object* v_res_814_; 
v_sz_boxed_812_ = lean_unbox_usize(v_sz_807_);
lean_dec(v_sz_807_);
v_i_boxed_813_ = lean_unbox_usize(v_i_808_);
lean_dec(v_i_808_);
v_res_814_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg(v_sz_boxed_812_, v_i_boxed_813_, v_bs_809_, v___y_810_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr(lean_object* v_indVal_817_, lean_object* v_argNames_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_){
_start:
{
lean_object* v_toConstantVal_826_; lean_object* v_name_827_; lean_object* v_levelParams_828_; lean_object* v_type_829_; lean_object* v___x_830_; size_t v_sz_831_; size_t v___x_832_; lean_object* v___x_833_; 
v_toConstantVal_826_ = lean_ctor_get(v_indVal_817_, 0);
lean_inc_ref(v_toConstantVal_826_);
lean_dec_ref(v_indVal_817_);
v_name_827_ = lean_ctor_get(v_toConstantVal_826_, 0);
lean_inc(v_name_827_);
v_levelParams_828_ = lean_ctor_get(v_toConstantVal_826_, 1);
lean_inc(v_levelParams_828_);
v_type_829_ = lean_ctor_get(v_toConstantVal_826_, 2);
lean_inc_ref(v_type_829_);
lean_dec_ref(v_toConstantVal_826_);
v___x_830_ = lean_array_mk(v_levelParams_828_);
v_sz_831_ = lean_array_size(v___x_830_);
v___x_832_ = ((size_t)0ULL);
lean_inc_ref(v_a_823_);
v___x_833_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg(v_sz_831_, v___x_832_, v___x_830_, v_a_823_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v_a_834_; lean_object* v___x_835_; lean_object* v___f_836_; uint8_t v___x_837_; lean_object* v___x_838_; 
v_a_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc(v_a_834_);
lean_dec_ref(v___x_833_);
v___x_835_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___boxed__const__1));
v___f_836_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___boxed), 13, 4);
lean_closure_set(v___f_836_, 0, v_argNames_818_);
lean_closure_set(v___f_836_, 1, v___x_835_);
lean_closure_set(v___f_836_, 2, v_name_827_);
lean_closure_set(v___f_836_, 3, v_a_834_);
v___x_837_ = 0;
v___x_838_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg(v_type_829_, v___f_836_, v___x_837_, v___x_837_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_);
return v___x_838_;
}
else
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_846_; 
lean_dec_ref(v_type_829_);
lean_dec(v_name_827_);
lean_dec(v_a_824_);
lean_dec_ref(v_a_823_);
lean_dec(v_a_822_);
lean_dec_ref(v_a_821_);
lean_dec(v_a_820_);
lean_dec_ref(v_a_819_);
lean_dec_ref(v_argNames_818_);
v_a_839_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_846_ == 0)
{
v___x_841_ = v___x_833_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_833_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_842_ == 0)
{
v___x_844_ = v___x_841_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_a_839_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___boxed(lean_object* v_indVal_847_, lean_object* v_argNames_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr(v_indVal_847_, v_argNames_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0(size_t v_sz_857_, size_t v_i_858_, lean_object* v_bs_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg(v_sz_857_, v_i_858_, v_bs_859_, v___y_864_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___boxed(lean_object* v_sz_868_, lean_object* v_i_869_, lean_object* v_bs_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
size_t v_sz_boxed_878_; size_t v_i_boxed_879_; lean_object* v_res_880_; 
v_sz_boxed_878_ = lean_unbox_usize(v_sz_868_);
lean_dec(v_sz_868_);
v_i_boxed_879_ = lean_unbox_usize(v_i_869_);
lean_dec(v_i_869_);
v_res_880_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0(v_sz_boxed_878_, v_i_boxed_879_, v_bs_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
lean_dec(v___y_876_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1(lean_object* v_as_881_, size_t v_sz_882_, size_t v_i_883_, lean_object* v_b_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg(v_as_881_, v_sz_882_, v_i_883_, v_b_884_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___boxed(lean_object* v_as_893_, lean_object* v_sz_894_, lean_object* v_i_895_, lean_object* v_b_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
size_t v_sz_boxed_904_; size_t v_i_boxed_905_; lean_object* v_res_906_; 
v_sz_boxed_904_ = lean_unbox_usize(v_sz_894_);
lean_dec(v_sz_894_);
v_i_boxed_905_ = lean_unbox_usize(v_i_895_);
lean_dec(v_i_895_);
v_res_906_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1(v_as_893_, v_sz_boxed_904_, v_i_boxed_905_, v_b_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec_ref(v_as_893_);
return v_res_906_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_914_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__2));
v___x_915_ = l_String_toRawSubstring_x27(v___x_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg(size_t v_sz_918_, size_t v_i_919_, lean_object* v_bs_920_, lean_object* v___y_921_){
_start:
{
uint8_t v___x_923_; 
v___x_923_ = lean_usize_dec_lt(v_i_919_, v_sz_918_);
if (v___x_923_ == 0)
{
lean_object* v___x_924_; 
lean_dec_ref(v___y_921_);
v___x_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_924_, 0, v_bs_920_);
return v___x_924_;
}
else
{
lean_object* v_ref_925_; lean_object* v_quotContext_926_; lean_object* v_currMacroScope_927_; lean_object* v_v_928_; lean_object* v___x_929_; lean_object* v_bs_x27_930_; uint8_t v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; size_t v___x_942_; size_t v___x_943_; lean_object* v___x_944_; 
v_ref_925_ = lean_ctor_get(v___y_921_, 5);
v_quotContext_926_ = lean_ctor_get(v___y_921_, 10);
v_currMacroScope_927_ = lean_ctor_get(v___y_921_, 11);
v_v_928_ = lean_array_uget(v_bs_920_, v_i_919_);
v___x_929_ = lean_unsigned_to_nat(0u);
v_bs_x27_930_ = lean_array_uset(v_bs_920_, v_i_919_, v___x_929_);
v___x_931_ = 0;
v___x_932_ = l_Lean_SourceInfo_fromRef(v_ref_925_, v___x_931_);
v___x_933_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__1));
v___x_934_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__2));
lean_inc(v___x_932_);
v___x_935_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_932_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__3);
v___x_937_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__4));
lean_inc(v_currMacroScope_927_);
lean_inc(v_quotContext_926_);
v___x_938_ = l_Lean_addMacroScope(v_quotContext_926_, v___x_937_, v_currMacroScope_927_);
v___x_939_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__7));
lean_inc(v___x_932_);
v___x_940_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_940_, 0, v___x_932_);
lean_ctor_set(v___x_940_, 1, v___x_936_);
lean_ctor_set(v___x_940_, 2, v___x_938_);
lean_ctor_set(v___x_940_, 3, v___x_939_);
v___x_941_ = l_Lean_Syntax_node3(v___x_932_, v___x_933_, v_v_928_, v___x_935_, v___x_940_);
v___x_942_ = ((size_t)1ULL);
v___x_943_ = lean_usize_add(v_i_919_, v___x_942_);
v___x_944_ = lean_array_uset(v_bs_x27_930_, v_i_919_, v___x_941_);
v_i_919_ = v___x_943_;
v_bs_920_ = v___x_944_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___boxed(lean_object* v_sz_946_, lean_object* v_i_947_, lean_object* v_bs_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
size_t v_sz_boxed_951_; size_t v_i_boxed_952_; lean_object* v_res_953_; 
v_sz_boxed_951_ = lean_unbox_usize(v_sz_946_);
lean_dec(v_sz_946_);
v_i_boxed_952_ = lean_unbox_usize(v_i_947_);
lean_dec(v_i_947_);
v_res_953_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg(v_sz_boxed_951_, v_i_boxed_952_, v_bs_948_, v___y_949_);
return v_res_953_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1(lean_object* v_msg_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v_toApplicative_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_1062_; 
v___x_969_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__0);
v___x_970_ = l_ReaderT_instMonad___redArg(v___x_969_);
v_toApplicative_971_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_1062_ == 0)
{
lean_object* v_unused_1063_; 
v_unused_1063_ = lean_ctor_get(v___x_970_, 1);
lean_dec(v_unused_1063_);
v___x_973_ = v___x_970_;
v_isShared_974_ = v_isSharedCheck_1062_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_toApplicative_971_);
lean_dec(v___x_970_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_1062_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v_toFunctor_975_; lean_object* v_toSeq_976_; lean_object* v_toSeqLeft_977_; lean_object* v_toSeqRight_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_1060_; 
v_toFunctor_975_ = lean_ctor_get(v_toApplicative_971_, 0);
v_toSeq_976_ = lean_ctor_get(v_toApplicative_971_, 2);
v_toSeqLeft_977_ = lean_ctor_get(v_toApplicative_971_, 3);
v_toSeqRight_978_ = lean_ctor_get(v_toApplicative_971_, 4);
v_isSharedCheck_1060_ = !lean_is_exclusive(v_toApplicative_971_);
if (v_isSharedCheck_1060_ == 0)
{
lean_object* v_unused_1061_; 
v_unused_1061_ = lean_ctor_get(v_toApplicative_971_, 1);
lean_dec(v_unused_1061_);
v___x_980_ = v_toApplicative_971_;
v_isShared_981_ = v_isSharedCheck_1060_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_toSeqRight_978_);
lean_inc(v_toSeqLeft_977_);
lean_inc(v_toSeq_976_);
lean_inc(v_toFunctor_975_);
lean_dec(v_toApplicative_971_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_1060_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___f_982_; lean_object* v___f_983_; lean_object* v___f_984_; lean_object* v___f_985_; lean_object* v___x_986_; lean_object* v___f_987_; lean_object* v___f_988_; lean_object* v___f_989_; lean_object* v___x_991_; 
v___f_982_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__1));
v___f_983_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__2));
lean_inc_ref(v_toFunctor_975_);
v___f_984_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_984_, 0, v_toFunctor_975_);
v___f_985_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_985_, 0, v_toFunctor_975_);
v___x_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_986_, 0, v___f_984_);
lean_ctor_set(v___x_986_, 1, v___f_985_);
v___f_987_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_987_, 0, v_toSeqRight_978_);
v___f_988_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_988_, 0, v_toSeqLeft_977_);
v___f_989_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_989_, 0, v_toSeq_976_);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 4, v___f_987_);
lean_ctor_set(v___x_980_, 3, v___f_988_);
lean_ctor_set(v___x_980_, 2, v___f_989_);
lean_ctor_set(v___x_980_, 1, v___f_982_);
lean_ctor_set(v___x_980_, 0, v___x_986_);
v___x_991_ = v___x_980_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_986_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v___f_982_);
lean_ctor_set(v_reuseFailAlloc_1059_, 2, v___f_989_);
lean_ctor_set(v_reuseFailAlloc_1059_, 3, v___f_988_);
lean_ctor_set(v_reuseFailAlloc_1059_, 4, v___f_987_);
v___x_991_ = v_reuseFailAlloc_1059_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
lean_object* v___x_993_; 
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 1, v___f_983_);
lean_ctor_set(v___x_973_, 0, v___x_991_);
v___x_993_ = v___x_973_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_991_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v___f_983_);
v___x_993_ = v_reuseFailAlloc_1058_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v___x_994_; lean_object* v_toApplicative_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1056_; 
v___x_994_ = l_ReaderT_instMonad___redArg(v___x_993_);
v_toApplicative_995_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1056_ == 0)
{
lean_object* v_unused_1057_; 
v_unused_1057_ = lean_ctor_get(v___x_994_, 1);
lean_dec(v_unused_1057_);
v___x_997_ = v___x_994_;
v_isShared_998_ = v_isSharedCheck_1056_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_toApplicative_995_);
lean_dec(v___x_994_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1056_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v_toFunctor_999_; lean_object* v_toSeq_1000_; lean_object* v_toSeqLeft_1001_; lean_object* v_toSeqRight_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1054_; 
v_toFunctor_999_ = lean_ctor_get(v_toApplicative_995_, 0);
v_toSeq_1000_ = lean_ctor_get(v_toApplicative_995_, 2);
v_toSeqLeft_1001_ = lean_ctor_get(v_toApplicative_995_, 3);
v_toSeqRight_1002_ = lean_ctor_get(v_toApplicative_995_, 4);
v_isSharedCheck_1054_ = !lean_is_exclusive(v_toApplicative_995_);
if (v_isSharedCheck_1054_ == 0)
{
lean_object* v_unused_1055_; 
v_unused_1055_ = lean_ctor_get(v_toApplicative_995_, 1);
lean_dec(v_unused_1055_);
v___x_1004_ = v_toApplicative_995_;
v_isShared_1005_ = v_isSharedCheck_1054_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_toSeqRight_1002_);
lean_inc(v_toSeqLeft_1001_);
lean_inc(v_toSeq_1000_);
lean_inc(v_toFunctor_999_);
lean_dec(v_toApplicative_995_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1054_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___f_1006_; lean_object* v___f_1007_; lean_object* v___f_1008_; lean_object* v___f_1009_; lean_object* v___x_1010_; lean_object* v___f_1011_; lean_object* v___f_1012_; lean_object* v___f_1013_; lean_object* v___x_1015_; 
v___f_1006_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__3));
v___f_1007_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__4));
lean_inc_ref(v_toFunctor_999_);
v___f_1008_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1008_, 0, v_toFunctor_999_);
v___f_1009_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1009_, 0, v_toFunctor_999_);
v___x_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___f_1008_);
lean_ctor_set(v___x_1010_, 1, v___f_1009_);
v___f_1011_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1011_, 0, v_toSeqRight_1002_);
v___f_1012_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1012_, 0, v_toSeqLeft_1001_);
v___f_1013_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1013_, 0, v_toSeq_1000_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 4, v___f_1011_);
lean_ctor_set(v___x_1004_, 3, v___f_1012_);
lean_ctor_set(v___x_1004_, 2, v___f_1013_);
lean_ctor_set(v___x_1004_, 1, v___f_1006_);
lean_ctor_set(v___x_1004_, 0, v___x_1010_);
v___x_1015_ = v___x_1004_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1010_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v___f_1006_);
lean_ctor_set(v_reuseFailAlloc_1053_, 2, v___f_1013_);
lean_ctor_set(v_reuseFailAlloc_1053_, 3, v___f_1012_);
lean_ctor_set(v_reuseFailAlloc_1053_, 4, v___f_1011_);
v___x_1015_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
lean_object* v___x_1017_; 
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 1, v___f_1007_);
lean_ctor_set(v___x_997_, 0, v___x_1015_);
v___x_1017_ = v___x_997_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1015_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v___f_1007_);
v___x_1017_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v___x_1018_; lean_object* v_toApplicative_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1050_; 
v___x_1018_ = l_ReaderT_instMonad___redArg(v___x_1017_);
v_toApplicative_1019_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1050_ == 0)
{
lean_object* v_unused_1051_; 
v_unused_1051_ = lean_ctor_get(v___x_1018_, 1);
lean_dec(v_unused_1051_);
v___x_1021_ = v___x_1018_;
v_isShared_1022_ = v_isSharedCheck_1050_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_toApplicative_1019_);
lean_dec(v___x_1018_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1050_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v_toFunctor_1023_; lean_object* v_toSeq_1024_; lean_object* v_toSeqLeft_1025_; lean_object* v_toSeqRight_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1048_; 
v_toFunctor_1023_ = lean_ctor_get(v_toApplicative_1019_, 0);
v_toSeq_1024_ = lean_ctor_get(v_toApplicative_1019_, 2);
v_toSeqLeft_1025_ = lean_ctor_get(v_toApplicative_1019_, 3);
v_toSeqRight_1026_ = lean_ctor_get(v_toApplicative_1019_, 4);
v_isSharedCheck_1048_ = !lean_is_exclusive(v_toApplicative_1019_);
if (v_isSharedCheck_1048_ == 0)
{
lean_object* v_unused_1049_; 
v_unused_1049_ = lean_ctor_get(v_toApplicative_1019_, 1);
lean_dec(v_unused_1049_);
v___x_1028_ = v_toApplicative_1019_;
v_isShared_1029_ = v_isSharedCheck_1048_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_toSeqRight_1026_);
lean_inc(v_toSeqLeft_1025_);
lean_inc(v_toSeq_1024_);
lean_inc(v_toFunctor_1023_);
lean_dec(v_toApplicative_1019_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1048_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___f_1030_; lean_object* v___f_1031_; lean_object* v___f_1032_; lean_object* v___f_1033_; lean_object* v___x_1034_; lean_object* v___f_1035_; lean_object* v___f_1036_; lean_object* v___f_1037_; lean_object* v___x_1039_; 
v___f_1030_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__5));
v___f_1031_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__6));
lean_inc_ref(v_toFunctor_1023_);
v___f_1032_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1032_, 0, v_toFunctor_1023_);
v___f_1033_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1033_, 0, v_toFunctor_1023_);
v___x_1034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___f_1032_);
lean_ctor_set(v___x_1034_, 1, v___f_1033_);
v___f_1035_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1035_, 0, v_toSeqRight_1026_);
v___f_1036_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1036_, 0, v_toSeqLeft_1025_);
v___f_1037_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1037_, 0, v_toSeq_1024_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 4, v___f_1035_);
lean_ctor_set(v___x_1028_, 3, v___f_1036_);
lean_ctor_set(v___x_1028_, 2, v___f_1037_);
lean_ctor_set(v___x_1028_, 1, v___f_1030_);
lean_ctor_set(v___x_1028_, 0, v___x_1034_);
v___x_1039_ = v___x_1028_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1034_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v___f_1030_);
lean_ctor_set(v_reuseFailAlloc_1047_, 2, v___f_1037_);
lean_ctor_set(v_reuseFailAlloc_1047_, 3, v___f_1036_);
lean_ctor_set(v_reuseFailAlloc_1047_, 4, v___f_1035_);
v___x_1039_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
lean_object* v___x_1041_; 
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 1, v___f_1031_);
lean_ctor_set(v___x_1021_, 0, v___x_1039_);
v___x_1041_ = v___x_1021_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1046_, 1, v___f_1031_);
v___x_1041_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_27594__overap_1044_; lean_object* v___x_1045_; 
v___x_1042_ = lean_box(0);
v___x_1043_ = l_instInhabitedOfMonad___redArg(v___x_1041_, v___x_1042_);
v___x_27594__overap_1044_ = lean_panic_fn(v___x_1043_, v_msg_961_);
v___x_1045_ = lean_apply_7(v___x_27594__overap_1044_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, lean_box(0));
return v___x_1045_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___boxed(lean_object* v_msg_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1(v_msg_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_);
return v_res_1072_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__0));
v___x_1075_ = l_Lean_stringToMessageData(v___x_1074_);
return v___x_1075_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__3(void){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__2));
v___x_1078_ = l_Lean_stringToMessageData(v___x_1077_);
return v___x_1078_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__7(void){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1082_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__6));
v___x_1083_ = lean_unsigned_to_nat(11u);
v___x_1084_ = lean_unsigned_to_nat(122u);
v___x_1085_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__5));
v___x_1086_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__4));
v___x_1087_ = l_mkPanicMessageWithDecl(v___x_1086_, v___x_1085_, v___x_1084_, v___x_1083_, v___x_1082_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1(lean_object* v_constName_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v___x_1104_; lean_object* v_env_1105_; uint8_t v___x_1106_; lean_object* v___x_1107_; 
v___x_1104_ = lean_st_ref_get(v___y_1094_);
v_env_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc_ref(v_env_1105_);
lean_dec(v___x_1104_);
v___x_1106_ = 0;
lean_inc(v_constName_1088_);
v___x_1107_ = l_Lean_Environment_findAsync_x3f(v_env_1105_, v_constName_1088_, v___x_1106_);
if (lean_obj_tag(v___x_1107_) == 1)
{
lean_object* v_val_1108_; uint8_t v_kind_1109_; 
v_val_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_val_1108_);
lean_dec_ref(v___x_1107_);
v_kind_1109_ = lean_ctor_get_uint8(v_val_1108_, sizeof(void*)*3);
if (v_kind_1109_ == 6)
{
lean_object* v___x_1110_; 
v___x_1110_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1108_);
if (lean_obj_tag(v___x_1110_) == 6)
{
lean_object* v_val_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v_constName_1088_);
v_val_1111_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1110_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_val_1111_);
lean_dec(v___x_1110_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
lean_ctor_set_tag(v___x_1113_, 0);
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_val_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
else
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
lean_dec_ref(v___x_1110_);
v___x_1119_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__7, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__7);
lean_inc(v___y_1094_);
lean_inc_ref(v___y_1093_);
lean_inc(v___y_1092_);
lean_inc_ref(v___y_1091_);
lean_inc(v___y_1090_);
lean_inc_ref(v___y_1089_);
v___x_1120_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1(v___x_1119_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1129_; 
v_a_1121_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1123_ = v___x_1120_;
v_isShared_1124_ = v_isSharedCheck_1129_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1120_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1129_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
if (lean_obj_tag(v_a_1121_) == 0)
{
lean_del_object(v___x_1123_);
goto v___jp_1096_;
}
else
{
lean_object* v_val_1125_; lean_object* v___x_1127_; 
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v_constName_1088_);
v_val_1125_ = lean_ctor_get(v_a_1121_, 0);
lean_inc(v_val_1125_);
lean_dec_ref(v_a_1121_);
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 0, v_val_1125_);
v___x_1127_ = v___x_1123_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_val_1125_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
else
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v_constName_1088_);
v_a_1130_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___x_1120_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1120_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1130_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
}
else
{
lean_dec(v_val_1108_);
goto v___jp_1096_;
}
}
else
{
lean_dec(v___x_1107_);
goto v___jp_1096_;
}
v___jp_1096_:
{
lean_object* v___x_1097_; uint8_t v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1097_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__1);
v___x_1098_ = 0;
v___x_1099_ = l_Lean_MessageData_ofConstName(v_constName_1088_, v___x_1098_);
v___x_1100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1097_);
lean_ctor_set(v___x_1100_, 1, v___x_1099_);
v___x_1101_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__3, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__3);
v___x_1102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1100_);
lean_ctor_set(v___x_1102_, 1, v___x_1101_);
v___x_1103_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v___x_1102_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v___y_1090_);
return v___x_1103_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___boxed(lean_object* v_constName_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1(v_constName_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__0(lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v_ref_1154_; uint8_t v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v_ref_1154_ = lean_ctor_get(v___y_1151_, 5);
v___x_1155_ = 0;
v___x_1156_ = l_Lean_SourceInfo_fromRef(v_ref_1154_, v___x_1155_);
v___x_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__0___boxed(lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__0(v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg(lean_object* v_upperBound_1173_, lean_object* v_a_1174_, lean_object* v_b_1175_, lean_object* v___y_1176_){
_start:
{
uint8_t v___x_1178_; 
v___x_1178_ = lean_nat_dec_lt(v_a_1174_, v_upperBound_1173_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; 
lean_dec(v_a_1174_);
v___x_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1179_, 0, v_b_1175_);
return v___x_1179_;
}
else
{
lean_object* v_ref_1180_; uint8_t v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v_ref_1180_ = lean_ctor_get(v___y_1176_, 5);
v___x_1181_ = 0;
v___x_1182_ = l_Lean_SourceInfo_fromRef(v_ref_1180_, v___x_1181_);
v___x_1183_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__1));
v___x_1184_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__2));
lean_inc(v___x_1182_);
v___x_1185_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1182_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
v___x_1186_ = l_Lean_Syntax_node1(v___x_1182_, v___x_1183_, v___x_1185_);
v___x_1187_ = lean_array_push(v_b_1175_, v___x_1186_);
v___x_1188_ = lean_unsigned_to_nat(1u);
v___x_1189_ = lean_nat_add(v_a_1174_, v___x_1188_);
lean_dec(v_a_1174_);
v_a_1174_ = v___x_1189_;
v_b_1175_ = v___x_1187_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___boxed(lean_object* v_upperBound_1191_, lean_object* v_a_1192_, lean_object* v_b_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg(v_upperBound_1191_, v_a_1192_, v_b_1193_, v___y_1194_);
lean_dec_ref(v___y_1194_);
lean_dec(v_upperBound_1191_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6___redArg(lean_object* v_upperBound_1197_, lean_object* v_header_1198_, lean_object* v_xs_1199_, lean_object* v_indVal_1200_, lean_object* v_auxFunName_1201_, lean_object* v_levelInsts_1202_, lean_object* v_a_1203_, lean_object* v_b_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
uint8_t v___x_1210_; 
v___x_1210_ = lean_nat_dec_lt(v_a_1203_, v_upperBound_1197_);
if (v___x_1210_ == 0)
{
lean_object* v___x_1211_; 
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v_a_1203_);
lean_dec(v_auxFunName_1201_);
lean_dec_ref(v_indVal_1200_);
v___x_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1211_, 0, v_b_1204_);
return v___x_1211_;
}
else
{
lean_object* v_argNames_1212_; lean_object* v_ref_1213_; lean_object* v_quotContext_1214_; lean_object* v_currMacroScope_1215_; lean_object* v_a_1217_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v_argNames_1212_ = lean_ctor_get(v_header_1198_, 1);
v_ref_1213_ = lean_ctor_get(v___y_1207_, 5);
v_quotContext_1214_ = lean_ctor_get(v___y_1207_, 10);
v_currMacroScope_1215_ = lean_ctor_get(v___y_1207_, 11);
v___x_1238_ = l_Lean_instInhabitedExpr;
v___x_1239_ = lean_array_get_borrowed(v___x_1238_, v_xs_1199_, v_a_1203_);
lean_inc(v___y_1208_);
lean_inc_ref(v___y_1207_);
lean_inc(v___y_1206_);
lean_inc_ref(v___y_1205_);
lean_inc(v___x_1239_);
v___x_1240_ = lean_infer_type(v___x_1239_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_toConstantVal_1241_; lean_object* v_a_1242_; lean_object* v_name_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1295_; 
v_toConstantVal_1241_ = lean_ctor_get(v_indVal_1200_, 0);
lean_inc_ref(v_toConstantVal_1241_);
v_a_1242_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_a_1242_);
lean_dec_ref(v___x_1240_);
v_name_1243_ = lean_ctor_get(v_toConstantVal_1241_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v_toConstantVal_1241_);
if (v_isSharedCheck_1295_ == 0)
{
lean_object* v_unused_1296_; lean_object* v_unused_1297_; 
v_unused_1296_ = lean_ctor_get(v_toConstantVal_1241_, 2);
lean_dec(v_unused_1296_);
v_unused_1297_ = lean_ctor_get(v_toConstantVal_1241_, 1);
lean_dec(v_unused_1297_);
v___x_1245_ = v_toConstantVal_1241_;
v_isShared_1246_ = v_isSharedCheck_1295_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_name_1243_);
lean_dec(v_toConstantVal_1241_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1295_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; uint8_t v___x_1250_; 
v___x_1247_ = lean_box(0);
v___x_1248_ = lean_array_get_borrowed(v___x_1247_, v_argNames_1212_, v_a_1203_);
lean_inc(v___x_1248_);
v___x_1249_ = lean_mk_syntax_ident(v___x_1248_);
v___x_1250_ = l_Lean_Expr_isAppOf(v_a_1242_, v_name_1243_);
lean_dec(v_name_1243_);
lean_dec(v_a_1242_);
if (v___x_1250_ == 0)
{
lean_object* v___x_1251_; 
lean_del_object(v___x_1245_);
lean_inc(v___y_1208_);
lean_inc_ref(v___y_1207_);
lean_inc(v___y_1206_);
lean_inc_ref(v___y_1205_);
lean_inc(v___x_1239_);
v___x_1251_ = l_Lean_Meta_isType(v___x_1239_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v_a_1252_; uint8_t v___x_1253_; 
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_a_1252_);
lean_dec_ref(v___x_1251_);
v___x_1253_ = lean_unbox(v_a_1252_);
if (v___x_1253_ == 0)
{
uint8_t v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1254_ = lean_unbox(v_a_1252_);
lean_dec(v_a_1252_);
v___x_1255_ = l_Lean_SourceInfo_fromRef(v_ref_1213_, v___x_1254_);
v___x_1256_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1257_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1);
v___x_1258_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__2));
lean_inc(v_currMacroScope_1215_);
lean_inc(v_quotContext_1214_);
v___x_1259_ = l_Lean_addMacroScope(v_quotContext_1214_, v___x_1258_, v_currMacroScope_1215_);
v___x_1260_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__6));
lean_inc(v___x_1255_);
v___x_1261_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1255_);
lean_ctor_set(v___x_1261_, 1, v___x_1257_);
lean_ctor_set(v___x_1261_, 2, v___x_1259_);
lean_ctor_set(v___x_1261_, 3, v___x_1260_);
v___x_1262_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
lean_inc(v___x_1255_);
v___x_1263_ = l_Lean_Syntax_node1(v___x_1255_, v___x_1262_, v___x_1249_);
v___x_1264_ = l_Lean_Syntax_node2(v___x_1255_, v___x_1256_, v___x_1261_, v___x_1263_);
v_a_1217_ = v___x_1264_;
goto v___jp_1216_;
}
else
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
lean_dec(v_a_1252_);
v___x_1265_ = l_Lean_SourceInfo_fromRef(v_ref_1213_, v___x_1250_);
v___x_1266_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1267_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8);
v___x_1268_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__9));
lean_inc(v_currMacroScope_1215_);
lean_inc(v_quotContext_1214_);
v___x_1269_ = l_Lean_addMacroScope(v_quotContext_1214_, v___x_1268_, v_currMacroScope_1215_);
v___x_1270_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__12));
lean_inc(v___x_1265_);
v___x_1271_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1265_);
lean_ctor_set(v___x_1271_, 1, v___x_1267_);
lean_ctor_set(v___x_1271_, 2, v___x_1269_);
lean_ctor_set(v___x_1271_, 3, v___x_1270_);
v___x_1272_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
lean_inc(v___x_1265_);
v___x_1273_ = l_Lean_Syntax_node1(v___x_1265_, v___x_1272_, v___x_1249_);
v___x_1274_ = l_Lean_Syntax_node2(v___x_1265_, v___x_1266_, v___x_1271_, v___x_1273_);
v_a_1217_ = v___x_1274_;
goto v___jp_1216_;
}
}
else
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1282_; 
lean_dec(v___x_1249_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec_ref(v_b_1204_);
lean_dec(v_a_1203_);
lean_dec(v_auxFunName_1201_);
lean_dec_ref(v_indVal_1200_);
v_a_1275_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1277_ = v___x_1251_;
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1251_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_a_1275_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
}
else
{
uint8_t v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1292_; 
v___x_1283_ = 0;
v___x_1284_ = l_Lean_SourceInfo_fromRef(v_ref_1213_, v___x_1283_);
v___x_1285_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
lean_inc(v_auxFunName_1201_);
v___x_1286_ = lean_mk_syntax_ident(v_auxFunName_1201_);
v___x_1287_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1288_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_1289_ = l_Array_append___redArg(v___x_1288_, v_levelInsts_1202_);
v___x_1290_ = lean_array_push(v___x_1289_, v___x_1249_);
lean_inc(v___x_1284_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set_tag(v___x_1245_, 1);
lean_ctor_set(v___x_1245_, 2, v___x_1290_);
lean_ctor_set(v___x_1245_, 1, v___x_1287_);
lean_ctor_set(v___x_1245_, 0, v___x_1284_);
v___x_1292_ = v___x_1245_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1284_);
lean_ctor_set(v_reuseFailAlloc_1294_, 1, v___x_1287_);
lean_ctor_set(v_reuseFailAlloc_1294_, 2, v___x_1290_);
v___x_1292_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
lean_object* v___x_1293_; 
v___x_1293_ = l_Lean_Syntax_node2(v___x_1284_, v___x_1285_, v___x_1286_, v___x_1292_);
v_a_1217_ = v___x_1293_;
goto v___jp_1216_;
}
}
}
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec_ref(v_b_1204_);
lean_dec(v_a_1203_);
lean_dec(v_auxFunName_1201_);
lean_dec_ref(v_indVal_1200_);
v_a_1298_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1240_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1240_);
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
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1298_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
v___jp_1216_:
{
lean_object* v_fst_1218_; lean_object* v_snd_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1237_; 
v_fst_1218_ = lean_ctor_get(v_b_1204_, 0);
v_snd_1219_ = lean_ctor_get(v_b_1204_, 1);
v_isSharedCheck_1237_ = !lean_is_exclusive(v_b_1204_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1221_ = v_b_1204_;
v_isShared_1222_ = v_isSharedCheck_1237_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_snd_1219_);
lean_inc(v_fst_1218_);
lean_dec(v_b_1204_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1237_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
uint8_t v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1232_; 
v___x_1223_ = 0;
v___x_1224_ = l_Lean_SourceInfo_fromRef(v_ref_1213_, v___x_1223_);
v___x_1225_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__2));
lean_inc(v___x_1224_);
v___x_1226_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1224_);
lean_ctor_set(v___x_1226_, 1, v___x_1225_);
v___x_1227_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__1));
v___x_1228_ = l_Lean_Syntax_node1(v___x_1224_, v___x_1227_, v___x_1226_);
v___x_1229_ = lean_array_push(v_fst_1218_, v___x_1228_);
v___x_1230_ = lean_array_push(v_snd_1219_, v_a_1217_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 1, v___x_1230_);
lean_ctor_set(v___x_1221_, 0, v___x_1229_);
v___x_1232_ = v___x_1221_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1229_);
lean_ctor_set(v_reuseFailAlloc_1236_, 1, v___x_1230_);
v___x_1232_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1233_ = lean_unsigned_to_nat(1u);
v___x_1234_ = lean_nat_add(v_a_1203_, v___x_1233_);
lean_dec(v_a_1203_);
v_a_1203_ = v___x_1234_;
v_b_1204_ = v___x_1232_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6___redArg___boxed(lean_object* v_upperBound_1306_, lean_object* v_header_1307_, lean_object* v_xs_1308_, lean_object* v_indVal_1309_, lean_object* v_auxFunName_1310_, lean_object* v_levelInsts_1311_, lean_object* v_a_1312_, lean_object* v_b_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6___redArg(v_upperBound_1306_, v_header_1307_, v_xs_1308_, v_indVal_1309_, v_auxFunName_1310_, v_levelInsts_1311_, v_a_1312_, v_b_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
lean_dec_ref(v_levelInsts_1311_);
lean_dec_ref(v_xs_1308_);
lean_dec_ref(v_header_1307_);
lean_dec(v_upperBound_1306_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4___redArg(lean_object* v_upperBound_1320_, lean_object* v_header_1321_, lean_object* v_xs_1322_, lean_object* v_indVal_1323_, lean_object* v_auxFunName_1324_, lean_object* v_levelInsts_1325_, lean_object* v_a_1326_, lean_object* v_b_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
uint8_t v___x_1335_; 
v___x_1335_ = lean_nat_dec_lt(v_a_1326_, v_upperBound_1320_);
if (v___x_1335_ == 0)
{
lean_object* v___x_1336_; 
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v_auxFunName_1324_);
lean_dec_ref(v_indVal_1323_);
v___x_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1336_, 0, v_b_1327_);
return v___x_1336_;
}
else
{
lean_object* v_argNames_1337_; lean_object* v_ref_1338_; lean_object* v_quotContext_1339_; lean_object* v_currMacroScope_1340_; lean_object* v_a_1342_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v_argNames_1337_ = lean_ctor_get(v_header_1321_, 1);
v_ref_1338_ = lean_ctor_get(v___y_1332_, 5);
v_quotContext_1339_ = lean_ctor_get(v___y_1332_, 10);
v_currMacroScope_1340_ = lean_ctor_get(v___y_1332_, 11);
v___x_1363_ = l_Lean_instInhabitedExpr;
v___x_1364_ = lean_array_get_borrowed(v___x_1363_, v_xs_1322_, v_a_1326_);
lean_inc(v___y_1333_);
lean_inc_ref(v___y_1332_);
lean_inc(v___y_1331_);
lean_inc_ref(v___y_1330_);
lean_inc(v___x_1364_);
v___x_1365_ = lean_infer_type(v___x_1364_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_toConstantVal_1366_; lean_object* v_a_1367_; lean_object* v_name_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1420_; 
v_toConstantVal_1366_ = lean_ctor_get(v_indVal_1323_, 0);
lean_inc_ref(v_toConstantVal_1366_);
v_a_1367_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_a_1367_);
lean_dec_ref(v___x_1365_);
v_name_1368_ = lean_ctor_get(v_toConstantVal_1366_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v_toConstantVal_1366_);
if (v_isSharedCheck_1420_ == 0)
{
lean_object* v_unused_1421_; lean_object* v_unused_1422_; 
v_unused_1421_ = lean_ctor_get(v_toConstantVal_1366_, 2);
lean_dec(v_unused_1421_);
v_unused_1422_ = lean_ctor_get(v_toConstantVal_1366_, 1);
lean_dec(v_unused_1422_);
v___x_1370_ = v_toConstantVal_1366_;
v_isShared_1371_ = v_isSharedCheck_1420_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_name_1368_);
lean_dec(v_toConstantVal_1366_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1420_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; uint8_t v___x_1375_; 
v___x_1372_ = lean_box(0);
v___x_1373_ = lean_array_get_borrowed(v___x_1372_, v_argNames_1337_, v_a_1326_);
lean_inc(v___x_1373_);
v___x_1374_ = lean_mk_syntax_ident(v___x_1373_);
v___x_1375_ = l_Lean_Expr_isAppOf(v_a_1367_, v_name_1368_);
lean_dec(v_name_1368_);
lean_dec(v_a_1367_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1376_; 
lean_del_object(v___x_1370_);
lean_inc(v___y_1333_);
lean_inc_ref(v___y_1332_);
lean_inc(v___y_1331_);
lean_inc_ref(v___y_1330_);
lean_inc(v___x_1364_);
v___x_1376_ = l_Lean_Meta_isType(v___x_1364_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; uint8_t v___x_1378_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_a_1377_);
lean_dec_ref(v___x_1376_);
v___x_1378_ = lean_unbox(v_a_1377_);
if (v___x_1378_ == 0)
{
uint8_t v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1379_ = lean_unbox(v_a_1377_);
lean_dec(v_a_1377_);
v___x_1380_ = l_Lean_SourceInfo_fromRef(v_ref_1338_, v___x_1379_);
v___x_1381_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1382_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1);
v___x_1383_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__2));
lean_inc(v_currMacroScope_1340_);
lean_inc(v_quotContext_1339_);
v___x_1384_ = l_Lean_addMacroScope(v_quotContext_1339_, v___x_1383_, v_currMacroScope_1340_);
v___x_1385_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__6));
lean_inc(v___x_1380_);
v___x_1386_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1380_);
lean_ctor_set(v___x_1386_, 1, v___x_1382_);
lean_ctor_set(v___x_1386_, 2, v___x_1384_);
lean_ctor_set(v___x_1386_, 3, v___x_1385_);
v___x_1387_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
lean_inc(v___x_1380_);
v___x_1388_ = l_Lean_Syntax_node1(v___x_1380_, v___x_1387_, v___x_1374_);
v___x_1389_ = l_Lean_Syntax_node2(v___x_1380_, v___x_1381_, v___x_1386_, v___x_1388_);
v_a_1342_ = v___x_1389_;
goto v___jp_1341_;
}
else
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
lean_dec(v_a_1377_);
v___x_1390_ = l_Lean_SourceInfo_fromRef(v_ref_1338_, v___x_1375_);
v___x_1391_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1392_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8);
v___x_1393_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__9));
lean_inc(v_currMacroScope_1340_);
lean_inc(v_quotContext_1339_);
v___x_1394_ = l_Lean_addMacroScope(v_quotContext_1339_, v___x_1393_, v_currMacroScope_1340_);
v___x_1395_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__12));
lean_inc(v___x_1390_);
v___x_1396_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1390_);
lean_ctor_set(v___x_1396_, 1, v___x_1392_);
lean_ctor_set(v___x_1396_, 2, v___x_1394_);
lean_ctor_set(v___x_1396_, 3, v___x_1395_);
v___x_1397_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
lean_inc(v___x_1390_);
v___x_1398_ = l_Lean_Syntax_node1(v___x_1390_, v___x_1397_, v___x_1374_);
v___x_1399_ = l_Lean_Syntax_node2(v___x_1390_, v___x_1391_, v___x_1396_, v___x_1398_);
v_a_1342_ = v___x_1399_;
goto v___jp_1341_;
}
}
else
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
lean_dec(v___x_1374_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec_ref(v_b_1327_);
lean_dec(v_auxFunName_1324_);
lean_dec_ref(v_indVal_1323_);
v_a_1400_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v___x_1376_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1376_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1400_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
else
{
uint8_t v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1417_; 
v___x_1408_ = 0;
v___x_1409_ = l_Lean_SourceInfo_fromRef(v_ref_1338_, v___x_1408_);
v___x_1410_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
lean_inc(v_auxFunName_1324_);
v___x_1411_ = lean_mk_syntax_ident(v_auxFunName_1324_);
v___x_1412_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1413_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_1414_ = l_Array_append___redArg(v___x_1413_, v_levelInsts_1325_);
v___x_1415_ = lean_array_push(v___x_1414_, v___x_1374_);
lean_inc(v___x_1409_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set_tag(v___x_1370_, 1);
lean_ctor_set(v___x_1370_, 2, v___x_1415_);
lean_ctor_set(v___x_1370_, 1, v___x_1412_);
lean_ctor_set(v___x_1370_, 0, v___x_1409_);
v___x_1417_ = v___x_1370_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1409_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v___x_1412_);
lean_ctor_set(v_reuseFailAlloc_1419_, 2, v___x_1415_);
v___x_1417_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_object* v___x_1418_; 
v___x_1418_ = l_Lean_Syntax_node2(v___x_1409_, v___x_1410_, v___x_1411_, v___x_1417_);
v_a_1342_ = v___x_1418_;
goto v___jp_1341_;
}
}
}
}
else
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1430_; 
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec_ref(v_b_1327_);
lean_dec(v_auxFunName_1324_);
lean_dec_ref(v_indVal_1323_);
v_a_1423_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1425_ = v___x_1365_;
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1365_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1428_; 
if (v_isShared_1426_ == 0)
{
v___x_1428_ = v___x_1425_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_a_1423_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
v___jp_1341_:
{
lean_object* v_fst_1343_; lean_object* v_snd_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1362_; 
v_fst_1343_ = lean_ctor_get(v_b_1327_, 0);
v_snd_1344_ = lean_ctor_get(v_b_1327_, 1);
v_isSharedCheck_1362_ = !lean_is_exclusive(v_b_1327_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1346_ = v_b_1327_;
v_isShared_1347_ = v_isSharedCheck_1362_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_snd_1344_);
lean_inc(v_fst_1343_);
lean_dec(v_b_1327_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1362_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
uint8_t v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1357_; 
v___x_1348_ = 0;
v___x_1349_ = l_Lean_SourceInfo_fromRef(v_ref_1338_, v___x_1348_);
v___x_1350_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__2));
lean_inc(v___x_1349_);
v___x_1351_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1349_);
lean_ctor_set(v___x_1351_, 1, v___x_1350_);
v___x_1352_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__1));
v___x_1353_ = l_Lean_Syntax_node1(v___x_1349_, v___x_1352_, v___x_1351_);
v___x_1354_ = lean_array_push(v_fst_1343_, v___x_1353_);
v___x_1355_ = lean_array_push(v_snd_1344_, v_a_1342_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 1, v___x_1355_);
lean_ctor_set(v___x_1346_, 0, v___x_1354_);
v___x_1357_ = v___x_1346_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1354_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v___x_1355_);
v___x_1357_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1358_ = lean_unsigned_to_nat(1u);
v___x_1359_ = lean_nat_add(v_a_1326_, v___x_1358_);
v___x_1360_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6___redArg(v_upperBound_1320_, v_header_1321_, v_xs_1322_, v_indVal_1323_, v_auxFunName_1324_, v_levelInsts_1325_, v___x_1359_, v___x_1357_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
return v___x_1360_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4___redArg___boxed(lean_object* v_upperBound_1431_, lean_object* v_header_1432_, lean_object* v_xs_1433_, lean_object* v_indVal_1434_, lean_object* v_auxFunName_1435_, lean_object* v_levelInsts_1436_, lean_object* v_a_1437_, lean_object* v_b_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4___redArg(v_upperBound_1431_, v_header_1432_, v_xs_1433_, v_indVal_1434_, v_auxFunName_1435_, v_levelInsts_1436_, v_a_1437_, v_b_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v_a_1437_);
lean_dec_ref(v_levelInsts_1436_);
lean_dec_ref(v_xs_1433_);
lean_dec_ref(v_header_1432_);
lean_dec(v_upperBound_1431_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg(lean_object* v_upperBound_1450_, lean_object* v___x_1451_, lean_object* v_xs_1452_, lean_object* v_indVal_1453_, lean_object* v_auxFunName_1454_, lean_object* v_levelInsts_1455_, lean_object* v_a_1456_, lean_object* v_b_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
uint8_t v___x_1463_; 
v___x_1463_ = lean_nat_dec_lt(v_a_1456_, v_upperBound_1450_);
if (v___x_1463_ == 0)
{
lean_object* v___x_1464_; 
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v_a_1456_);
lean_dec(v_auxFunName_1454_);
lean_dec_ref(v_indVal_1453_);
v___x_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1464_, 0, v_b_1457_);
return v___x_1464_;
}
else
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1465_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg___closed__1));
lean_inc(v___y_1461_);
lean_inc_ref(v___y_1460_);
v___x_1466_ = l_Lean_Core_mkFreshUserName(v___x_1465_, v___y_1460_, v___y_1461_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_a_1467_; lean_object* v_fst_1468_; lean_object* v_snd_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1557_; 
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_a_1467_);
lean_dec_ref(v___x_1466_);
v_fst_1468_ = lean_ctor_get(v_b_1457_, 0);
v_snd_1469_ = lean_ctor_get(v_b_1457_, 1);
v_isSharedCheck_1557_ = !lean_is_exclusive(v_b_1457_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1471_ = v_b_1457_;
v_isShared_1472_ = v_isSharedCheck_1557_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_snd_1469_);
lean_inc(v_fst_1468_);
lean_dec(v_b_1457_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1557_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1473_ = l_Lean_instInhabitedExpr;
v___x_1474_ = lean_nat_add(v___x_1451_, v_a_1456_);
v___x_1475_ = lean_array_get_borrowed(v___x_1473_, v_xs_1452_, v___x_1474_);
lean_dec(v___x_1474_);
lean_inc(v___y_1461_);
lean_inc_ref(v___y_1460_);
lean_inc(v___y_1459_);
lean_inc_ref(v___y_1458_);
lean_inc(v___x_1475_);
v___x_1476_ = lean_infer_type(v___x_1475_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_toConstantVal_1477_; lean_object* v_a_1478_; lean_object* v_name_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1546_; 
v_toConstantVal_1477_ = lean_ctor_get(v_indVal_1453_, 0);
lean_inc_ref(v_toConstantVal_1477_);
v_a_1478_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_a_1478_);
lean_dec_ref(v___x_1476_);
v_name_1479_ = lean_ctor_get(v_toConstantVal_1477_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v_toConstantVal_1477_);
if (v_isSharedCheck_1546_ == 0)
{
lean_object* v_unused_1547_; lean_object* v_unused_1548_; 
v_unused_1547_ = lean_ctor_get(v_toConstantVal_1477_, 2);
lean_dec(v_unused_1547_);
v_unused_1548_ = lean_ctor_get(v_toConstantVal_1477_, 1);
lean_dec(v_unused_1548_);
v___x_1481_ = v_toConstantVal_1477_;
v_isShared_1482_ = v_isSharedCheck_1546_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_name_1479_);
lean_dec(v_toConstantVal_1477_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1546_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v_a_1486_; uint8_t v___x_1494_; 
v___x_1483_ = lean_mk_syntax_ident(v_a_1467_);
lean_inc(v___x_1483_);
v___x_1484_ = lean_array_push(v_fst_1468_, v___x_1483_);
v___x_1494_ = l_Lean_Expr_isAppOf(v_a_1478_, v_name_1479_);
lean_dec(v_name_1479_);
lean_dec(v_a_1478_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1495_; 
lean_del_object(v___x_1481_);
lean_inc(v___y_1461_);
lean_inc_ref(v___y_1460_);
lean_inc(v___y_1459_);
lean_inc_ref(v___y_1458_);
lean_inc(v___x_1475_);
v___x_1495_ = l_Lean_Meta_isType(v___x_1475_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v_a_1496_; uint8_t v___x_1497_; 
v_a_1496_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_a_1496_);
lean_dec_ref(v___x_1495_);
v___x_1497_ = lean_unbox(v_a_1496_);
if (v___x_1497_ == 0)
{
lean_object* v_ref_1498_; lean_object* v_quotContext_1499_; lean_object* v_currMacroScope_1500_; uint8_t v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v_ref_1498_ = lean_ctor_get(v___y_1460_, 5);
v_quotContext_1499_ = lean_ctor_get(v___y_1460_, 10);
v_currMacroScope_1500_ = lean_ctor_get(v___y_1460_, 11);
v___x_1501_ = lean_unbox(v_a_1496_);
lean_dec(v_a_1496_);
v___x_1502_ = l_Lean_SourceInfo_fromRef(v_ref_1498_, v___x_1501_);
v___x_1503_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1504_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1);
v___x_1505_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__2));
lean_inc(v_currMacroScope_1500_);
lean_inc(v_quotContext_1499_);
v___x_1506_ = l_Lean_addMacroScope(v_quotContext_1499_, v___x_1505_, v_currMacroScope_1500_);
v___x_1507_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__6));
lean_inc(v___x_1502_);
v___x_1508_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1502_);
lean_ctor_set(v___x_1508_, 1, v___x_1504_);
lean_ctor_set(v___x_1508_, 2, v___x_1506_);
lean_ctor_set(v___x_1508_, 3, v___x_1507_);
v___x_1509_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
lean_inc(v___x_1502_);
v___x_1510_ = l_Lean_Syntax_node1(v___x_1502_, v___x_1509_, v___x_1483_);
v___x_1511_ = l_Lean_Syntax_node2(v___x_1502_, v___x_1503_, v___x_1508_, v___x_1510_);
v_a_1486_ = v___x_1511_;
goto v___jp_1485_;
}
else
{
lean_object* v_ref_1512_; lean_object* v_quotContext_1513_; lean_object* v_currMacroScope_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
lean_dec(v_a_1496_);
v_ref_1512_ = lean_ctor_get(v___y_1460_, 5);
v_quotContext_1513_ = lean_ctor_get(v___y_1460_, 10);
v_currMacroScope_1514_ = lean_ctor_get(v___y_1460_, 11);
v___x_1515_ = l_Lean_SourceInfo_fromRef(v_ref_1512_, v___x_1494_);
v___x_1516_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1517_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8);
v___x_1518_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__9));
lean_inc(v_currMacroScope_1514_);
lean_inc(v_quotContext_1513_);
v___x_1519_ = l_Lean_addMacroScope(v_quotContext_1513_, v___x_1518_, v_currMacroScope_1514_);
v___x_1520_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__12));
lean_inc(v___x_1515_);
v___x_1521_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1515_);
lean_ctor_set(v___x_1521_, 1, v___x_1517_);
lean_ctor_set(v___x_1521_, 2, v___x_1519_);
lean_ctor_set(v___x_1521_, 3, v___x_1520_);
v___x_1522_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
lean_inc(v___x_1515_);
v___x_1523_ = l_Lean_Syntax_node1(v___x_1515_, v___x_1522_, v___x_1483_);
v___x_1524_ = l_Lean_Syntax_node2(v___x_1515_, v___x_1516_, v___x_1521_, v___x_1523_);
v_a_1486_ = v___x_1524_;
goto v___jp_1485_;
}
}
else
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1532_; 
lean_dec_ref(v___x_1484_);
lean_dec(v___x_1483_);
lean_del_object(v___x_1471_);
lean_dec(v_snd_1469_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v_a_1456_);
lean_dec(v_auxFunName_1454_);
lean_dec_ref(v_indVal_1453_);
v_a_1525_ = lean_ctor_get(v___x_1495_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1527_ = v___x_1495_;
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1495_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1530_; 
if (v_isShared_1528_ == 0)
{
v___x_1530_ = v___x_1527_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_a_1525_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
}
else
{
lean_object* v_ref_1533_; uint8_t v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1543_; 
v_ref_1533_ = lean_ctor_get(v___y_1460_, 5);
v___x_1534_ = 0;
v___x_1535_ = l_Lean_SourceInfo_fromRef(v_ref_1533_, v___x_1534_);
v___x_1536_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
lean_inc(v_auxFunName_1454_);
v___x_1537_ = lean_mk_syntax_ident(v_auxFunName_1454_);
v___x_1538_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1539_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_1540_ = l_Array_append___redArg(v___x_1539_, v_levelInsts_1455_);
v___x_1541_ = lean_array_push(v___x_1540_, v___x_1483_);
lean_inc(v___x_1535_);
if (v_isShared_1482_ == 0)
{
lean_ctor_set_tag(v___x_1481_, 1);
lean_ctor_set(v___x_1481_, 2, v___x_1541_);
lean_ctor_set(v___x_1481_, 1, v___x_1538_);
lean_ctor_set(v___x_1481_, 0, v___x_1535_);
v___x_1543_ = v___x_1481_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1535_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v___x_1538_);
lean_ctor_set(v_reuseFailAlloc_1545_, 2, v___x_1541_);
v___x_1543_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
lean_object* v___x_1544_; 
v___x_1544_ = l_Lean_Syntax_node2(v___x_1535_, v___x_1536_, v___x_1537_, v___x_1543_);
v_a_1486_ = v___x_1544_;
goto v___jp_1485_;
}
}
v___jp_1485_:
{
lean_object* v___x_1487_; lean_object* v___x_1489_; 
v___x_1487_ = lean_array_push(v_snd_1469_, v_a_1486_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 1, v___x_1487_);
lean_ctor_set(v___x_1471_, 0, v___x_1484_);
v___x_1489_ = v___x_1471_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1484_);
lean_ctor_set(v_reuseFailAlloc_1493_, 1, v___x_1487_);
v___x_1489_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1490_ = lean_unsigned_to_nat(1u);
v___x_1491_ = lean_nat_add(v_a_1456_, v___x_1490_);
lean_dec(v_a_1456_);
v_a_1456_ = v___x_1491_;
v_b_1457_ = v___x_1489_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1556_; 
lean_del_object(v___x_1471_);
lean_dec(v_snd_1469_);
lean_dec(v_fst_1468_);
lean_dec(v_a_1467_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v_a_1456_);
lean_dec(v_auxFunName_1454_);
lean_dec_ref(v_indVal_1453_);
v_a_1549_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1551_ = v___x_1476_;
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1476_);
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
}
else
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec_ref(v_b_1457_);
lean_dec(v_a_1456_);
lean_dec(v_auxFunName_1454_);
lean_dec_ref(v_indVal_1453_);
v_a_1558_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1560_ = v___x_1466_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1466_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1558_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg___boxed(lean_object* v_upperBound_1566_, lean_object* v___x_1567_, lean_object* v_xs_1568_, lean_object* v_indVal_1569_, lean_object* v_auxFunName_1570_, lean_object* v_levelInsts_1571_, lean_object* v_a_1572_, lean_object* v_b_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg(v_upperBound_1566_, v___x_1567_, v_xs_1568_, v_indVal_1569_, v_auxFunName_1570_, v_levelInsts_1571_, v_a_1572_, v_b_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
lean_dec_ref(v_levelInsts_1571_);
lean_dec_ref(v_xs_1568_);
lean_dec(v___x_1567_);
lean_dec(v_upperBound_1566_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3___redArg(lean_object* v_upperBound_1580_, lean_object* v___x_1581_, lean_object* v_xs_1582_, lean_object* v_indVal_1583_, lean_object* v_auxFunName_1584_, lean_object* v_levelInsts_1585_, lean_object* v_a_1586_, lean_object* v_b_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
uint8_t v___x_1595_; 
v___x_1595_ = lean_nat_dec_lt(v_a_1586_, v_upperBound_1580_);
if (v___x_1595_ == 0)
{
lean_object* v___x_1596_; 
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v_auxFunName_1584_);
lean_dec_ref(v_indVal_1583_);
v___x_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1596_, 0, v_b_1587_);
return v___x_1596_;
}
else
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1597_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg___closed__1));
lean_inc(v___y_1593_);
lean_inc_ref(v___y_1592_);
v___x_1598_ = l_Lean_Core_mkFreshUserName(v___x_1597_, v___y_1592_, v___y_1593_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; lean_object* v_fst_1600_; lean_object* v_snd_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1689_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref(v___x_1598_);
v_fst_1600_ = lean_ctor_get(v_b_1587_, 0);
v_snd_1601_ = lean_ctor_get(v_b_1587_, 1);
v_isSharedCheck_1689_ = !lean_is_exclusive(v_b_1587_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1603_ = v_b_1587_;
v_isShared_1604_ = v_isSharedCheck_1689_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_snd_1601_);
lean_inc(v_fst_1600_);
lean_dec(v_b_1587_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1689_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1605_ = l_Lean_instInhabitedExpr;
v___x_1606_ = lean_nat_add(v___x_1581_, v_a_1586_);
v___x_1607_ = lean_array_get_borrowed(v___x_1605_, v_xs_1582_, v___x_1606_);
lean_dec(v___x_1606_);
lean_inc(v___y_1593_);
lean_inc_ref(v___y_1592_);
lean_inc(v___y_1591_);
lean_inc_ref(v___y_1590_);
lean_inc(v___x_1607_);
v___x_1608_ = lean_infer_type(v___x_1607_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_toConstantVal_1609_; lean_object* v_a_1610_; lean_object* v_name_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1678_; 
v_toConstantVal_1609_ = lean_ctor_get(v_indVal_1583_, 0);
lean_inc_ref(v_toConstantVal_1609_);
v_a_1610_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_a_1610_);
lean_dec_ref(v___x_1608_);
v_name_1611_ = lean_ctor_get(v_toConstantVal_1609_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v_toConstantVal_1609_);
if (v_isSharedCheck_1678_ == 0)
{
lean_object* v_unused_1679_; lean_object* v_unused_1680_; 
v_unused_1679_ = lean_ctor_get(v_toConstantVal_1609_, 2);
lean_dec(v_unused_1679_);
v_unused_1680_ = lean_ctor_get(v_toConstantVal_1609_, 1);
lean_dec(v_unused_1680_);
v___x_1613_ = v_toConstantVal_1609_;
v_isShared_1614_ = v_isSharedCheck_1678_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_name_1611_);
lean_dec(v_toConstantVal_1609_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1678_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v_a_1618_; uint8_t v___x_1626_; 
v___x_1615_ = lean_mk_syntax_ident(v_a_1599_);
lean_inc(v___x_1615_);
v___x_1616_ = lean_array_push(v_fst_1600_, v___x_1615_);
v___x_1626_ = l_Lean_Expr_isAppOf(v_a_1610_, v_name_1611_);
lean_dec(v_name_1611_);
lean_dec(v_a_1610_);
if (v___x_1626_ == 0)
{
lean_object* v___x_1627_; 
lean_del_object(v___x_1613_);
lean_inc(v___y_1593_);
lean_inc_ref(v___y_1592_);
lean_inc(v___y_1591_);
lean_inc_ref(v___y_1590_);
lean_inc(v___x_1607_);
v___x_1627_ = l_Lean_Meta_isType(v___x_1607_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v_a_1628_; uint8_t v___x_1629_; 
v_a_1628_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_a_1628_);
lean_dec_ref(v___x_1627_);
v___x_1629_ = lean_unbox(v_a_1628_);
if (v___x_1629_ == 0)
{
lean_object* v_ref_1630_; lean_object* v_quotContext_1631_; lean_object* v_currMacroScope_1632_; uint8_t v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v_ref_1630_ = lean_ctor_get(v___y_1592_, 5);
v_quotContext_1631_ = lean_ctor_get(v___y_1592_, 10);
v_currMacroScope_1632_ = lean_ctor_get(v___y_1592_, 11);
v___x_1633_ = lean_unbox(v_a_1628_);
lean_dec(v_a_1628_);
v___x_1634_ = l_Lean_SourceInfo_fromRef(v_ref_1630_, v___x_1633_);
v___x_1635_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1636_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1);
v___x_1637_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__2));
lean_inc(v_currMacroScope_1632_);
lean_inc(v_quotContext_1631_);
v___x_1638_ = l_Lean_addMacroScope(v_quotContext_1631_, v___x_1637_, v_currMacroScope_1632_);
v___x_1639_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__6));
lean_inc(v___x_1634_);
v___x_1640_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1634_);
lean_ctor_set(v___x_1640_, 1, v___x_1636_);
lean_ctor_set(v___x_1640_, 2, v___x_1638_);
lean_ctor_set(v___x_1640_, 3, v___x_1639_);
v___x_1641_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
lean_inc(v___x_1634_);
v___x_1642_ = l_Lean_Syntax_node1(v___x_1634_, v___x_1641_, v___x_1615_);
v___x_1643_ = l_Lean_Syntax_node2(v___x_1634_, v___x_1635_, v___x_1640_, v___x_1642_);
v_a_1618_ = v___x_1643_;
goto v___jp_1617_;
}
else
{
lean_object* v_ref_1644_; lean_object* v_quotContext_1645_; lean_object* v_currMacroScope_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
lean_dec(v_a_1628_);
v_ref_1644_ = lean_ctor_get(v___y_1592_, 5);
v_quotContext_1645_ = lean_ctor_get(v___y_1592_, 10);
v_currMacroScope_1646_ = lean_ctor_get(v___y_1592_, 11);
v___x_1647_ = l_Lean_SourceInfo_fromRef(v_ref_1644_, v___x_1626_);
v___x_1648_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1649_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8);
v___x_1650_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__9));
lean_inc(v_currMacroScope_1646_);
lean_inc(v_quotContext_1645_);
v___x_1651_ = l_Lean_addMacroScope(v_quotContext_1645_, v___x_1650_, v_currMacroScope_1646_);
v___x_1652_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__12));
lean_inc(v___x_1647_);
v___x_1653_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1647_);
lean_ctor_set(v___x_1653_, 1, v___x_1649_);
lean_ctor_set(v___x_1653_, 2, v___x_1651_);
lean_ctor_set(v___x_1653_, 3, v___x_1652_);
v___x_1654_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
lean_inc(v___x_1647_);
v___x_1655_ = l_Lean_Syntax_node1(v___x_1647_, v___x_1654_, v___x_1615_);
v___x_1656_ = l_Lean_Syntax_node2(v___x_1647_, v___x_1648_, v___x_1653_, v___x_1655_);
v_a_1618_ = v___x_1656_;
goto v___jp_1617_;
}
}
else
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
lean_dec_ref(v___x_1616_);
lean_dec(v___x_1615_);
lean_del_object(v___x_1603_);
lean_dec(v_snd_1601_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v_auxFunName_1584_);
lean_dec_ref(v_indVal_1583_);
v_a_1657_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1627_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1627_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
else
{
lean_object* v_ref_1665_; uint8_t v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1675_; 
v_ref_1665_ = lean_ctor_get(v___y_1592_, 5);
v___x_1666_ = 0;
v___x_1667_ = l_Lean_SourceInfo_fromRef(v_ref_1665_, v___x_1666_);
v___x_1668_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
lean_inc(v_auxFunName_1584_);
v___x_1669_ = lean_mk_syntax_ident(v_auxFunName_1584_);
v___x_1670_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1671_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_1672_ = l_Array_append___redArg(v___x_1671_, v_levelInsts_1585_);
v___x_1673_ = lean_array_push(v___x_1672_, v___x_1615_);
lean_inc(v___x_1667_);
if (v_isShared_1614_ == 0)
{
lean_ctor_set_tag(v___x_1613_, 1);
lean_ctor_set(v___x_1613_, 2, v___x_1673_);
lean_ctor_set(v___x_1613_, 1, v___x_1670_);
lean_ctor_set(v___x_1613_, 0, v___x_1667_);
v___x_1675_ = v___x_1613_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v___x_1667_);
lean_ctor_set(v_reuseFailAlloc_1677_, 1, v___x_1670_);
lean_ctor_set(v_reuseFailAlloc_1677_, 2, v___x_1673_);
v___x_1675_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
lean_object* v___x_1676_; 
v___x_1676_ = l_Lean_Syntax_node2(v___x_1667_, v___x_1668_, v___x_1669_, v___x_1675_);
v_a_1618_ = v___x_1676_;
goto v___jp_1617_;
}
}
v___jp_1617_:
{
lean_object* v___x_1619_; lean_object* v___x_1621_; 
v___x_1619_ = lean_array_push(v_snd_1601_, v_a_1618_);
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 1, v___x_1619_);
lean_ctor_set(v___x_1603_, 0, v___x_1616_);
v___x_1621_ = v___x_1603_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v___x_1616_);
lean_ctor_set(v_reuseFailAlloc_1625_, 1, v___x_1619_);
v___x_1621_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1622_ = lean_unsigned_to_nat(1u);
v___x_1623_ = lean_nat_add(v_a_1586_, v___x_1622_);
v___x_1624_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg(v_upperBound_1580_, v___x_1581_, v_xs_1582_, v_indVal_1583_, v_auxFunName_1584_, v_levelInsts_1585_, v___x_1623_, v___x_1621_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
return v___x_1624_;
}
}
}
}
else
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
lean_del_object(v___x_1603_);
lean_dec(v_snd_1601_);
lean_dec(v_fst_1600_);
lean_dec(v_a_1599_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v_auxFunName_1584_);
lean_dec_ref(v_indVal_1583_);
v_a_1681_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1683_ = v___x_1608_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1608_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1684_ == 0)
{
v___x_1686_ = v___x_1683_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_a_1681_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
}
else
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1697_; 
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec_ref(v_b_1587_);
lean_dec(v_auxFunName_1584_);
lean_dec_ref(v_indVal_1583_);
v_a_1690_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1692_ = v___x_1598_;
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1598_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1690_);
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
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3___redArg___boxed(lean_object* v_upperBound_1698_, lean_object* v___x_1699_, lean_object* v_xs_1700_, lean_object* v_indVal_1701_, lean_object* v_auxFunName_1702_, lean_object* v_levelInsts_1703_, lean_object* v_a_1704_, lean_object* v_b_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3___redArg(v_upperBound_1698_, v___x_1699_, v_xs_1700_, v_indVal_1701_, v_auxFunName_1702_, v_levelInsts_1703_, v_a_1704_, v_b_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec(v_a_1704_);
lean_dec_ref(v_levelInsts_1703_);
lean_dec_ref(v_xs_1700_);
lean_dec(v___x_1699_);
lean_dec(v_upperBound_1698_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__2(size_t v_sz_1714_, size_t v_i_1715_, lean_object* v_bs_1716_){
_start:
{
uint8_t v___x_1717_; 
v___x_1717_ = lean_usize_dec_lt(v_i_1715_, v_sz_1714_);
if (v___x_1717_ == 0)
{
return v_bs_1716_;
}
else
{
lean_object* v_v_1718_; lean_object* v___x_1719_; lean_object* v_bs_x27_1720_; size_t v___x_1721_; size_t v___x_1722_; lean_object* v___x_1723_; 
v_v_1718_ = lean_array_uget(v_bs_1716_, v_i_1715_);
v___x_1719_ = lean_unsigned_to_nat(0u);
v_bs_x27_1720_ = lean_array_uset(v_bs_1716_, v_i_1715_, v___x_1719_);
v___x_1721_ = ((size_t)1ULL);
v___x_1722_ = lean_usize_add(v_i_1715_, v___x_1721_);
v___x_1723_ = lean_array_uset(v_bs_x27_1720_, v_i_1715_, v_v_1718_);
v_i_1715_ = v___x_1722_;
v_bs_1716_ = v___x_1723_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__2___boxed(lean_object* v_sz_1725_, lean_object* v_i_1726_, lean_object* v_bs_1727_){
_start:
{
size_t v_sz_boxed_1728_; size_t v_i_boxed_1729_; lean_object* v_res_1730_; 
v_sz_boxed_1728_ = lean_unbox_usize(v_sz_1725_);
lean_dec(v_sz_1725_);
v_i_boxed_1729_ = lean_unbox_usize(v_i_1726_);
lean_dec(v_i_1726_);
v_res_1730_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__2(v_sz_boxed_1728_, v_i_boxed_1729_, v_bs_1727_);
return v_res_1730_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1738_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__9));
v___x_1739_ = l_Lean_mkAtom(v___x_1738_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1(lean_object* v_indVal_1741_, lean_object* v___x_1742_, lean_object* v___x_1743_, lean_object* v_numParams_1744_, lean_object* v_header_1745_, lean_object* v_auxFunName_1746_, lean_object* v_levelInsts_1747_, lean_object* v_numFields_1748_, lean_object* v___f_1749_, lean_object* v_name_1750_, lean_object* v_a_1751_, lean_object* v_head_1752_, lean_object* v_xs_1753_, lean_object* v_x_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v_numIndices_1762_; lean_object* v___x_1763_; 
v_numIndices_1762_ = lean_ctor_get(v_indVal_1741_, 2);
lean_inc_ref(v___x_1743_);
lean_inc(v___x_1742_);
v___x_1763_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg(v_numIndices_1762_, v___x_1742_, v___x_1743_, v___y_1759_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1764_);
lean_dec_ref(v___x_1763_);
lean_inc_ref(v___x_1743_);
v___x_1765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1743_);
lean_ctor_set(v___x_1765_, 1, v___x_1743_);
lean_inc(v___y_1760_);
lean_inc_ref(v___y_1759_);
lean_inc(v___y_1758_);
lean_inc_ref(v___y_1757_);
lean_inc(v_auxFunName_1746_);
lean_inc_ref(v_indVal_1741_);
v___x_1766_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4___redArg(v_numParams_1744_, v_header_1745_, v_xs_1753_, v_indVal_1741_, v_auxFunName_1746_, v_levelInsts_1747_, v___x_1742_, v___x_1765_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v_fst_1768_; lean_object* v_snd_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1872_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_a_1767_);
lean_dec_ref(v___x_1766_);
v_fst_1768_ = lean_ctor_get(v_a_1767_, 0);
v_snd_1769_ = lean_ctor_get(v_a_1767_, 1);
v_isSharedCheck_1872_ = !lean_is_exclusive(v_a_1767_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1771_ = v_a_1767_;
v_isShared_1772_ = v_isSharedCheck_1872_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_snd_1769_);
lean_inc(v_fst_1768_);
lean_dec(v_a_1767_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1872_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_fst_1768_);
lean_ctor_set(v_reuseFailAlloc_1871_, 1, v_snd_1769_);
v___x_1774_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
lean_object* v___x_1775_; 
lean_inc(v___y_1760_);
lean_inc_ref(v___y_1759_);
lean_inc(v___y_1758_);
lean_inc_ref(v___y_1757_);
v___x_1775_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3___redArg(v_numFields_1748_, v_numParams_1744_, v_xs_1753_, v_indVal_1741_, v_auxFunName_1746_, v_levelInsts_1747_, v___x_1742_, v___x_1774_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
lean_dec(v___x_1742_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; lean_object* v_ref_1777_; lean_object* v_quotContext_1778_; lean_object* v_currMacroScope_1779_; lean_object* v___x_1780_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_a_1776_);
lean_dec_ref(v___x_1775_);
v_ref_1777_ = lean_ctor_get(v___y_1759_, 5);
lean_inc(v_ref_1777_);
v_quotContext_1778_ = lean_ctor_get(v___y_1759_, 10);
v_currMacroScope_1779_ = lean_ctor_get(v___y_1759_, 11);
lean_inc_ref(v___f_1749_);
lean_inc(v___y_1760_);
lean_inc_ref(v___y_1759_);
lean_inc(v___y_1758_);
lean_inc_ref(v___y_1757_);
lean_inc(v___y_1756_);
lean_inc_ref(v___y_1755_);
v___x_1780_ = lean_apply_7(v___f_1749_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, lean_box(0));
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v_a_1781_; lean_object* v_fst_1782_; lean_object* v_snd_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1854_; 
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
lean_inc(v_a_1781_);
lean_dec_ref(v___x_1780_);
v_fst_1782_ = lean_ctor_get(v_a_1776_, 0);
v_snd_1783_ = lean_ctor_get(v_a_1776_, 1);
v_isSharedCheck_1854_ = !lean_is_exclusive(v_a_1776_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1785_ = v_a_1776_;
v_isShared_1786_ = v_isSharedCheck_1854_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_snd_1783_);
lean_inc(v_fst_1782_);
lean_dec(v_a_1776_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1854_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1798_; 
v___x_1787_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1788_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__4));
v___x_1789_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__2, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__2_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__2);
lean_inc(v_currMacroScope_1779_);
lean_inc(v_quotContext_1778_);
v___x_1790_ = l_Lean_addMacroScope(v_quotContext_1778_, v___x_1788_, v_currMacroScope_1779_);
v___x_1791_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__10));
lean_inc(v_a_1781_);
v___x_1792_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1792_, 0, v_a_1781_);
lean_ctor_set(v___x_1792_, 1, v___x_1789_);
lean_ctor_set(v___x_1792_, 2, v___x_1790_);
lean_ctor_set(v___x_1792_, 3, v___x_1791_);
v___x_1793_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1794_ = l_Lean_instQuoteNameMkStr1___private__1(v_name_1750_);
v___x_1795_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__12));
v___x_1796_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__13));
lean_inc(v_a_1781_);
if (v_isShared_1786_ == 0)
{
lean_ctor_set_tag(v___x_1785_, 2);
lean_ctor_set(v___x_1785_, 1, v___x_1796_);
lean_ctor_set(v___x_1785_, 0, v_a_1781_);
v___x_1798_ = v___x_1785_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1781_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v___x_1796_);
v___x_1798_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1799_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_1800_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__9));
v___x_1801_ = l_Lean_Syntax_SepArray_ofElems(v___x_1800_, v_a_1751_);
v___x_1802_ = l_Array_append___redArg(v___x_1799_, v___x_1801_);
lean_dec_ref(v___x_1801_);
lean_inc(v_a_1781_);
v___x_1803_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1803_, 0, v_a_1781_);
lean_ctor_set(v___x_1803_, 1, v___x_1793_);
lean_ctor_set(v___x_1803_, 2, v___x_1802_);
v___x_1804_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__14));
lean_inc(v_a_1781_);
v___x_1805_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1805_, 0, v_a_1781_);
lean_ctor_set(v___x_1805_, 1, v___x_1804_);
lean_inc(v_a_1781_);
v___x_1806_ = l_Lean_Syntax_node3(v_a_1781_, v___x_1795_, v___x_1798_, v___x_1803_, v___x_1805_);
lean_inc(v_a_1781_);
v___x_1807_ = l_Lean_Syntax_node2(v_a_1781_, v___x_1793_, v___x_1794_, v___x_1806_);
v___x_1808_ = l_Lean_Syntax_node2(v_a_1781_, v___x_1787_, v___x_1792_, v___x_1807_);
lean_inc_ref(v___y_1759_);
v___x_1809_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm(v___x_1808_, v_snd_1783_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
lean_dec(v_snd_1783_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_a_1810_; lean_object* v___x_1811_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
lean_inc(v_a_1810_);
lean_dec_ref(v___x_1809_);
v___x_1811_ = lean_apply_7(v___f_1749_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, lean_box(0));
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1844_; 
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1814_ = v___x_1811_;
v_isShared_1815_ = v_isSharedCheck_1844_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1811_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1844_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
uint8_t v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; size_t v_sz_1830_; size_t v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1842_; 
v___x_1816_ = 0;
v___x_1817_ = l_Lean_SourceInfo_fromRef(v_ref_1777_, v___x_1816_);
lean_dec(v_ref_1777_);
v___x_1818_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__4));
lean_inc(v___x_1817_);
v___x_1819_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1817_);
lean_ctor_set(v___x_1819_, 1, v___x_1818_);
v___x_1820_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__3));
v___x_1821_ = lean_mk_syntax_ident(v_head_1752_);
lean_inc(v___x_1817_);
v___x_1822_ = l_Lean_Syntax_node2(v___x_1817_, v___x_1820_, v___x_1819_, v___x_1821_);
v___x_1823_ = l_Array_append___redArg(v___x_1799_, v_fst_1782_);
lean_dec(v_fst_1782_);
lean_inc(v___x_1817_);
v___x_1824_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1817_);
lean_ctor_set(v___x_1824_, 1, v___x_1793_);
lean_ctor_set(v___x_1824_, 2, v___x_1823_);
v___x_1825_ = l_Lean_Syntax_node2(v___x_1817_, v___x_1787_, v___x_1822_, v___x_1824_);
v___x_1826_ = lean_array_push(v_a_1764_, v___x_1825_);
v___x_1827_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__1));
v___x_1828_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__2));
lean_inc(v_a_1812_);
v___x_1829_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1829_, 0, v_a_1812_);
lean_ctor_set(v___x_1829_, 1, v___x_1828_);
v_sz_1830_ = lean_array_size(v___x_1826_);
v___x_1831_ = ((size_t)0ULL);
v___x_1832_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__2(v_sz_1830_, v___x_1831_, v___x_1826_);
v___x_1833_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__3);
v___x_1834_ = l_Lean_mkSepArray(v___x_1832_, v___x_1833_);
lean_dec_ref(v___x_1832_);
v___x_1835_ = l_Array_append___redArg(v___x_1799_, v___x_1834_);
lean_dec_ref(v___x_1834_);
lean_inc(v_a_1812_);
v___x_1836_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1836_, 0, v_a_1812_);
lean_ctor_set(v___x_1836_, 1, v___x_1793_);
lean_ctor_set(v___x_1836_, 2, v___x_1835_);
lean_inc(v_a_1812_);
v___x_1837_ = l_Lean_Syntax_node1(v_a_1812_, v___x_1793_, v___x_1836_);
v___x_1838_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__4));
lean_inc(v_a_1812_);
v___x_1839_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1839_, 0, v_a_1812_);
lean_ctor_set(v___x_1839_, 1, v___x_1838_);
v___x_1840_ = l_Lean_Syntax_node4(v_a_1812_, v___x_1827_, v___x_1829_, v___x_1837_, v___x_1839_, v_a_1810_);
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 0, v___x_1840_);
v___x_1842_ = v___x_1814_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v___x_1840_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
else
{
lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1852_; 
lean_dec(v_a_1810_);
lean_dec(v_fst_1782_);
lean_dec(v_ref_1777_);
lean_dec(v_a_1764_);
lean_dec(v_head_1752_);
v_a_1845_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1847_ = v___x_1811_;
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v___x_1811_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1850_; 
if (v_isShared_1848_ == 0)
{
v___x_1850_ = v___x_1847_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_a_1845_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
}
else
{
lean_dec(v_fst_1782_);
lean_dec(v_ref_1777_);
lean_dec(v_a_1764_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v_head_1752_);
lean_dec_ref(v___f_1749_);
return v___x_1809_;
}
}
}
}
else
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
lean_dec(v_ref_1777_);
lean_dec(v_a_1776_);
lean_dec(v_a_1764_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v_head_1752_);
lean_dec(v_name_1750_);
lean_dec_ref(v___f_1749_);
v_a_1855_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1857_ = v___x_1780_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1780_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1855_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
else
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1870_; 
lean_dec(v_a_1764_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v_head_1752_);
lean_dec(v_name_1750_);
lean_dec_ref(v___f_1749_);
v_a_1863_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1865_ = v___x_1775_;
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1775_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1868_; 
if (v_isShared_1866_ == 0)
{
v___x_1868_ = v___x_1865_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1863_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
}
}
}
else
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
lean_dec(v_a_1764_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v_head_1752_);
lean_dec(v_name_1750_);
lean_dec_ref(v___f_1749_);
lean_dec(v_auxFunName_1746_);
lean_dec(v___x_1742_);
lean_dec_ref(v_indVal_1741_);
v_a_1873_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v___x_1766_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1766_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1873_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
else
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1888_; 
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v_head_1752_);
lean_dec(v_name_1750_);
lean_dec_ref(v___f_1749_);
lean_dec(v_auxFunName_1746_);
lean_dec_ref(v___x_1743_);
lean_dec(v___x_1742_);
lean_dec_ref(v_indVal_1741_);
v_a_1881_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1883_ = v___x_1763_;
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1763_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1886_; 
if (v_isShared_1884_ == 0)
{
v___x_1886_ = v___x_1883_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_a_1881_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_indVal_1889_ = _args[0];
lean_object* v___x_1890_ = _args[1];
lean_object* v___x_1891_ = _args[2];
lean_object* v_numParams_1892_ = _args[3];
lean_object* v_header_1893_ = _args[4];
lean_object* v_auxFunName_1894_ = _args[5];
lean_object* v_levelInsts_1895_ = _args[6];
lean_object* v_numFields_1896_ = _args[7];
lean_object* v___f_1897_ = _args[8];
lean_object* v_name_1898_ = _args[9];
lean_object* v_a_1899_ = _args[10];
lean_object* v_head_1900_ = _args[11];
lean_object* v_xs_1901_ = _args[12];
lean_object* v_x_1902_ = _args[13];
lean_object* v___y_1903_ = _args[14];
lean_object* v___y_1904_ = _args[15];
lean_object* v___y_1905_ = _args[16];
lean_object* v___y_1906_ = _args[17];
lean_object* v___y_1907_ = _args[18];
lean_object* v___y_1908_ = _args[19];
lean_object* v___y_1909_ = _args[20];
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1(v_indVal_1889_, v___x_1890_, v___x_1891_, v_numParams_1892_, v_header_1893_, v_auxFunName_1894_, v_levelInsts_1895_, v_numFields_1896_, v___f_1897_, v_name_1898_, v_a_1899_, v_head_1900_, v_xs_1901_, v_x_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_);
lean_dec_ref(v_x_1902_);
lean_dec_ref(v_xs_1901_);
lean_dec_ref(v_a_1899_);
lean_dec(v_numFields_1896_);
lean_dec_ref(v_levelInsts_1895_);
lean_dec_ref(v_header_1893_);
lean_dec(v_numParams_1892_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg(lean_object* v_a_1912_, lean_object* v_indVal_1913_, lean_object* v_auxFunName_1914_, lean_object* v_levelInsts_1915_, lean_object* v_header_1916_, lean_object* v_as_x27_1917_, lean_object* v_b_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
if (lean_obj_tag(v_as_x27_1917_) == 0)
{
lean_object* v___x_1926_; 
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
lean_dec_ref(v_header_1916_);
lean_dec_ref(v_levelInsts_1915_);
lean_dec(v_auxFunName_1914_);
lean_dec_ref(v_indVal_1913_);
lean_dec_ref(v_a_1912_);
v___x_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1926_, 0, v_b_1918_);
return v___x_1926_;
}
else
{
lean_object* v_head_1927_; lean_object* v_tail_1928_; lean_object* v___x_1929_; 
v_head_1927_ = lean_ctor_get(v_as_x27_1917_, 0);
lean_inc(v_head_1927_);
v_tail_1928_ = lean_ctor_get(v_as_x27_1917_, 1);
lean_inc(v_tail_1928_);
lean_dec_ref(v_as_x27_1917_);
lean_inc(v___y_1924_);
lean_inc_ref(v___y_1923_);
lean_inc(v___y_1922_);
lean_inc_ref(v___y_1921_);
lean_inc(v___y_1920_);
lean_inc_ref(v___y_1919_);
lean_inc(v_head_1927_);
v___x_1929_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1(v_head_1927_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; lean_object* v_toConstantVal_1931_; lean_object* v_numParams_1932_; lean_object* v_numFields_1933_; lean_object* v_name_1934_; lean_object* v_type_1935_; lean_object* v___f_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___f_1939_; uint8_t v___x_1940_; lean_object* v___x_1941_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_a_1930_);
lean_dec_ref(v___x_1929_);
v_toConstantVal_1931_ = lean_ctor_get(v_a_1930_, 0);
lean_inc_ref(v_toConstantVal_1931_);
v_numParams_1932_ = lean_ctor_get(v_a_1930_, 3);
lean_inc(v_numParams_1932_);
v_numFields_1933_ = lean_ctor_get(v_a_1930_, 4);
lean_inc(v_numFields_1933_);
lean_dec(v_a_1930_);
v_name_1934_ = lean_ctor_get(v_toConstantVal_1931_, 0);
lean_inc(v_name_1934_);
v_type_1935_ = lean_ctor_get(v_toConstantVal_1931_, 2);
lean_inc_ref(v_type_1935_);
lean_dec_ref(v_toConstantVal_1931_);
v___f_1936_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___closed__0));
v___x_1937_ = lean_unsigned_to_nat(0u);
v___x_1938_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__0));
lean_inc_ref(v_a_1912_);
lean_inc_ref(v_levelInsts_1915_);
lean_inc(v_auxFunName_1914_);
lean_inc_ref(v_header_1916_);
lean_inc_ref(v_indVal_1913_);
v___f_1939_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___boxed), 21, 12);
lean_closure_set(v___f_1939_, 0, v_indVal_1913_);
lean_closure_set(v___f_1939_, 1, v___x_1937_);
lean_closure_set(v___f_1939_, 2, v___x_1938_);
lean_closure_set(v___f_1939_, 3, v_numParams_1932_);
lean_closure_set(v___f_1939_, 4, v_header_1916_);
lean_closure_set(v___f_1939_, 5, v_auxFunName_1914_);
lean_closure_set(v___f_1939_, 6, v_levelInsts_1915_);
lean_closure_set(v___f_1939_, 7, v_numFields_1933_);
lean_closure_set(v___f_1939_, 8, v___f_1936_);
lean_closure_set(v___f_1939_, 9, v_name_1934_);
lean_closure_set(v___f_1939_, 10, v_a_1912_);
lean_closure_set(v___f_1939_, 11, v_head_1927_);
v___x_1940_ = 0;
lean_inc(v___y_1924_);
lean_inc_ref(v___y_1923_);
lean_inc(v___y_1922_);
lean_inc_ref(v___y_1921_);
lean_inc(v___y_1920_);
lean_inc_ref(v___y_1919_);
v___x_1941_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg(v_type_1935_, v___f_1939_, v___x_1940_, v___x_1940_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v_a_1942_; lean_object* v___x_1943_; 
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_a_1942_);
lean_dec_ref(v___x_1941_);
v___x_1943_ = lean_array_push(v_b_1918_, v_a_1942_);
v_as_x27_1917_ = v_tail_1928_;
v_b_1918_ = v___x_1943_;
goto _start;
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
lean_dec(v_tail_1928_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
lean_dec_ref(v_b_1918_);
lean_dec_ref(v_header_1916_);
lean_dec_ref(v_levelInsts_1915_);
lean_dec(v_auxFunName_1914_);
lean_dec_ref(v_indVal_1913_);
lean_dec_ref(v_a_1912_);
v_a_1945_ = lean_ctor_get(v___x_1941_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1941_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1941_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
else
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1960_; 
lean_dec(v_tail_1928_);
lean_dec(v_head_1927_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
lean_dec_ref(v_b_1918_);
lean_dec_ref(v_header_1916_);
lean_dec_ref(v_levelInsts_1915_);
lean_dec(v_auxFunName_1914_);
lean_dec_ref(v_indVal_1913_);
lean_dec_ref(v_a_1912_);
v_a_1953_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1955_ = v___x_1929_;
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___x_1929_);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___boxed(lean_object* v_a_1961_, lean_object* v_indVal_1962_, lean_object* v_auxFunName_1963_, lean_object* v_levelInsts_1964_, lean_object* v_header_1965_, lean_object* v_as_x27_1966_, lean_object* v_b_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg(v_a_1961_, v_indVal_1962_, v_auxFunName_1963_, v_levelInsts_1964_, v_header_1965_, v_as_x27_1966_, v_b_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__7(size_t v_sz_1976_, size_t v_i_1977_, lean_object* v_bs_1978_){
_start:
{
uint8_t v___x_1979_; 
v___x_1979_ = lean_usize_dec_lt(v_i_1977_, v_sz_1976_);
if (v___x_1979_ == 0)
{
return v_bs_1978_;
}
else
{
lean_object* v_v_1980_; lean_object* v___x_1981_; lean_object* v_bs_x27_1982_; size_t v___x_1983_; size_t v___x_1984_; lean_object* v___x_1985_; 
v_v_1980_ = lean_array_uget(v_bs_1978_, v_i_1977_);
v___x_1981_ = lean_unsigned_to_nat(0u);
v_bs_x27_1982_ = lean_array_uset(v_bs_1978_, v_i_1977_, v___x_1981_);
v___x_1983_ = ((size_t)1ULL);
v___x_1984_ = lean_usize_add(v_i_1977_, v___x_1983_);
v___x_1985_ = lean_array_uset(v_bs_x27_1982_, v_i_1977_, v_v_1980_);
v_i_1977_ = v___x_1984_;
v_bs_1978_ = v___x_1985_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__7___boxed(lean_object* v_sz_1987_, lean_object* v_i_1988_, lean_object* v_bs_1989_){
_start:
{
size_t v_sz_boxed_1990_; size_t v_i_boxed_1991_; lean_object* v_res_1992_; 
v_sz_boxed_1990_ = lean_unbox_usize(v_sz_1987_);
lean_dec(v_sz_1987_);
v_i_boxed_1991_ = lean_unbox_usize(v_i_1988_);
lean_dec(v_i_1988_);
v_res_1992_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__7(v_sz_boxed_1990_, v_i_boxed_1991_, v_bs_1989_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts(lean_object* v_header_1993_, lean_object* v_indVal_1994_, lean_object* v_auxFunName_1995_, lean_object* v_levelInsts_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_){
_start:
{
size_t v_sz_2004_; size_t v___x_2005_; lean_object* v___x_2006_; 
v_sz_2004_ = lean_array_size(v_levelInsts_1996_);
v___x_2005_ = ((size_t)0ULL);
lean_inc_ref(v_a_2001_);
lean_inc_ref(v_levelInsts_1996_);
v___x_2006_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg(v_sz_2004_, v___x_2005_, v_levelInsts_1996_, v_a_2001_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v_a_2007_; lean_object* v_ctors_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
lean_inc(v_a_2007_);
lean_dec_ref(v___x_2006_);
v_ctors_2008_ = lean_ctor_get(v_indVal_1994_, 4);
lean_inc(v_ctors_2008_);
v___x_2009_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__0));
v___x_2010_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg(v_a_2007_, v_indVal_1994_, v_auxFunName_1995_, v_levelInsts_1996_, v_header_1993_, v_ctors_2008_, v___x_2009_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2020_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2013_ = v___x_2010_;
v_isShared_2014_ = v_isSharedCheck_2020_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_2010_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2020_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
size_t v_sz_2015_; lean_object* v___x_2016_; lean_object* v___x_2018_; 
v_sz_2015_ = lean_array_size(v_a_2011_);
v___x_2016_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__7(v_sz_2015_, v___x_2005_, v_a_2011_);
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 0, v___x_2016_);
v___x_2018_ = v___x_2013_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2016_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
else
{
return v___x_2010_;
}
}
else
{
lean_dec(v_a_2002_);
lean_dec_ref(v_a_2001_);
lean_dec(v_a_2000_);
lean_dec_ref(v_a_1999_);
lean_dec(v_a_1998_);
lean_dec_ref(v_a_1997_);
lean_dec_ref(v_levelInsts_1996_);
lean_dec(v_auxFunName_1995_);
lean_dec_ref(v_indVal_1994_);
lean_dec_ref(v_header_1993_);
return v___x_2006_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts___boxed(lean_object* v_header_2021_, lean_object* v_indVal_2022_, lean_object* v_auxFunName_2023_, lean_object* v_levelInsts_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts(v_header_2021_, v_indVal_2022_, v_auxFunName_2023_, v_levelInsts_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0(size_t v_sz_2033_, size_t v_i_2034_, lean_object* v_bs_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
lean_object* v___x_2043_; 
v___x_2043_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg(v_sz_2033_, v_i_2034_, v_bs_2035_, v___y_2040_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___boxed(lean_object* v_sz_2044_, lean_object* v_i_2045_, lean_object* v_bs_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
size_t v_sz_boxed_2054_; size_t v_i_boxed_2055_; lean_object* v_res_2056_; 
v_sz_boxed_2054_ = lean_unbox_usize(v_sz_2044_);
lean_dec(v_sz_2044_);
v_i_boxed_2055_ = lean_unbox_usize(v_i_2045_);
lean_dec(v_i_2045_);
v_res_2056_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0(v_sz_boxed_2054_, v_i_boxed_2055_, v_bs_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
lean_dec(v___y_2052_);
lean_dec(v___y_2050_);
lean_dec_ref(v___y_2049_);
lean_dec(v___y_2048_);
lean_dec_ref(v___y_2047_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3(lean_object* v_upperBound_2057_, lean_object* v___x_2058_, lean_object* v_xs_2059_, lean_object* v_indVal_2060_, lean_object* v_auxFunName_2061_, lean_object* v_levelInsts_2062_, lean_object* v_inst_2063_, lean_object* v_R_2064_, lean_object* v_a_2065_, lean_object* v_b_2066_, lean_object* v_c_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
lean_object* v___x_2075_; 
v___x_2075_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3___redArg(v_upperBound_2057_, v___x_2058_, v_xs_2059_, v_indVal_2060_, v_auxFunName_2061_, v_levelInsts_2062_, v_a_2065_, v_b_2066_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
return v___x_2075_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3___boxed(lean_object** _args){
lean_object* v_upperBound_2076_ = _args[0];
lean_object* v___x_2077_ = _args[1];
lean_object* v_xs_2078_ = _args[2];
lean_object* v_indVal_2079_ = _args[3];
lean_object* v_auxFunName_2080_ = _args[4];
lean_object* v_levelInsts_2081_ = _args[5];
lean_object* v_inst_2082_ = _args[6];
lean_object* v_R_2083_ = _args[7];
lean_object* v_a_2084_ = _args[8];
lean_object* v_b_2085_ = _args[9];
lean_object* v_c_2086_ = _args[10];
lean_object* v___y_2087_ = _args[11];
lean_object* v___y_2088_ = _args[12];
lean_object* v___y_2089_ = _args[13];
lean_object* v___y_2090_ = _args[14];
lean_object* v___y_2091_ = _args[15];
lean_object* v___y_2092_ = _args[16];
lean_object* v___y_2093_ = _args[17];
_start:
{
lean_object* v_res_2094_; 
v_res_2094_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3(v_upperBound_2076_, v___x_2077_, v_xs_2078_, v_indVal_2079_, v_auxFunName_2080_, v_levelInsts_2081_, v_inst_2082_, v_R_2083_, v_a_2084_, v_b_2085_, v_c_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
lean_dec(v_a_2084_);
lean_dec_ref(v_levelInsts_2081_);
lean_dec_ref(v_xs_2078_);
lean_dec(v___x_2077_);
lean_dec(v_upperBound_2076_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4(lean_object* v_upperBound_2095_, lean_object* v_header_2096_, lean_object* v_xs_2097_, lean_object* v_indVal_2098_, lean_object* v_auxFunName_2099_, lean_object* v_levelInsts_2100_, lean_object* v_inst_2101_, lean_object* v_R_2102_, lean_object* v_a_2103_, lean_object* v_b_2104_, lean_object* v_c_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v___x_2113_; 
v___x_2113_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4___redArg(v_upperBound_2095_, v_header_2096_, v_xs_2097_, v_indVal_2098_, v_auxFunName_2099_, v_levelInsts_2100_, v_a_2103_, v_b_2104_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_2114_ = _args[0];
lean_object* v_header_2115_ = _args[1];
lean_object* v_xs_2116_ = _args[2];
lean_object* v_indVal_2117_ = _args[3];
lean_object* v_auxFunName_2118_ = _args[4];
lean_object* v_levelInsts_2119_ = _args[5];
lean_object* v_inst_2120_ = _args[6];
lean_object* v_R_2121_ = _args[7];
lean_object* v_a_2122_ = _args[8];
lean_object* v_b_2123_ = _args[9];
lean_object* v_c_2124_ = _args[10];
lean_object* v___y_2125_ = _args[11];
lean_object* v___y_2126_ = _args[12];
lean_object* v___y_2127_ = _args[13];
lean_object* v___y_2128_ = _args[14];
lean_object* v___y_2129_ = _args[15];
lean_object* v___y_2130_ = _args[16];
lean_object* v___y_2131_ = _args[17];
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4(v_upperBound_2114_, v_header_2115_, v_xs_2116_, v_indVal_2117_, v_auxFunName_2118_, v_levelInsts_2119_, v_inst_2120_, v_R_2121_, v_a_2122_, v_b_2123_, v_c_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec(v_a_2122_);
lean_dec_ref(v_levelInsts_2119_);
lean_dec_ref(v_xs_2116_);
lean_dec_ref(v_header_2115_);
lean_dec(v_upperBound_2114_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5(lean_object* v_upperBound_2133_, lean_object* v_inst_2134_, lean_object* v_R_2135_, lean_object* v_a_2136_, lean_object* v_b_2137_, lean_object* v_c_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_){
_start:
{
lean_object* v___x_2146_; 
v___x_2146_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg(v_upperBound_2133_, v_a_2136_, v_b_2137_, v___y_2143_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___boxed(lean_object* v_upperBound_2147_, lean_object* v_inst_2148_, lean_object* v_R_2149_, lean_object* v_a_2150_, lean_object* v_b_2151_, lean_object* v_c_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_){
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5(v_upperBound_2147_, v_inst_2148_, v_R_2149_, v_a_2150_, v_b_2151_, v_c_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec(v_upperBound_2147_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6(lean_object* v_a_2161_, lean_object* v_indVal_2162_, lean_object* v_auxFunName_2163_, lean_object* v_levelInsts_2164_, lean_object* v_header_2165_, lean_object* v_as_2166_, lean_object* v_as_x27_2167_, lean_object* v_b_2168_, lean_object* v_a_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v___x_2177_; 
v___x_2177_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg(v_a_2161_, v_indVal_2162_, v_auxFunName_2163_, v_levelInsts_2164_, v_header_2165_, v_as_x27_2167_, v_b_2168_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___boxed(lean_object* v_a_2178_, lean_object* v_indVal_2179_, lean_object* v_auxFunName_2180_, lean_object* v_levelInsts_2181_, lean_object* v_header_2182_, lean_object* v_as_2183_, lean_object* v_as_x27_2184_, lean_object* v_b_2185_, lean_object* v_a_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6(v_a_2178_, v_indVal_2179_, v_auxFunName_2180_, v_levelInsts_2181_, v_header_2182_, v_as_2183_, v_as_x27_2184_, v_b_2185_, v_a_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
lean_dec(v_as_2183_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4(lean_object* v_upperBound_2195_, lean_object* v___x_2196_, lean_object* v_xs_2197_, lean_object* v_indVal_2198_, lean_object* v_auxFunName_2199_, lean_object* v_levelInsts_2200_, lean_object* v_inst_2201_, lean_object* v_R_2202_, lean_object* v_a_2203_, lean_object* v_b_2204_, lean_object* v_c_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
lean_object* v___x_2213_; 
v___x_2213_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg(v_upperBound_2195_, v___x_2196_, v_xs_2197_, v_indVal_2198_, v_auxFunName_2199_, v_levelInsts_2200_, v_a_2203_, v_b_2204_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_2214_ = _args[0];
lean_object* v___x_2215_ = _args[1];
lean_object* v_xs_2216_ = _args[2];
lean_object* v_indVal_2217_ = _args[3];
lean_object* v_auxFunName_2218_ = _args[4];
lean_object* v_levelInsts_2219_ = _args[5];
lean_object* v_inst_2220_ = _args[6];
lean_object* v_R_2221_ = _args[7];
lean_object* v_a_2222_ = _args[8];
lean_object* v_b_2223_ = _args[9];
lean_object* v_c_2224_ = _args[10];
lean_object* v___y_2225_ = _args[11];
lean_object* v___y_2226_ = _args[12];
lean_object* v___y_2227_ = _args[13];
lean_object* v___y_2228_ = _args[14];
lean_object* v___y_2229_ = _args[15];
lean_object* v___y_2230_ = _args[16];
lean_object* v___y_2231_ = _args[17];
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4(v_upperBound_2214_, v___x_2215_, v_xs_2216_, v_indVal_2217_, v_auxFunName_2218_, v_levelInsts_2219_, v_inst_2220_, v_R_2221_, v_a_2222_, v_b_2223_, v_c_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
lean_dec_ref(v_levelInsts_2219_);
lean_dec_ref(v_xs_2216_);
lean_dec(v___x_2215_);
lean_dec(v_upperBound_2214_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6(lean_object* v_upperBound_2233_, lean_object* v_header_2234_, lean_object* v_xs_2235_, lean_object* v_indVal_2236_, lean_object* v_auxFunName_2237_, lean_object* v_levelInsts_2238_, lean_object* v_inst_2239_, lean_object* v_R_2240_, lean_object* v_a_2241_, lean_object* v_b_2242_, lean_object* v_c_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_){
_start:
{
lean_object* v___x_2251_; 
v___x_2251_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6___redArg(v_upperBound_2233_, v_header_2234_, v_xs_2235_, v_indVal_2236_, v_auxFunName_2237_, v_levelInsts_2238_, v_a_2241_, v_b_2242_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_);
return v___x_2251_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6___boxed(lean_object** _args){
lean_object* v_upperBound_2252_ = _args[0];
lean_object* v_header_2253_ = _args[1];
lean_object* v_xs_2254_ = _args[2];
lean_object* v_indVal_2255_ = _args[3];
lean_object* v_auxFunName_2256_ = _args[4];
lean_object* v_levelInsts_2257_ = _args[5];
lean_object* v_inst_2258_ = _args[6];
lean_object* v_R_2259_ = _args[7];
lean_object* v_a_2260_ = _args[8];
lean_object* v_b_2261_ = _args[9];
lean_object* v_c_2262_ = _args[10];
lean_object* v___y_2263_ = _args[11];
lean_object* v___y_2264_ = _args[12];
lean_object* v___y_2265_ = _args[13];
lean_object* v___y_2266_ = _args[14];
lean_object* v___y_2267_ = _args[15];
lean_object* v___y_2268_ = _args[16];
lean_object* v___y_2269_ = _args[17];
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6(v_upperBound_2252_, v_header_2253_, v_xs_2254_, v_indVal_2255_, v_auxFunName_2256_, v_levelInsts_2257_, v_inst_2258_, v_R_2259_, v_a_2260_, v_b_2261_, v_c_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec_ref(v_levelInsts_2257_);
lean_dec_ref(v_xs_2254_);
lean_dec_ref(v_header_2253_);
lean_dec(v_upperBound_2252_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody(lean_object* v_header_2284_, lean_object* v_indVal_2285_, lean_object* v_auxFunName_2286_, lean_object* v_levelInsts_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_){
_start:
{
lean_object* v___x_2295_; 
lean_inc_ref(v_indVal_2285_);
lean_inc_ref(v_header_2284_);
v___x_2295_ = l_Lean_Elab_Deriving_mkDiscrs(v_header_2284_, v_indVal_2285_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_object* v_a_2296_; lean_object* v___x_2297_; 
v_a_2296_ = lean_ctor_get(v___x_2295_, 0);
lean_inc(v_a_2296_);
lean_dec_ref(v___x_2295_);
lean_inc_ref(v_a_2292_);
v___x_2297_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts(v_header_2284_, v_indVal_2285_, v_auxFunName_2286_, v_levelInsts_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2328_; 
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2300_ = v___x_2297_;
v_isShared_2301_ = v_isSharedCheck_2328_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2297_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2328_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v_ref_2302_; uint8_t v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; size_t v_sz_2311_; size_t v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2326_; 
v_ref_2302_ = lean_ctor_get(v_a_2292_, 5);
lean_inc(v_ref_2302_);
lean_dec_ref(v_a_2292_);
v___x_2303_ = 0;
v___x_2304_ = l_Lean_SourceInfo_fromRef(v_ref_2302_, v___x_2303_);
lean_dec(v_ref_2302_);
v___x_2305_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__0));
v___x_2306_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__1));
lean_inc(v___x_2304_);
v___x_2307_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2304_);
lean_ctor_set(v___x_2307_, 1, v___x_2305_);
v___x_2308_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_2309_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
lean_inc(v___x_2304_);
v___x_2310_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2304_);
lean_ctor_set(v___x_2310_, 1, v___x_2308_);
lean_ctor_set(v___x_2310_, 2, v___x_2309_);
v_sz_2311_ = lean_array_size(v_a_2296_);
v___x_2312_ = ((size_t)0ULL);
v___x_2313_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__2(v_sz_2311_, v___x_2312_, v_a_2296_);
v___x_2314_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__3);
v___x_2315_ = l_Lean_mkSepArray(v___x_2313_, v___x_2314_);
lean_dec_ref(v___x_2313_);
v___x_2316_ = l_Array_append___redArg(v___x_2309_, v___x_2315_);
lean_dec_ref(v___x_2315_);
lean_inc(v___x_2304_);
v___x_2317_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2304_);
lean_ctor_set(v___x_2317_, 1, v___x_2308_);
lean_ctor_set(v___x_2317_, 2, v___x_2316_);
v___x_2318_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__2));
lean_inc(v___x_2304_);
v___x_2319_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2304_);
lean_ctor_set(v___x_2319_, 1, v___x_2318_);
v___x_2320_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__4));
v___x_2321_ = l_Array_append___redArg(v___x_2309_, v_a_2298_);
lean_dec(v_a_2298_);
lean_inc(v___x_2304_);
v___x_2322_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2304_);
lean_ctor_set(v___x_2322_, 1, v___x_2308_);
lean_ctor_set(v___x_2322_, 2, v___x_2321_);
lean_inc(v___x_2304_);
v___x_2323_ = l_Lean_Syntax_node1(v___x_2304_, v___x_2320_, v___x_2322_);
lean_inc_ref(v___x_2310_);
v___x_2324_ = l_Lean_Syntax_node6(v___x_2304_, v___x_2306_, v___x_2307_, v___x_2310_, v___x_2310_, v___x_2317_, v___x_2319_, v___x_2323_);
if (v_isShared_2301_ == 0)
{
lean_ctor_set(v___x_2300_, 0, v___x_2324_);
v___x_2326_ = v___x_2300_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2324_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
else
{
lean_object* v_a_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2336_; 
lean_dec(v_a_2296_);
lean_dec_ref(v_a_2292_);
v_a_2329_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2331_ = v___x_2297_;
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_a_2329_);
lean_dec(v___x_2297_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2334_; 
if (v_isShared_2332_ == 0)
{
v___x_2334_ = v___x_2331_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_a_2329_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
}
}
else
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2344_; 
lean_dec(v_a_2293_);
lean_dec_ref(v_a_2292_);
lean_dec(v_a_2291_);
lean_dec_ref(v_a_2290_);
lean_dec(v_a_2289_);
lean_dec_ref(v_a_2288_);
lean_dec_ref(v_levelInsts_2287_);
lean_dec(v_auxFunName_2286_);
lean_dec_ref(v_indVal_2285_);
lean_dec_ref(v_header_2284_);
v_a_2337_ = lean_ctor_get(v___x_2295_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2339_ = v___x_2295_;
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2295_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2342_; 
if (v_isShared_2340_ == 0)
{
v___x_2342_ = v___x_2339_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_a_2337_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___boxed(lean_object* v_header_2345_, lean_object* v_indVal_2346_, lean_object* v_auxFunName_2347_, lean_object* v_levelInsts_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_){
_start:
{
lean_object* v_res_2356_; 
v_res_2356_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody(v_header_2345_, v_indVal_2346_, v_auxFunName_2347_, v_levelInsts_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__0___redArg(lean_object* v_a_2357_, lean_object* v_b_2358_){
_start:
{
lean_object* v_array_2359_; lean_object* v_start_2360_; lean_object* v_stop_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2374_; 
v_array_2359_ = lean_ctor_get(v_a_2357_, 0);
v_start_2360_ = lean_ctor_get(v_a_2357_, 1);
v_stop_2361_ = lean_ctor_get(v_a_2357_, 2);
v_isSharedCheck_2374_ = !lean_is_exclusive(v_a_2357_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2363_ = v_a_2357_;
v_isShared_2364_ = v_isSharedCheck_2374_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_stop_2361_);
lean_inc(v_start_2360_);
lean_inc(v_array_2359_);
lean_dec(v_a_2357_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2374_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
uint8_t v___x_2365_; 
v___x_2365_ = lean_nat_dec_lt(v_start_2360_, v_stop_2361_);
if (v___x_2365_ == 0)
{
lean_del_object(v___x_2363_);
lean_dec(v_stop_2361_);
lean_dec(v_start_2360_);
lean_dec_ref(v_array_2359_);
return v_b_2358_;
}
else
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2369_; 
v___x_2366_ = lean_unsigned_to_nat(1u);
v___x_2367_ = lean_nat_add(v_start_2360_, v___x_2366_);
lean_inc_ref(v_array_2359_);
if (v_isShared_2364_ == 0)
{
lean_ctor_set(v___x_2363_, 1, v___x_2367_);
v___x_2369_ = v___x_2363_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_array_2359_);
lean_ctor_set(v_reuseFailAlloc_2373_, 1, v___x_2367_);
lean_ctor_set(v_reuseFailAlloc_2373_, 2, v_stop_2361_);
v___x_2369_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2370_ = lean_array_fget(v_array_2359_, v_start_2360_);
lean_dec(v_start_2360_);
lean_dec_ref(v_array_2359_);
v___x_2371_ = lean_array_push(v_b_2358_, v___x_2370_);
v_a_2357_ = v___x_2369_;
v_b_2358_ = v___x_2371_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__12(void){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2405_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__3));
v___x_2406_ = l_String_toRawSubstring_x27(v___x_2405_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1(lean_object* v_argNames_2482_, lean_object* v_levelInsts_2483_, lean_object* v_as_2484_, size_t v_sz_2485_, size_t v_i_2486_, lean_object* v_b_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
uint8_t v___x_2495_; 
v___x_2495_ = lean_usize_dec_lt(v_i_2486_, v_sz_2485_);
if (v___x_2495_ == 0)
{
lean_object* v___x_2496_; 
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec_ref(v_argNames_2482_);
v___x_2496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2496_, 0, v_b_2487_);
return v___x_2496_;
}
else
{
lean_object* v_snd_2497_; lean_object* v_fst_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2670_; 
v_snd_2497_ = lean_ctor_get(v_b_2487_, 1);
v_fst_2498_ = lean_ctor_get(v_b_2487_, 0);
v_isSharedCheck_2670_ = !lean_is_exclusive(v_b_2487_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2500_ = v_b_2487_;
v_isShared_2501_ = v_isSharedCheck_2670_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_snd_2497_);
lean_inc(v_fst_2498_);
lean_dec(v_b_2487_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2670_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v_array_2502_; lean_object* v_start_2503_; lean_object* v_stop_2504_; uint8_t v___x_2505_; 
v_array_2502_ = lean_ctor_get(v_snd_2497_, 0);
v_start_2503_ = lean_ctor_get(v_snd_2497_, 1);
v_stop_2504_ = lean_ctor_get(v_snd_2497_, 2);
v___x_2505_ = lean_nat_dec_lt(v_start_2503_, v_stop_2504_);
if (v___x_2505_ == 0)
{
lean_object* v___x_2507_; 
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec_ref(v_argNames_2482_);
if (v_isShared_2501_ == 0)
{
v___x_2507_ = v___x_2500_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_fst_2498_);
lean_ctor_set(v_reuseFailAlloc_2509_, 1, v_snd_2497_);
v___x_2507_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
lean_object* v___x_2508_; 
v___x_2508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2508_, 0, v___x_2507_);
return v___x_2508_;
}
}
else
{
lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2666_; 
lean_inc(v_stop_2504_);
lean_inc(v_start_2503_);
lean_inc_ref(v_array_2502_);
v_isSharedCheck_2666_ = !lean_is_exclusive(v_snd_2497_);
if (v_isSharedCheck_2666_ == 0)
{
lean_object* v_unused_2667_; lean_object* v_unused_2668_; lean_object* v_unused_2669_; 
v_unused_2667_ = lean_ctor_get(v_snd_2497_, 2);
lean_dec(v_unused_2667_);
v_unused_2668_ = lean_ctor_get(v_snd_2497_, 1);
lean_dec(v_unused_2668_);
v_unused_2669_ = lean_ctor_get(v_snd_2497_, 0);
lean_dec(v_unused_2669_);
v___x_2511_ = v_snd_2497_;
v_isShared_2512_ = v_isSharedCheck_2666_;
goto v_resetjp_2510_;
}
else
{
lean_dec(v_snd_2497_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2666_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v_a_2513_; lean_object* v___x_2514_; 
v_a_2513_ = lean_array_uget_borrowed(v_as_2484_, v_i_2486_);
lean_inc(v___y_2493_);
lean_inc_ref(v___y_2492_);
lean_inc(v___y_2491_);
lean_inc_ref(v___y_2490_);
lean_inc(v___y_2489_);
lean_inc_ref(v___y_2488_);
lean_inc(v_a_2513_);
v___x_2514_ = l_Lean_Elab_Deriving_mkInductArgNames(v_a_2513_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v_a_2515_; lean_object* v_numParams_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2521_; 
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_a_2515_);
lean_dec_ref(v___x_2514_);
v_numParams_2516_ = lean_ctor_get(v_a_2513_, 1);
v___x_2517_ = lean_array_fget(v_array_2502_, v_start_2503_);
v___x_2518_ = lean_unsigned_to_nat(1u);
v___x_2519_ = lean_nat_add(v_start_2503_, v___x_2518_);
lean_dec(v_start_2503_);
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 1, v___x_2519_);
v___x_2521_ = v___x_2511_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_array_2502_);
lean_ctor_set(v_reuseFailAlloc_2657_, 1, v___x_2519_);
lean_ctor_set(v_reuseFailAlloc_2657_, 2, v_stop_2504_);
v___x_2521_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
lean_object* v_lower_2523_; lean_object* v_upper_2524_; lean_object* v___x_2654_; lean_object* v___x_2655_; uint8_t v___x_2656_; 
v___x_2654_ = lean_unsigned_to_nat(0u);
v___x_2655_ = lean_array_get_size(v_a_2515_);
v___x_2656_ = lean_nat_dec_le(v_numParams_2516_, v___x_2654_);
if (v___x_2656_ == 0)
{
lean_inc(v_numParams_2516_);
v_lower_2523_ = v_numParams_2516_;
v_upper_2524_ = v___x_2655_;
goto v___jp_2522_;
}
else
{
v_lower_2523_ = v___x_2654_;
v_upper_2524_ = v___x_2655_;
goto v___jp_2522_;
}
v___jp_2522_:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2525_ = l_Array_toSubarray___redArg(v_a_2515_, v_lower_2523_, v_upper_2524_);
lean_inc_ref(v___x_2525_);
v___x_2526_ = l_Subarray_copy___redArg(v___x_2525_);
v___x_2527_ = l_Lean_Elab_Deriving_mkImplicitBinders(v___x_2526_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_object* v_a_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v_a_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; 
v_a_2528_ = lean_ctor_get(v___x_2527_, 0);
lean_inc(v_a_2528_);
lean_dec_ref(v___x_2527_);
v___x_2529_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2516_);
lean_inc_ref(v_argNames_2482_);
v___x_2530_ = l_Array_toSubarray___redArg(v_argNames_2482_, v___x_2529_, v_numParams_2516_);
v___x_2531_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__0));
v___x_2532_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__0___redArg(v___x_2530_, v___x_2531_);
v___x_2533_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__0___redArg(v___x_2525_, v___x_2531_);
v_a_2534_ = l_Array_append___redArg(v___x_2532_, v___x_2533_);
lean_dec_ref(v___x_2533_);
v___x_2535_ = lean_array_get_size(v_a_2534_);
v___x_2536_ = l_Array_toSubarray___redArg(v_a_2534_, v___x_2529_, v___x_2535_);
v___x_2537_ = l_Subarray_copy___redArg(v___x_2536_);
lean_inc(v_a_2513_);
v___x_2538_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v_a_2513_, v___x_2537_, v___y_2492_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v_a_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; 
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_a_2539_);
lean_dec_ref(v___x_2538_);
v___x_2540_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__2));
lean_inc(v___y_2493_);
lean_inc_ref(v___y_2492_);
v___x_2541_ = l_Lean_Core_mkFreshUserName(v___x_2540_, v___y_2492_, v___y_2493_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v_a_2542_; lean_object* v___x_2543_; 
v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
lean_inc(v_a_2542_);
lean_dec_ref(v___x_2541_);
lean_inc(v___y_2493_);
lean_inc_ref(v___y_2492_);
lean_inc(v___y_2491_);
lean_inc_ref(v___y_2490_);
lean_inc(v___y_2489_);
lean_inc_ref(v___y_2488_);
lean_inc_ref(v_argNames_2482_);
lean_inc(v_a_2513_);
v___x_2543_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr(v_a_2513_, v_argNames_2482_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v_a_2544_; lean_object* v_ref_2545_; lean_object* v_quotContext_2546_; lean_object* v_currMacroScope_2547_; uint8_t v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2617_; 
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc(v_a_2544_);
lean_dec_ref(v___x_2543_);
v_ref_2545_ = lean_ctor_get(v___y_2492_, 5);
v_quotContext_2546_ = lean_ctor_get(v___y_2492_, 10);
v_currMacroScope_2547_ = lean_ctor_get(v___y_2492_, 11);
v___x_2548_ = 0;
v___x_2549_ = l_Lean_SourceInfo_fromRef(v_ref_2545_, v___x_2548_);
v___x_2550_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__4));
v___x_2551_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__6));
v___x_2552_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__8));
v___x_2553_ = lean_mk_syntax_ident(v_a_2542_);
lean_inc(v___x_2549_);
v___x_2554_ = l_Lean_Syntax_node1(v___x_2549_, v___x_2552_, v___x_2553_);
v___x_2555_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_2556_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_2557_ = l_Array_append___redArg(v___x_2556_, v_a_2528_);
lean_dec(v_a_2528_);
lean_inc(v___x_2549_);
v___x_2558_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2549_);
lean_ctor_set(v___x_2558_, 1, v___x_2555_);
lean_ctor_set(v___x_2558_, 2, v___x_2557_);
v___x_2559_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__10));
v___x_2560_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__11));
lean_inc(v___x_2549_);
v___x_2561_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2549_);
lean_ctor_set(v___x_2561_, 1, v___x_2560_);
v___x_2562_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_2563_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__12);
v___x_2564_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__13));
lean_inc(v_currMacroScope_2547_);
lean_inc(v_quotContext_2546_);
v___x_2565_ = l_Lean_addMacroScope(v_quotContext_2546_, v___x_2564_, v_currMacroScope_2547_);
v___x_2566_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__26));
lean_inc(v___x_2549_);
v___x_2567_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2549_);
lean_ctor_set(v___x_2567_, 1, v___x_2563_);
lean_ctor_set(v___x_2567_, 2, v___x_2565_);
lean_ctor_set(v___x_2567_, 3, v___x_2566_);
lean_inc(v___x_2549_);
v___x_2568_ = l_Lean_Syntax_node1(v___x_2549_, v___x_2555_, v_a_2539_);
lean_inc(v___x_2549_);
v___x_2569_ = l_Lean_Syntax_node2(v___x_2549_, v___x_2562_, v___x_2567_, v___x_2568_);
lean_inc(v___x_2549_);
v___x_2570_ = l_Lean_Syntax_node2(v___x_2549_, v___x_2559_, v___x_2561_, v___x_2569_);
lean_inc(v___x_2549_);
v___x_2571_ = l_Lean_Syntax_node1(v___x_2549_, v___x_2555_, v___x_2570_);
v___x_2572_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__27));
lean_inc(v___x_2549_);
v___x_2573_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2549_);
lean_ctor_set(v___x_2573_, 1, v___x_2572_);
v___x_2574_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__29));
v___x_2575_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__30));
lean_inc(v___x_2549_);
v___x_2576_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2549_);
lean_ctor_set(v___x_2576_, 1, v___x_2575_);
lean_inc(v___x_2549_);
v___x_2577_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2549_);
lean_ctor_set(v___x_2577_, 1, v___x_2555_);
lean_ctor_set(v___x_2577_, 2, v___x_2556_);
v___x_2578_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__32));
v___x_2579_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__34));
v___x_2580_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__36));
v___x_2581_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1);
v___x_2582_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__2));
lean_inc(v_currMacroScope_2547_);
lean_inc(v_quotContext_2546_);
v___x_2583_ = l_Lean_addMacroScope(v_quotContext_2546_, v___x_2582_, v_currMacroScope_2547_);
v___x_2584_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__6));
lean_inc(v___x_2549_);
v___x_2585_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2549_);
lean_ctor_set(v___x_2585_, 1, v___x_2581_);
lean_ctor_set(v___x_2585_, 2, v___x_2583_);
lean_ctor_set(v___x_2585_, 3, v___x_2584_);
lean_inc_ref(v___x_2577_);
lean_inc(v___x_2549_);
v___x_2586_ = l_Lean_Syntax_node2(v___x_2549_, v___x_2580_, v___x_2585_, v___x_2577_);
v___x_2587_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__38));
v___x_2588_ = lean_mk_syntax_ident(v___x_2517_);
v___x_2589_ = l_Array_append___redArg(v___x_2556_, v_levelInsts_2483_);
lean_inc(v___x_2549_);
v___x_2590_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2549_);
lean_ctor_set(v___x_2590_, 1, v___x_2555_);
lean_ctor_set(v___x_2590_, 2, v___x_2589_);
lean_inc(v___x_2549_);
v___x_2591_ = l_Lean_Syntax_node2(v___x_2549_, v___x_2562_, v___x_2588_, v___x_2590_);
lean_inc_ref(v___x_2577_);
lean_inc_ref(v___x_2573_);
lean_inc(v___x_2549_);
v___x_2592_ = l_Lean_Syntax_node3(v___x_2549_, v___x_2587_, v___x_2573_, v___x_2577_, v___x_2591_);
lean_inc_ref_n(v___x_2577_, 2);
lean_inc(v___x_2549_);
v___x_2593_ = l_Lean_Syntax_node3(v___x_2549_, v___x_2555_, v___x_2577_, v___x_2577_, v___x_2592_);
lean_inc(v___x_2549_);
v___x_2594_ = l_Lean_Syntax_node2(v___x_2549_, v___x_2579_, v___x_2586_, v___x_2593_);
v___x_2595_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__9));
lean_inc(v___x_2549_);
v___x_2596_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2549_);
lean_ctor_set(v___x_2596_, 1, v___x_2595_);
v___x_2597_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8);
v___x_2598_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__9));
lean_inc(v_currMacroScope_2547_);
lean_inc(v_quotContext_2546_);
v___x_2599_ = l_Lean_addMacroScope(v_quotContext_2546_, v___x_2598_, v_currMacroScope_2547_);
v___x_2600_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__12));
lean_inc(v___x_2549_);
v___x_2601_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2549_);
lean_ctor_set(v___x_2601_, 1, v___x_2597_);
lean_ctor_set(v___x_2601_, 2, v___x_2599_);
lean_ctor_set(v___x_2601_, 3, v___x_2600_);
lean_inc_ref(v___x_2577_);
lean_inc(v___x_2549_);
v___x_2602_ = l_Lean_Syntax_node2(v___x_2549_, v___x_2580_, v___x_2601_, v___x_2577_);
lean_inc_ref(v___x_2577_);
lean_inc_ref(v___x_2573_);
lean_inc(v___x_2549_);
v___x_2603_ = l_Lean_Syntax_node3(v___x_2549_, v___x_2587_, v___x_2573_, v___x_2577_, v_a_2544_);
lean_inc_ref_n(v___x_2577_, 2);
lean_inc(v___x_2549_);
v___x_2604_ = l_Lean_Syntax_node3(v___x_2549_, v___x_2555_, v___x_2577_, v___x_2577_, v___x_2603_);
lean_inc(v___x_2549_);
v___x_2605_ = l_Lean_Syntax_node2(v___x_2549_, v___x_2579_, v___x_2602_, v___x_2604_);
lean_inc(v___x_2549_);
v___x_2606_ = l_Lean_Syntax_node3(v___x_2549_, v___x_2555_, v___x_2594_, v___x_2596_, v___x_2605_);
lean_inc(v___x_2549_);
v___x_2607_ = l_Lean_Syntax_node1(v___x_2549_, v___x_2578_, v___x_2606_);
v___x_2608_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__40));
lean_inc_ref(v___x_2577_);
lean_inc(v___x_2549_);
v___x_2609_ = l_Lean_Syntax_node1(v___x_2549_, v___x_2608_, v___x_2577_);
v___x_2610_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__10));
lean_inc(v___x_2549_);
v___x_2611_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2549_);
lean_ctor_set(v___x_2611_, 1, v___x_2610_);
lean_inc_ref(v___x_2577_);
lean_inc(v___x_2549_);
v___x_2612_ = l_Lean_Syntax_node6(v___x_2549_, v___x_2574_, v___x_2576_, v___x_2577_, v___x_2607_, v___x_2609_, v___x_2577_, v___x_2611_);
lean_inc(v___x_2549_);
v___x_2613_ = l_Lean_Syntax_node5(v___x_2549_, v___x_2551_, v___x_2554_, v___x_2558_, v___x_2571_, v___x_2573_, v___x_2612_);
v___x_2614_ = l_Lean_Syntax_node1(v___x_2549_, v___x_2550_, v___x_2613_);
v___x_2615_ = lean_array_push(v_fst_2498_, v___x_2614_);
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 1, v___x_2521_);
lean_ctor_set(v___x_2500_, 0, v___x_2615_);
v___x_2617_ = v___x_2500_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v___x_2615_);
lean_ctor_set(v_reuseFailAlloc_2621_, 1, v___x_2521_);
v___x_2617_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
size_t v___x_2618_; size_t v___x_2619_; 
v___x_2618_ = ((size_t)1ULL);
v___x_2619_ = lean_usize_add(v_i_2486_, v___x_2618_);
v_i_2486_ = v___x_2619_;
v_b_2487_ = v___x_2617_;
goto _start;
}
}
else
{
lean_object* v_a_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2629_; 
lean_dec(v_a_2542_);
lean_dec(v_a_2539_);
lean_dec(v_a_2528_);
lean_dec_ref(v___x_2521_);
lean_dec(v___x_2517_);
lean_del_object(v___x_2500_);
lean_dec(v_fst_2498_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec_ref(v_argNames_2482_);
v_a_2622_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2624_ = v___x_2543_;
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_a_2622_);
lean_dec(v___x_2543_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2627_; 
if (v_isShared_2625_ == 0)
{
v___x_2627_ = v___x_2624_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_a_2622_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
}
else
{
lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2637_; 
lean_dec(v_a_2539_);
lean_dec(v_a_2528_);
lean_dec_ref(v___x_2521_);
lean_dec(v___x_2517_);
lean_del_object(v___x_2500_);
lean_dec(v_fst_2498_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec_ref(v_argNames_2482_);
v_a_2630_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2632_ = v___x_2541_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2541_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2635_; 
if (v_isShared_2633_ == 0)
{
v___x_2635_ = v___x_2632_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_a_2630_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
}
else
{
lean_object* v_a_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2645_; 
lean_dec(v_a_2528_);
lean_dec_ref(v___x_2521_);
lean_dec(v___x_2517_);
lean_del_object(v___x_2500_);
lean_dec(v_fst_2498_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec_ref(v_argNames_2482_);
v_a_2638_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2640_ = v___x_2538_;
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_a_2638_);
lean_dec(v___x_2538_);
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
else
{
lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2653_; 
lean_dec_ref(v___x_2525_);
lean_dec_ref(v___x_2521_);
lean_dec(v___x_2517_);
lean_del_object(v___x_2500_);
lean_dec(v_fst_2498_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec_ref(v_argNames_2482_);
v_a_2646_ = lean_ctor_get(v___x_2527_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2648_ = v___x_2527_;
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2527_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2651_; 
if (v_isShared_2649_ == 0)
{
v___x_2651_ = v___x_2648_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_a_2646_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
}
}
}
else
{
lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2665_; 
lean_del_object(v___x_2511_);
lean_dec(v_stop_2504_);
lean_dec(v_start_2503_);
lean_dec_ref(v_array_2502_);
lean_del_object(v___x_2500_);
lean_dec(v_fst_2498_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec_ref(v_argNames_2482_);
v_a_2658_ = lean_ctor_get(v___x_2514_, 0);
v_isSharedCheck_2665_ = !lean_is_exclusive(v___x_2514_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2660_ = v___x_2514_;
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v___x_2514_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2663_; 
if (v_isShared_2661_ == 0)
{
v___x_2663_ = v___x_2660_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_a_2658_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___boxed(lean_object* v_argNames_2671_, lean_object* v_levelInsts_2672_, lean_object* v_as_2673_, lean_object* v_sz_2674_, lean_object* v_i_2675_, lean_object* v_b_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_){
_start:
{
size_t v_sz_boxed_2684_; size_t v_i_boxed_2685_; lean_object* v_res_2686_; 
v_sz_boxed_2684_ = lean_unbox_usize(v_sz_2674_);
lean_dec(v_sz_2674_);
v_i_boxed_2685_ = lean_unbox_usize(v_i_2675_);
lean_dec(v_i_2675_);
v_res_2686_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1(v_argNames_2671_, v_levelInsts_2672_, v_as_2673_, v_sz_boxed_2684_, v_i_boxed_2685_, v_b_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_);
lean_dec_ref(v_as_2673_);
lean_dec_ref(v_levelInsts_2672_);
return v_res_2686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls(lean_object* v_ctx_2687_, lean_object* v_argNames_2688_, lean_object* v_levelInsts_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_){
_start:
{
lean_object* v_typeInfos_2697_; lean_object* v_auxFunNames_2698_; lean_object* v___x_2699_; lean_object* v_letDecls_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; size_t v_sz_2704_; size_t v___x_2705_; lean_object* v___x_2706_; 
v_typeInfos_2697_ = lean_ctor_get(v_ctx_2687_, 1);
lean_inc_ref(v_typeInfos_2697_);
v_auxFunNames_2698_ = lean_ctor_get(v_ctx_2687_, 2);
lean_inc_ref(v_auxFunNames_2698_);
lean_dec_ref(v_ctx_2687_);
v___x_2699_ = lean_unsigned_to_nat(0u);
v_letDecls_2700_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__0));
v___x_2701_ = lean_array_get_size(v_auxFunNames_2698_);
v___x_2702_ = l_Array_toSubarray___redArg(v_auxFunNames_2698_, v___x_2699_, v___x_2701_);
v___x_2703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2703_, 0, v_letDecls_2700_);
lean_ctor_set(v___x_2703_, 1, v___x_2702_);
v_sz_2704_ = lean_array_size(v_typeInfos_2697_);
v___x_2705_ = ((size_t)0ULL);
v___x_2706_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1(v_argNames_2688_, v_levelInsts_2689_, v_typeInfos_2697_, v_sz_2704_, v___x_2705_, v___x_2703_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_);
lean_dec_ref(v_typeInfos_2697_);
if (lean_obj_tag(v___x_2706_) == 0)
{
lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2715_; 
v_a_2707_ = lean_ctor_get(v___x_2706_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___x_2706_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2709_ = v___x_2706_;
v_isShared_2710_ = v_isSharedCheck_2715_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_dec(v___x_2706_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2715_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v_fst_2711_; lean_object* v___x_2713_; 
v_fst_2711_ = lean_ctor_get(v_a_2707_, 0);
lean_inc(v_fst_2711_);
lean_dec(v_a_2707_);
if (v_isShared_2710_ == 0)
{
lean_ctor_set(v___x_2709_, 0, v_fst_2711_);
v___x_2713_ = v___x_2709_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_fst_2711_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
return v___x_2713_;
}
}
}
else
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2723_; 
v_a_2716_ = lean_ctor_get(v___x_2706_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2706_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2718_ = v___x_2706_;
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2706_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2721_; 
if (v_isShared_2719_ == 0)
{
v___x_2721_ = v___x_2718_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_a_2716_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls___boxed(lean_object* v_ctx_2724_, lean_object* v_argNames_2725_, lean_object* v_levelInsts_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_){
_start:
{
lean_object* v_res_2734_; 
v_res_2734_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls(v_ctx_2724_, v_argNames_2725_, v_levelInsts_2726_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_);
lean_dec_ref(v_levelInsts_2726_);
return v_res_2734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__0(lean_object* v_inst_2735_, lean_object* v_R_2736_, lean_object* v_a_2737_, lean_object* v_b_2738_){
_start:
{
lean_object* v___x_2739_; 
v___x_2739_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__0___redArg(v_a_2737_, v_b_2738_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__2(size_t v_sz_2740_, size_t v_i_2741_, lean_object* v_bs_2742_){
_start:
{
uint8_t v___x_2743_; 
v___x_2743_ = lean_usize_dec_lt(v_i_2741_, v_sz_2740_);
if (v___x_2743_ == 0)
{
return v_bs_2742_;
}
else
{
lean_object* v_v_2744_; lean_object* v___x_2745_; lean_object* v_bs_x27_2746_; size_t v___x_2747_; size_t v___x_2748_; lean_object* v___x_2749_; 
v_v_2744_ = lean_array_uget(v_bs_2742_, v_i_2741_);
v___x_2745_ = lean_unsigned_to_nat(0u);
v_bs_x27_2746_ = lean_array_uset(v_bs_2742_, v_i_2741_, v___x_2745_);
v___x_2747_ = ((size_t)1ULL);
v___x_2748_ = lean_usize_add(v_i_2741_, v___x_2747_);
v___x_2749_ = lean_array_uset(v_bs_x27_2746_, v_i_2741_, v_v_2744_);
v_i_2741_ = v___x_2748_;
v_bs_2742_ = v___x_2749_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__2___boxed(lean_object* v_sz_2751_, lean_object* v_i_2752_, lean_object* v_bs_2753_){
_start:
{
size_t v_sz_boxed_2754_; size_t v_i_boxed_2755_; lean_object* v_res_2756_; 
v_sz_boxed_2754_ = lean_unbox_usize(v_sz_2751_);
lean_dec(v_sz_2751_);
v_i_boxed_2755_ = lean_unbox_usize(v_i_2752_);
lean_dec(v_i_2752_);
v_res_2756_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__2(v_sz_boxed_2754_, v_i_boxed_2755_, v_bs_2753_);
return v_res_2756_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2767_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__4));
v___x_2768_ = l_String_toRawSubstring_x27(v___x_2767_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg(size_t v_sz_2789_, size_t v_i_2790_, lean_object* v_bs_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_){
_start:
{
uint8_t v___x_2795_; 
v___x_2795_ = lean_usize_dec_lt(v_i_2790_, v_sz_2789_);
if (v___x_2795_ == 0)
{
lean_object* v___x_2796_; 
lean_dec(v___y_2793_);
lean_dec_ref(v___y_2792_);
v___x_2796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2796_, 0, v_bs_2791_);
return v___x_2796_;
}
else
{
lean_object* v___x_2797_; lean_object* v___x_2798_; 
v___x_2797_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__1));
lean_inc(v___y_2793_);
lean_inc_ref(v___y_2792_);
v___x_2798_ = l_Lean_Core_mkFreshUserName(v___x_2797_, v___y_2792_, v___y_2793_);
if (lean_obj_tag(v___x_2798_) == 0)
{
lean_object* v_a_2799_; lean_object* v_ref_2800_; lean_object* v_quotContext_2801_; lean_object* v_currMacroScope_2802_; lean_object* v_v_2803_; lean_object* v___x_2804_; lean_object* v_bs_x27_2805_; lean_object* v___x_2806_; uint8_t v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; size_t v___x_2836_; size_t v___x_2837_; lean_object* v___x_2838_; 
v_a_2799_ = lean_ctor_get(v___x_2798_, 0);
lean_inc(v_a_2799_);
lean_dec_ref(v___x_2798_);
v_ref_2800_ = lean_ctor_get(v___y_2792_, 5);
v_quotContext_2801_ = lean_ctor_get(v___y_2792_, 10);
v_currMacroScope_2802_ = lean_ctor_get(v___y_2792_, 11);
v_v_2803_ = lean_array_uget(v_bs_2791_, v_i_2790_);
v___x_2804_ = lean_unsigned_to_nat(0u);
v_bs_x27_2805_ = lean_array_uset(v_bs_2791_, v_i_2790_, v___x_2804_);
v___x_2806_ = lean_mk_syntax_ident(v_a_2799_);
v___x_2807_ = 0;
v___x_2808_ = l_Lean_SourceInfo_fromRef(v_ref_2800_, v___x_2807_);
v___x_2809_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__3));
v___x_2810_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__4));
lean_inc(v___x_2808_);
v___x_2811_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2811_, 0, v___x_2808_);
lean_ctor_set(v___x_2811_, 1, v___x_2810_);
v___x_2812_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
lean_inc(v___x_2806_);
lean_inc(v___x_2808_);
v___x_2813_ = l_Lean_Syntax_node1(v___x_2808_, v___x_2812_, v___x_2806_);
v___x_2814_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__11));
lean_inc(v___x_2808_);
v___x_2815_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2808_);
lean_ctor_set(v___x_2815_, 1, v___x_2814_);
v___x_2816_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__6));
v___x_2817_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__5);
v___x_2818_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__6));
lean_inc(v_currMacroScope_2802_);
lean_inc(v_quotContext_2801_);
v___x_2819_ = l_Lean_addMacroScope(v_quotContext_2801_, v___x_2818_, v_currMacroScope_2802_);
v___x_2820_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__12));
lean_inc(v___x_2808_);
v___x_2821_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2821_, 0, v___x_2808_);
lean_ctor_set(v___x_2821_, 1, v___x_2817_);
lean_ctor_set(v___x_2821_, 2, v___x_2819_);
lean_ctor_set(v___x_2821_, 3, v___x_2820_);
v___x_2822_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__7));
lean_inc(v___x_2808_);
v___x_2823_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2823_, 0, v___x_2808_);
lean_ctor_set(v___x_2823_, 1, v___x_2822_);
v___x_2824_ = lean_mk_syntax_ident(v_v_2803_);
lean_inc(v___x_2808_);
v___x_2825_ = l_Lean_Syntax_node1(v___x_2808_, v___x_2812_, v___x_2824_);
v___x_2826_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__10));
lean_inc(v___x_2808_);
v___x_2827_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2827_, 0, v___x_2808_);
lean_ctor_set(v___x_2827_, 1, v___x_2826_);
lean_inc(v___x_2808_);
v___x_2828_ = l_Lean_Syntax_node4(v___x_2808_, v___x_2816_, v___x_2821_, v___x_2823_, v___x_2825_, v___x_2827_);
lean_inc(v___x_2808_);
v___x_2829_ = l_Lean_Syntax_node2(v___x_2808_, v___x_2812_, v___x_2815_, v___x_2828_);
v___x_2830_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
lean_inc(v___x_2808_);
v___x_2831_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2808_);
lean_ctor_set(v___x_2831_, 1, v___x_2812_);
lean_ctor_set(v___x_2831_, 2, v___x_2830_);
v___x_2832_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__13));
lean_inc(v___x_2808_);
v___x_2833_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2808_);
lean_ctor_set(v___x_2833_, 1, v___x_2832_);
v___x_2834_ = l_Lean_Syntax_node5(v___x_2808_, v___x_2809_, v___x_2811_, v___x_2813_, v___x_2829_, v___x_2831_, v___x_2833_);
v___x_2835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2806_);
lean_ctor_set(v___x_2835_, 1, v___x_2834_);
v___x_2836_ = ((size_t)1ULL);
v___x_2837_ = lean_usize_add(v_i_2790_, v___x_2836_);
v___x_2838_ = lean_array_uset(v_bs_x27_2805_, v_i_2790_, v___x_2835_);
v_i_2790_ = v___x_2837_;
v_bs_2791_ = v___x_2838_;
goto _start;
}
else
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2847_; 
lean_dec(v___y_2793_);
lean_dec_ref(v___y_2792_);
lean_dec_ref(v_bs_2791_);
v_a_2840_ = lean_ctor_get(v___x_2798_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2842_ = v___x_2798_;
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2798_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2845_; 
if (v_isShared_2843_ == 0)
{
v___x_2845_ = v___x_2842_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_a_2840_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___boxed(lean_object* v_sz_2848_, lean_object* v_i_2849_, lean_object* v_bs_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_){
_start:
{
size_t v_sz_boxed_2854_; size_t v_i_boxed_2855_; lean_object* v_res_2856_; 
v_sz_boxed_2854_ = lean_unbox_usize(v_sz_2848_);
lean_dec(v_sz_2848_);
v_i_boxed_2855_ = lean_unbox_usize(v_i_2849_);
lean_dec(v_i_2849_);
v_res_2856_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg(v_sz_boxed_2854_, v_i_boxed_2855_, v_bs_2850_, v___y_2851_, v___y_2852_);
return v_res_2856_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__1(size_t v_sz_2857_, size_t v_i_2858_, lean_object* v_bs_2859_){
_start:
{
uint8_t v___x_2860_; 
v___x_2860_ = lean_usize_dec_lt(v_i_2858_, v_sz_2857_);
if (v___x_2860_ == 0)
{
return v_bs_2859_;
}
else
{
lean_object* v_v_2861_; lean_object* v___x_2862_; lean_object* v_bs_x27_2863_; size_t v___x_2864_; size_t v___x_2865_; lean_object* v___x_2866_; 
v_v_2861_ = lean_array_uget(v_bs_2859_, v_i_2858_);
v___x_2862_ = lean_unsigned_to_nat(0u);
v_bs_x27_2863_ = lean_array_uset(v_bs_2859_, v_i_2858_, v___x_2862_);
v___x_2864_ = ((size_t)1ULL);
v___x_2865_ = lean_usize_add(v_i_2858_, v___x_2864_);
v___x_2866_ = lean_array_uset(v_bs_x27_2863_, v_i_2858_, v_v_2861_);
v_i_2858_ = v___x_2865_;
v_bs_2859_ = v___x_2866_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__1___boxed(lean_object* v_sz_2868_, lean_object* v_i_2869_, lean_object* v_bs_2870_){
_start:
{
size_t v_sz_boxed_2871_; size_t v_i_boxed_2872_; lean_object* v_res_2873_; 
v_sz_boxed_2871_ = lean_unbox_usize(v_sz_2868_);
lean_dec(v_sz_2868_);
v_i_boxed_2872_ = lean_unbox_usize(v_i_2869_);
lean_dec(v_i_2869_);
v_res_2873_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__1(v_sz_boxed_2871_, v_i_boxed_2872_, v_bs_2870_);
return v_res_2873_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__7(void){
_start:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2881_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__7));
v___x_2882_ = l_String_toRawSubstring_x27(v___x_2881_);
return v___x_2882_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20(void){
_start:
{
lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2907_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__19));
v___x_2908_ = l_Lean_stringToMessageData(v___x_2907_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction(lean_object* v_ctx_2909_, lean_object* v_i_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_){
_start:
{
lean_object* v_typeInfos_2918_; lean_object* v_auxFunNames_2919_; uint8_t v_usePartial_2920_; lean_object* v___x_2921_; lean_object* v_indVal_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
v_typeInfos_2918_ = lean_ctor_get(v_ctx_2909_, 1);
v_auxFunNames_2919_ = lean_ctor_get(v_ctx_2909_, 2);
v_usePartial_2920_ = lean_ctor_get_uint8(v_ctx_2909_, sizeof(void*)*3);
v___x_2921_ = l_Lean_instInhabitedInductiveVal_default;
v_indVal_2922_ = lean_array_get(v___x_2921_, v_typeInfos_2918_, v_i_2910_);
v___x_2923_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0));
v___x_2924_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__14));
v___x_2925_ = lean_unsigned_to_nat(1u);
lean_inc(v_a_2916_);
lean_inc_ref(v_a_2915_);
lean_inc(v_a_2914_);
lean_inc_ref(v_a_2913_);
lean_inc(v_a_2912_);
lean_inc_ref(v_a_2911_);
lean_inc(v_indVal_2922_);
v___x_2926_ = l_Lean_Elab_Deriving_mkHeader(v___x_2924_, v___x_2925_, v_indVal_2922_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_object* v_toConstantVal_2927_; lean_object* v_a_2928_; lean_object* v_levelParams_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_3168_; 
v_toConstantVal_2927_ = lean_ctor_get(v_indVal_2922_, 0);
lean_inc_ref(v_toConstantVal_2927_);
v_a_2928_ = lean_ctor_get(v___x_2926_, 0);
lean_inc(v_a_2928_);
lean_dec_ref(v___x_2926_);
v_levelParams_2929_ = lean_ctor_get(v_toConstantVal_2927_, 1);
v_isSharedCheck_3168_ = !lean_is_exclusive(v_toConstantVal_2927_);
if (v_isSharedCheck_3168_ == 0)
{
lean_object* v_unused_3169_; lean_object* v_unused_3170_; 
v_unused_3169_ = lean_ctor_get(v_toConstantVal_2927_, 2);
lean_dec(v_unused_3169_);
v_unused_3170_ = lean_ctor_get(v_toConstantVal_2927_, 0);
lean_dec(v_unused_3170_);
v___x_2931_ = v_toConstantVal_2927_;
v_isShared_2932_ = v_isSharedCheck_3168_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_levelParams_2929_);
lean_dec(v_toConstantVal_2927_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_3168_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2933_; size_t v_sz_2934_; size_t v___x_2935_; lean_object* v___x_2936_; 
v___x_2933_ = lean_array_mk(v_levelParams_2929_);
v_sz_2934_ = lean_array_size(v___x_2933_);
v___x_2935_ = ((size_t)0ULL);
lean_inc(v_a_2916_);
lean_inc_ref(v_a_2915_);
v___x_2936_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg(v_sz_2934_, v___x_2935_, v___x_2933_, v_a_2915_, v_a_2916_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_3159_; 
v_a_2937_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_2939_ = v___x_2936_;
v_isShared_2940_ = v_isSharedCheck_3159_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2936_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_3159_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2941_; lean_object* v_fst_2942_; lean_object* v_snd_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_3158_; 
v___x_2941_ = l_Array_unzip___redArg(v_a_2937_);
lean_dec(v_a_2937_);
v_fst_2942_ = lean_ctor_get(v___x_2941_, 0);
v_snd_2943_ = lean_ctor_get(v___x_2941_, 1);
v_isSharedCheck_3158_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_3158_ == 0)
{
v___x_2945_ = v___x_2941_;
v_isShared_2946_ = v_isSharedCheck_3158_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_snd_2943_);
lean_inc(v_fst_2942_);
lean_dec(v___x_2941_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_3158_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2947_; lean_object* v_auxFunName_2948_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v_a_2955_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v_body_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; size_t v_sz_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
v___x_2947_ = lean_box(0);
v_auxFunName_2948_ = lean_array_get(v___x_2947_, v_auxFunNames_2919_, v_i_2910_);
v_sz_3140_ = lean_array_size(v_fst_2942_);
v___x_3141_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__2(v_sz_3140_, v___x_2935_, v_fst_2942_);
lean_inc(v_a_2916_);
lean_inc_ref(v_a_2915_);
lean_inc(v_a_2914_);
lean_inc_ref(v_a_2913_);
lean_inc(v_a_2912_);
lean_inc_ref(v_a_2911_);
lean_inc_ref(v___x_3141_);
lean_inc(v_auxFunName_2948_);
lean_inc(v_indVal_2922_);
lean_inc(v_a_2928_);
v___x_3142_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody(v_a_2928_, v_indVal_2922_, v_auxFunName_2948_, v___x_3141_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_);
if (lean_obj_tag(v___x_3142_) == 0)
{
if (v_usePartial_2920_ == 0)
{
lean_object* v_a_3143_; 
lean_dec_ref(v___x_3141_);
lean_dec_ref(v_ctx_2909_);
v_a_3143_ = lean_ctor_get(v___x_3142_, 0);
lean_inc(v_a_3143_);
lean_dec_ref(v___x_3142_);
v_body_3088_ = v_a_3143_;
v___y_3089_ = v_a_2911_;
v___y_3090_ = v_a_2912_;
v___y_3091_ = v_a_2913_;
v___y_3092_ = v_a_2914_;
v___y_3093_ = v_a_2915_;
v___y_3094_ = v_a_2916_;
goto v___jp_3087_;
}
else
{
lean_object* v_a_3144_; lean_object* v_argNames_3145_; lean_object* v___x_3146_; 
v_a_3144_ = lean_ctor_get(v___x_3142_, 0);
lean_inc(v_a_3144_);
lean_dec_ref(v___x_3142_);
v_argNames_3145_ = lean_ctor_get(v_a_2928_, 1);
lean_inc(v_a_2916_);
lean_inc_ref(v_a_2915_);
lean_inc(v_a_2914_);
lean_inc_ref(v_a_2913_);
lean_inc(v_a_2912_);
lean_inc_ref(v_a_2911_);
lean_inc_ref(v_argNames_3145_);
v___x_3146_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls(v_ctx_2909_, v_argNames_3145_, v___x_3141_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_);
lean_dec_ref(v___x_3141_);
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_object* v_a_3147_; lean_object* v___x_3148_; 
v_a_3147_ = lean_ctor_get(v___x_3146_, 0);
lean_inc(v_a_3147_);
lean_dec_ref(v___x_3146_);
v___x_3148_ = l_Lean_Elab_Deriving_mkLet(v_a_3147_, v_a_3144_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_);
lean_dec(v_a_3147_);
if (lean_obj_tag(v___x_3148_) == 0)
{
lean_object* v_a_3149_; 
v_a_3149_ = lean_ctor_get(v___x_3148_, 0);
lean_inc(v_a_3149_);
lean_dec_ref(v___x_3148_);
v_body_3088_ = v_a_3149_;
v___y_3089_ = v_a_2911_;
v___y_3090_ = v_a_2912_;
v___y_3091_ = v_a_2913_;
v___y_3092_ = v_a_2914_;
v___y_3093_ = v_a_2915_;
v___y_3094_ = v_a_2916_;
goto v___jp_3087_;
}
else
{
lean_dec(v_auxFunName_2948_);
lean_del_object(v___x_2945_);
lean_dec(v_snd_2943_);
lean_del_object(v___x_2939_);
lean_del_object(v___x_2931_);
lean_dec(v_a_2928_);
lean_dec(v_indVal_2922_);
lean_dec(v_a_2916_);
lean_dec_ref(v_a_2915_);
lean_dec(v_a_2914_);
lean_dec_ref(v_a_2913_);
lean_dec(v_a_2912_);
lean_dec_ref(v_a_2911_);
return v___x_3148_;
}
}
else
{
lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3157_; 
lean_dec(v_a_3144_);
lean_dec(v_auxFunName_2948_);
lean_del_object(v___x_2945_);
lean_dec(v_snd_2943_);
lean_del_object(v___x_2939_);
lean_del_object(v___x_2931_);
lean_dec(v_a_2928_);
lean_dec(v_indVal_2922_);
lean_dec(v_a_2916_);
lean_dec_ref(v_a_2915_);
lean_dec(v_a_2914_);
lean_dec_ref(v_a_2913_);
lean_dec(v_a_2912_);
lean_dec_ref(v_a_2911_);
v_a_3150_ = lean_ctor_get(v___x_3146_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3152_ = v___x_3146_;
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_dec(v___x_3146_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3155_; 
if (v_isShared_3153_ == 0)
{
v___x_3155_ = v___x_3152_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_a_3150_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3141_);
lean_dec(v_auxFunName_2948_);
lean_del_object(v___x_2945_);
lean_dec(v_snd_2943_);
lean_del_object(v___x_2939_);
lean_del_object(v___x_2931_);
lean_dec(v_a_2928_);
lean_dec(v_indVal_2922_);
lean_dec(v_a_2916_);
lean_dec_ref(v_a_2915_);
lean_dec(v_a_2914_);
lean_dec_ref(v_a_2913_);
lean_dec(v_a_2912_);
lean_dec_ref(v_a_2911_);
lean_dec_ref(v_ctx_2909_);
return v___x_3142_;
}
v___jp_2949_:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; size_t v_sz_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2956_ = lean_array_pop(v___y_2954_);
v___x_2957_ = l_Array_append___redArg(v___x_2956_, v_snd_2943_);
lean_dec(v_snd_2943_);
v___x_2958_ = lean_mk_empty_array_with_capacity(v___x_2925_);
v___x_2959_ = lean_array_push(v___x_2958_, v_a_2955_);
v_sz_2960_ = lean_array_size(v___x_2959_);
v___x_2961_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__1(v_sz_2960_, v___x_2935_, v___x_2959_);
v___x_2962_ = l_Array_append___redArg(v___x_2957_, v___x_2961_);
lean_dec_ref(v___x_2961_);
if (v_usePartial_2920_ == 0)
{
lean_object* v_ref_2963_; lean_object* v_quotContext_2964_; lean_object* v_currMacroScope_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2975_; 
v_ref_2963_ = lean_ctor_get(v___y_2950_, 5);
lean_inc(v_ref_2963_);
v_quotContext_2964_ = lean_ctor_get(v___y_2950_, 10);
lean_inc(v_quotContext_2964_);
v_currMacroScope_2965_ = lean_ctor_get(v___y_2950_, 11);
lean_inc(v_currMacroScope_2965_);
lean_dec_ref(v___y_2950_);
v___x_2966_ = l_Lean_SourceInfo_fromRef(v_ref_2963_, v_usePartial_2920_);
lean_dec(v_ref_2963_);
v___x_2967_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__0));
v___x_2968_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__1));
lean_inc_ref(v___y_2951_);
v___x_2969_ = l_Lean_Name_mkStr4(v___x_2923_, v___y_2951_, v___x_2967_, v___x_2968_);
v___x_2970_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__2));
lean_inc_ref(v___y_2951_);
v___x_2971_ = l_Lean_Name_mkStr4(v___x_2923_, v___y_2951_, v___x_2967_, v___x_2970_);
v___x_2972_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_2973_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
lean_inc(v___x_2966_);
if (v_isShared_2932_ == 0)
{
lean_ctor_set_tag(v___x_2931_, 1);
lean_ctor_set(v___x_2931_, 2, v___x_2973_);
lean_ctor_set(v___x_2931_, 1, v___x_2972_);
lean_ctor_set(v___x_2931_, 0, v___x_2966_);
v___x_2975_ = v___x_2931_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v___x_2966_);
lean_ctor_set(v_reuseFailAlloc_3017_, 1, v___x_2972_);
lean_ctor_set(v_reuseFailAlloc_3017_, 2, v___x_2973_);
v___x_2975_ = v_reuseFailAlloc_3017_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2981_; 
lean_inc_ref_n(v___x_2975_, 7);
lean_inc(v___x_2966_);
v___x_2976_ = l_Lean_Syntax_node7(v___x_2966_, v___x_2971_, v___x_2975_, v___x_2975_, v___x_2975_, v___x_2975_, v___x_2975_, v___x_2975_, v___x_2975_);
v___x_2977_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__3));
lean_inc_ref(v___y_2951_);
v___x_2978_ = l_Lean_Name_mkStr4(v___x_2923_, v___y_2951_, v___x_2967_, v___x_2977_);
v___x_2979_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__4));
lean_inc(v___x_2966_);
if (v_isShared_2946_ == 0)
{
lean_ctor_set_tag(v___x_2945_, 2);
lean_ctor_set(v___x_2945_, 1, v___x_2979_);
lean_ctor_set(v___x_2945_, 0, v___x_2966_);
v___x_2981_ = v___x_2945_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v___x_2966_);
lean_ctor_set(v_reuseFailAlloc_3016_, 1, v___x_2979_);
v___x_2981_ = v_reuseFailAlloc_3016_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3014_; 
v___x_2982_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__5));
lean_inc_ref(v___y_2951_);
v___x_2983_ = l_Lean_Name_mkStr4(v___x_2923_, v___y_2951_, v___x_2967_, v___x_2982_);
v___x_2984_ = lean_mk_syntax_ident(v_auxFunName_2948_);
lean_inc_ref(v___x_2975_);
lean_inc(v___x_2966_);
v___x_2985_ = l_Lean_Syntax_node2(v___x_2966_, v___x_2983_, v___x_2984_, v___x_2975_);
v___x_2986_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__6));
lean_inc_ref(v___y_2951_);
v___x_2987_ = l_Lean_Name_mkStr4(v___x_2923_, v___y_2951_, v___x_2967_, v___x_2986_);
v___x_2988_ = l_Array_append___redArg(v___x_2973_, v___x_2962_);
lean_dec_ref(v___x_2962_);
lean_inc(v___x_2966_);
v___x_2989_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2989_, 0, v___x_2966_);
lean_ctor_set(v___x_2989_, 1, v___x_2972_);
lean_ctor_set(v___x_2989_, 2, v___x_2988_);
v___x_2990_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__9));
lean_inc_ref(v___y_2951_);
v___x_2991_ = l_Lean_Name_mkStr4(v___x_2923_, v___y_2951_, v___y_2953_, v___x_2990_);
v___x_2992_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__11));
lean_inc(v___x_2966_);
v___x_2993_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2993_, 0, v___x_2966_);
lean_ctor_set(v___x_2993_, 1, v___x_2992_);
v___x_2994_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__7, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__7_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__7);
v___x_2995_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__8));
v___x_2996_ = l_Lean_addMacroScope(v_quotContext_2964_, v___x_2995_, v_currMacroScope_2965_);
v___x_2997_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__14));
lean_inc(v___x_2966_);
v___x_2998_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2966_);
lean_ctor_set(v___x_2998_, 1, v___x_2994_);
lean_ctor_set(v___x_2998_, 2, v___x_2996_);
lean_ctor_set(v___x_2998_, 3, v___x_2997_);
lean_inc(v___x_2966_);
v___x_2999_ = l_Lean_Syntax_node2(v___x_2966_, v___x_2991_, v___x_2993_, v___x_2998_);
lean_inc(v___x_2966_);
v___x_3000_ = l_Lean_Syntax_node1(v___x_2966_, v___x_2972_, v___x_2999_);
lean_inc(v___x_2966_);
v___x_3001_ = l_Lean_Syntax_node2(v___x_2966_, v___x_2987_, v___x_2989_, v___x_3000_);
v___x_3002_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__15));
lean_inc_ref(v___y_2951_);
v___x_3003_ = l_Lean_Name_mkStr4(v___x_2923_, v___y_2951_, v___x_2967_, v___x_3002_);
v___x_3004_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__27));
lean_inc(v___x_2966_);
v___x_3005_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3005_, 0, v___x_2966_);
lean_ctor_set(v___x_3005_, 1, v___x_3004_);
v___x_3006_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__16));
v___x_3007_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__17));
v___x_3008_ = l_Lean_Name_mkStr4(v___x_2923_, v___y_2951_, v___x_3006_, v___x_3007_);
lean_inc_ref_n(v___x_2975_, 2);
lean_inc(v___x_2966_);
v___x_3009_ = l_Lean_Syntax_node2(v___x_2966_, v___x_3008_, v___x_2975_, v___x_2975_);
lean_inc_ref(v___x_2975_);
lean_inc(v___x_2966_);
v___x_3010_ = l_Lean_Syntax_node4(v___x_2966_, v___x_3003_, v___x_3005_, v___y_2952_, v___x_3009_, v___x_2975_);
lean_inc(v___x_2966_);
v___x_3011_ = l_Lean_Syntax_node5(v___x_2966_, v___x_2978_, v___x_2981_, v___x_2985_, v___x_3001_, v___x_3010_, v___x_2975_);
v___x_3012_ = l_Lean_Syntax_node2(v___x_2966_, v___x_2969_, v___x_2976_, v___x_3011_);
if (v_isShared_2940_ == 0)
{
lean_ctor_set(v___x_2939_, 0, v___x_3012_);
v___x_3014_ = v___x_2939_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v___x_3012_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
}
}
}
}
else
{
lean_object* v_ref_3018_; lean_object* v_quotContext_3019_; lean_object* v_currMacroScope_3020_; uint8_t v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3031_; 
v_ref_3018_ = lean_ctor_get(v___y_2950_, 5);
lean_inc(v_ref_3018_);
v_quotContext_3019_ = lean_ctor_get(v___y_2950_, 10);
lean_inc(v_quotContext_3019_);
v_currMacroScope_3020_ = lean_ctor_get(v___y_2950_, 11);
lean_inc(v_currMacroScope_3020_);
lean_dec_ref(v___y_2950_);
v___x_3021_ = 0;
v___x_3022_ = l_Lean_SourceInfo_fromRef(v_ref_3018_, v___x_3021_);
lean_dec(v_ref_3018_);
v___x_3023_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__0));
v___x_3024_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__1));
lean_inc_ref(v___y_2951_);
v___x_3025_ = l_Lean_Name_mkStr4(v___x_2923_, v___y_2951_, v___x_3023_, v___x_3024_);
v___x_3026_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__2));
lean_inc_ref(v___y_2951_);
v___x_3027_ = l_Lean_Name_mkStr4(v___x_2923_, v___y_2951_, v___x_3023_, v___x_3026_);
v___x_3028_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_3029_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
lean_inc(v___x_3022_);
if (v_isShared_2932_ == 0)
{
lean_ctor_set_tag(v___x_2931_, 1);
lean_ctor_set(v___x_2931_, 2, v___x_3029_);
lean_ctor_set(v___x_2931_, 1, v___x_3028_);
lean_ctor_set(v___x_2931_, 0, v___x_3022_);
v___x_3031_ = v___x_2931_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v___x_3022_);
lean_ctor_set(v_reuseFailAlloc_3078_, 1, v___x_3028_);
lean_ctor_set(v_reuseFailAlloc_3078_, 2, v___x_3029_);
v___x_3031_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3035_; 
v___x_3032_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__18));
lean_inc_ref(v___y_2951_);
v___x_3033_ = l_Lean_Name_mkStr4(v___x_2923_, v___y_2951_, v___x_3023_, v___x_3032_);
lean_inc(v___x_3022_);
if (v_isShared_2946_ == 0)
{
lean_ctor_set_tag(v___x_2945_, 2);
lean_ctor_set(v___x_2945_, 1, v___x_3032_);
lean_ctor_set(v___x_2945_, 0, v___x_3022_);
v___x_3035_ = v___x_2945_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v___x_3022_);
lean_ctor_set(v_reuseFailAlloc_3077_, 1, v___x_3032_);
v___x_3035_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3075_; 
lean_inc(v___x_3022_);
v___x_3036_ = l_Lean_Syntax_node1(v___x_3022_, v___x_3033_, v___x_3035_);
lean_inc(v___x_3022_);
v___x_3037_ = l_Lean_Syntax_node1(v___x_3022_, v___x_3028_, v___x_3036_);
lean_inc_ref_n(v___x_3031_, 6);
lean_inc(v___x_3022_);
v___x_3038_ = l_Lean_Syntax_node7(v___x_3022_, v___x_3027_, v___x_3031_, v___x_3031_, v___x_3031_, v___x_3031_, v___x_3031_, v___x_3031_, v___x_3037_);
v___x_3039_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__3));
lean_inc_ref(v___y_2951_);
v___x_3040_ = l_Lean_Name_mkStr4(v___x_2923_, v___y_2951_, v___x_3023_, v___x_3039_);
v___x_3041_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__4));
lean_inc(v___x_3022_);
v___x_3042_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3042_, 0, v___x_3022_);
lean_ctor_set(v___x_3042_, 1, v___x_3041_);
v___x_3043_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__5));
lean_inc_ref(v___y_2951_);
v___x_3044_ = l_Lean_Name_mkStr4(v___x_2923_, v___y_2951_, v___x_3023_, v___x_3043_);
v___x_3045_ = lean_mk_syntax_ident(v_auxFunName_2948_);
lean_inc_ref(v___x_3031_);
lean_inc(v___x_3022_);
v___x_3046_ = l_Lean_Syntax_node2(v___x_3022_, v___x_3044_, v___x_3045_, v___x_3031_);
v___x_3047_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__6));
lean_inc_ref(v___y_2951_);
v___x_3048_ = l_Lean_Name_mkStr4(v___x_2923_, v___y_2951_, v___x_3023_, v___x_3047_);
v___x_3049_ = l_Array_append___redArg(v___x_3029_, v___x_2962_);
lean_dec_ref(v___x_2962_);
lean_inc(v___x_3022_);
v___x_3050_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3050_, 0, v___x_3022_);
lean_ctor_set(v___x_3050_, 1, v___x_3028_);
lean_ctor_set(v___x_3050_, 2, v___x_3049_);
v___x_3051_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__9));
lean_inc_ref(v___y_2951_);
v___x_3052_ = l_Lean_Name_mkStr4(v___x_2923_, v___y_2951_, v___y_2953_, v___x_3051_);
v___x_3053_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__11));
lean_inc(v___x_3022_);
v___x_3054_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3022_);
lean_ctor_set(v___x_3054_, 1, v___x_3053_);
v___x_3055_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__7, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__7_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__7);
v___x_3056_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__8));
v___x_3057_ = l_Lean_addMacroScope(v_quotContext_3019_, v___x_3056_, v_currMacroScope_3020_);
v___x_3058_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__14));
lean_inc(v___x_3022_);
v___x_3059_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3059_, 0, v___x_3022_);
lean_ctor_set(v___x_3059_, 1, v___x_3055_);
lean_ctor_set(v___x_3059_, 2, v___x_3057_);
lean_ctor_set(v___x_3059_, 3, v___x_3058_);
lean_inc(v___x_3022_);
v___x_3060_ = l_Lean_Syntax_node2(v___x_3022_, v___x_3052_, v___x_3054_, v___x_3059_);
lean_inc(v___x_3022_);
v___x_3061_ = l_Lean_Syntax_node1(v___x_3022_, v___x_3028_, v___x_3060_);
lean_inc(v___x_3022_);
v___x_3062_ = l_Lean_Syntax_node2(v___x_3022_, v___x_3048_, v___x_3050_, v___x_3061_);
v___x_3063_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__15));
lean_inc_ref(v___y_2951_);
v___x_3064_ = l_Lean_Name_mkStr4(v___x_2923_, v___y_2951_, v___x_3023_, v___x_3063_);
v___x_3065_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__27));
lean_inc(v___x_3022_);
v___x_3066_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3022_);
lean_ctor_set(v___x_3066_, 1, v___x_3065_);
v___x_3067_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__16));
v___x_3068_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__17));
v___x_3069_ = l_Lean_Name_mkStr4(v___x_2923_, v___y_2951_, v___x_3067_, v___x_3068_);
lean_inc_ref_n(v___x_3031_, 2);
lean_inc(v___x_3022_);
v___x_3070_ = l_Lean_Syntax_node2(v___x_3022_, v___x_3069_, v___x_3031_, v___x_3031_);
lean_inc_ref(v___x_3031_);
lean_inc(v___x_3022_);
v___x_3071_ = l_Lean_Syntax_node4(v___x_3022_, v___x_3064_, v___x_3066_, v___y_2952_, v___x_3070_, v___x_3031_);
lean_inc(v___x_3022_);
v___x_3072_ = l_Lean_Syntax_node5(v___x_3022_, v___x_3040_, v___x_3042_, v___x_3046_, v___x_3062_, v___x_3071_, v___x_3031_);
v___x_3073_ = l_Lean_Syntax_node2(v___x_3022_, v___x_3025_, v___x_3038_, v___x_3072_);
if (v_isShared_2940_ == 0)
{
lean_ctor_set(v___x_2939_, 0, v___x_3073_);
v___x_3075_ = v___x_2939_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v___x_3073_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
}
}
}
v___jp_3079_:
{
if (lean_obj_tag(v___y_3085_) == 0)
{
lean_object* v_a_3086_; 
v_a_3086_ = lean_ctor_get(v___y_3085_, 0);
lean_inc(v_a_3086_);
lean_dec_ref(v___y_3085_);
v___y_2950_ = v___y_3080_;
v___y_2951_ = v___y_3081_;
v___y_2952_ = v___y_3082_;
v___y_2953_ = v___y_3083_;
v___y_2954_ = v___y_3084_;
v_a_2955_ = v_a_3086_;
goto v___jp_2949_;
}
else
{
lean_dec_ref(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
lean_dec_ref(v___y_3080_);
lean_dec(v_auxFunName_2948_);
lean_del_object(v___x_2945_);
lean_dec(v_snd_2943_);
lean_del_object(v___x_2939_);
lean_del_object(v___x_2931_);
return v___y_3085_;
}
}
v___jp_3087_:
{
lean_object* v_binders_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; uint8_t v___x_3103_; 
v_binders_3095_ = lean_ctor_get(v_a_2928_, 0);
lean_inc_ref(v_binders_3095_);
lean_dec(v_a_2928_);
v___x_3096_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__1));
v___x_3097_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__2));
v___x_3098_ = lean_box(0);
v___x_3099_ = lean_array_get_size(v_binders_3095_);
v___x_3100_ = lean_nat_sub(v___x_3099_, v___x_2925_);
v___x_3101_ = lean_array_get_borrowed(v___x_3098_, v_binders_3095_, v___x_3100_);
lean_dec(v___x_3100_);
v___x_3102_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__3));
lean_inc(v___x_3101_);
v___x_3103_ = l_Lean_Syntax_isOfKind(v___x_3101_, v___x_3102_);
if (v___x_3103_ == 0)
{
lean_object* v___x_3104_; lean_object* v___x_3105_; 
lean_dec(v_indVal_2922_);
v___x_3104_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20);
v___x_3105_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v___x_3104_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_);
lean_dec(v___y_3094_);
lean_dec(v___y_3092_);
lean_dec_ref(v___y_3091_);
lean_dec(v___y_3090_);
v___y_3080_ = v___y_3093_;
v___y_3081_ = v___x_3096_;
v___y_3082_ = v_body_3088_;
v___y_3083_ = v___x_3097_;
v___y_3084_ = v_binders_3095_;
v___y_3085_ = v___x_3105_;
goto v___jp_3079_;
}
else
{
lean_object* v___x_3106_; uint8_t v___x_3107_; 
v___x_3106_ = l_Lean_Syntax_getArg(v___x_3101_, v___x_2925_);
lean_inc(v___x_3106_);
v___x_3107_ = l_Lean_Syntax_matchesNull(v___x_3106_, v___x_2925_);
if (v___x_3107_ == 0)
{
lean_object* v___x_3108_; lean_object* v___x_3109_; 
lean_dec(v___x_3106_);
lean_dec(v_indVal_2922_);
v___x_3108_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20);
v___x_3109_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v___x_3108_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_);
lean_dec(v___y_3094_);
lean_dec(v___y_3092_);
lean_dec_ref(v___y_3091_);
lean_dec(v___y_3090_);
v___y_3080_ = v___y_3093_;
v___y_3081_ = v___x_3096_;
v___y_3082_ = v_body_3088_;
v___y_3083_ = v___x_3097_;
v___y_3084_ = v_binders_3095_;
v___y_3085_ = v___x_3109_;
goto v___jp_3079_;
}
else
{
lean_object* v___x_3110_; lean_object* v___x_3111_; uint8_t v___x_3112_; 
v___x_3110_ = lean_unsigned_to_nat(2u);
v___x_3111_ = l_Lean_Syntax_getArg(v___x_3101_, v___x_3110_);
lean_inc(v___x_3111_);
v___x_3112_ = l_Lean_Syntax_matchesNull(v___x_3111_, v___x_3110_);
if (v___x_3112_ == 0)
{
lean_object* v___x_3113_; lean_object* v___x_3114_; 
lean_dec(v___x_3111_);
lean_dec(v___x_3106_);
lean_dec(v_indVal_2922_);
v___x_3113_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20);
v___x_3114_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v___x_3113_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_);
lean_dec(v___y_3094_);
lean_dec(v___y_3092_);
lean_dec_ref(v___y_3091_);
lean_dec(v___y_3090_);
v___y_3080_ = v___y_3093_;
v___y_3081_ = v___x_3096_;
v___y_3082_ = v_body_3088_;
v___y_3083_ = v___x_3097_;
v___y_3084_ = v_binders_3095_;
v___y_3085_ = v___x_3114_;
goto v___jp_3079_;
}
else
{
lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; uint8_t v___x_3118_; 
v___x_3115_ = lean_unsigned_to_nat(0u);
v___x_3116_ = lean_unsigned_to_nat(3u);
v___x_3117_ = l_Lean_Syntax_getArg(v___x_3101_, v___x_3116_);
v___x_3118_ = l_Lean_Syntax_matchesNull(v___x_3117_, v___x_3115_);
if (v___x_3118_ == 0)
{
lean_object* v___x_3119_; lean_object* v___x_3120_; 
lean_dec(v___x_3111_);
lean_dec(v___x_3106_);
lean_dec(v_indVal_2922_);
v___x_3119_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20);
v___x_3120_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v___x_3119_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_);
lean_dec(v___y_3094_);
lean_dec(v___y_3092_);
lean_dec_ref(v___y_3091_);
lean_dec(v___y_3090_);
v___y_3080_ = v___y_3093_;
v___y_3081_ = v___x_3096_;
v___y_3082_ = v_body_3088_;
v___y_3083_ = v___x_3097_;
v___y_3084_ = v_binders_3095_;
v___y_3085_ = v___x_3120_;
goto v___jp_3079_;
}
else
{
lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3121_ = l_Lean_Syntax_getArg(v___x_3111_, v___x_2925_);
lean_dec(v___x_3111_);
v___x_3122_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType(v_indVal_2922_, v___x_3121_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_);
lean_dec(v___y_3094_);
lean_dec(v___y_3092_);
lean_dec_ref(v___y_3091_);
lean_dec(v___y_3090_);
if (lean_obj_tag(v___x_3122_) == 0)
{
lean_object* v_a_3123_; lean_object* v_ref_3124_; lean_object* v___x_3125_; uint8_t v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; 
v_a_3123_ = lean_ctor_get(v___x_3122_, 0);
lean_inc(v_a_3123_);
lean_dec_ref(v___x_3122_);
v_ref_3124_ = lean_ctor_get(v___y_3093_, 5);
v___x_3125_ = l_Lean_Syntax_getArg(v___x_3106_, v___x_3115_);
lean_dec(v___x_3106_);
v___x_3126_ = 0;
v___x_3127_ = l_Lean_SourceInfo_fromRef(v_ref_3124_, v___x_3126_);
v___x_3128_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__4));
lean_inc(v___x_3127_);
v___x_3129_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3127_);
lean_ctor_set(v___x_3129_, 1, v___x_3128_);
v___x_3130_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
lean_inc(v___x_3127_);
v___x_3131_ = l_Lean_Syntax_node1(v___x_3127_, v___x_3130_, v___x_3125_);
v___x_3132_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__11));
lean_inc(v___x_3127_);
v___x_3133_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3133_, 0, v___x_3127_);
lean_ctor_set(v___x_3133_, 1, v___x_3132_);
lean_inc(v___x_3127_);
v___x_3134_ = l_Lean_Syntax_node2(v___x_3127_, v___x_3130_, v___x_3133_, v_a_3123_);
v___x_3135_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
lean_inc(v___x_3127_);
v___x_3136_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3127_);
lean_ctor_set(v___x_3136_, 1, v___x_3130_);
lean_ctor_set(v___x_3136_, 2, v___x_3135_);
v___x_3137_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__13));
lean_inc(v___x_3127_);
v___x_3138_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3127_);
lean_ctor_set(v___x_3138_, 1, v___x_3137_);
v___x_3139_ = l_Lean_Syntax_node5(v___x_3127_, v___x_3102_, v___x_3129_, v___x_3131_, v___x_3134_, v___x_3136_, v___x_3138_);
v___y_2950_ = v___y_3093_;
v___y_2951_ = v___x_3096_;
v___y_2952_ = v_body_3088_;
v___y_2953_ = v___x_3097_;
v___y_2954_ = v_binders_3095_;
v_a_2955_ = v___x_3139_;
goto v___jp_2949_;
}
else
{
lean_dec(v___x_3106_);
v___y_3080_ = v___y_3093_;
v___y_3081_ = v___x_3096_;
v___y_3082_ = v_body_3088_;
v___y_3083_ = v___x_3097_;
v___y_3084_ = v_binders_3095_;
v___y_3085_ = v___x_3122_;
goto v___jp_3079_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
lean_del_object(v___x_2931_);
lean_dec(v_a_2928_);
lean_dec(v_indVal_2922_);
lean_dec(v_a_2916_);
lean_dec_ref(v_a_2915_);
lean_dec(v_a_2914_);
lean_dec_ref(v_a_2913_);
lean_dec(v_a_2912_);
lean_dec_ref(v_a_2911_);
lean_dec_ref(v_ctx_2909_);
v_a_3160_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3162_ = v___x_2936_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___x_2936_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3165_; 
if (v_isShared_3163_ == 0)
{
v___x_3165_ = v___x_3162_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3160_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
}
}
else
{
lean_object* v_a_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3178_; 
lean_dec(v_indVal_2922_);
lean_dec(v_a_2916_);
lean_dec_ref(v_a_2915_);
lean_dec(v_a_2914_);
lean_dec_ref(v_a_2913_);
lean_dec(v_a_2912_);
lean_dec_ref(v_a_2911_);
lean_dec_ref(v_ctx_2909_);
v_a_3171_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3173_ = v___x_2926_;
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_a_3171_);
lean_dec(v___x_2926_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3176_; 
if (v_isShared_3174_ == 0)
{
v___x_3176_ = v___x_3173_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_a_3171_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___boxed(lean_object* v_ctx_3179_, lean_object* v_i_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_){
_start:
{
lean_object* v_res_3188_; 
v_res_3188_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction(v_ctx_3179_, v_i_3180_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_);
lean_dec(v_i_3180_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0(size_t v_sz_3189_, size_t v_i_3190_, lean_object* v_bs_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_){
_start:
{
lean_object* v___x_3199_; 
v___x_3199_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg(v_sz_3189_, v_i_3190_, v_bs_3191_, v___y_3196_, v___y_3197_);
return v___x_3199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___boxed(lean_object* v_sz_3200_, lean_object* v_i_3201_, lean_object* v_bs_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_){
_start:
{
size_t v_sz_boxed_3210_; size_t v_i_boxed_3211_; lean_object* v_res_3212_; 
v_sz_boxed_3210_ = lean_unbox_usize(v_sz_3200_);
lean_dec(v_sz_3200_);
v_i_boxed_3211_ = lean_unbox_usize(v_i_3201_);
lean_dec(v_i_3201_);
v_res_3212_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0(v_sz_boxed_3210_, v_i_boxed_3211_, v_bs_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec(v___y_3204_);
lean_dec_ref(v___y_3203_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0___redArg(lean_object* v_upperBound_3213_, lean_object* v_ctx_3214_, lean_object* v_a_3215_, lean_object* v_b_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_){
_start:
{
uint8_t v___x_3224_; 
v___x_3224_ = lean_nat_dec_lt(v_a_3215_, v_upperBound_3213_);
if (v___x_3224_ == 0)
{
lean_object* v___x_3225_; 
lean_dec(v___y_3222_);
lean_dec_ref(v___y_3221_);
lean_dec(v___y_3220_);
lean_dec_ref(v___y_3219_);
lean_dec(v___y_3218_);
lean_dec_ref(v___y_3217_);
lean_dec(v_a_3215_);
lean_dec_ref(v_ctx_3214_);
v___x_3225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3225_, 0, v_b_3216_);
return v___x_3225_;
}
else
{
lean_object* v___x_3226_; 
lean_inc(v___y_3222_);
lean_inc_ref(v___y_3221_);
lean_inc(v___y_3220_);
lean_inc_ref(v___y_3219_);
lean_inc(v___y_3218_);
lean_inc_ref(v___y_3217_);
lean_inc_ref(v_ctx_3214_);
v___x_3226_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction(v_ctx_3214_, v_a_3215_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_);
if (lean_obj_tag(v___x_3226_) == 0)
{
lean_object* v_a_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; 
v_a_3227_ = lean_ctor_get(v___x_3226_, 0);
lean_inc(v_a_3227_);
lean_dec_ref(v___x_3226_);
v___x_3228_ = lean_array_push(v_b_3216_, v_a_3227_);
v___x_3229_ = lean_unsigned_to_nat(1u);
v___x_3230_ = lean_nat_add(v_a_3215_, v___x_3229_);
lean_dec(v_a_3215_);
v_a_3215_ = v___x_3230_;
v_b_3216_ = v___x_3228_;
goto _start;
}
else
{
lean_object* v_a_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3239_; 
lean_dec(v___y_3222_);
lean_dec_ref(v___y_3221_);
lean_dec(v___y_3220_);
lean_dec_ref(v___y_3219_);
lean_dec(v___y_3218_);
lean_dec_ref(v___y_3217_);
lean_dec_ref(v_b_3216_);
lean_dec(v_a_3215_);
lean_dec_ref(v_ctx_3214_);
v_a_3232_ = lean_ctor_get(v___x_3226_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3234_ = v___x_3226_;
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_a_3232_);
lean_dec(v___x_3226_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3237_; 
if (v_isShared_3235_ == 0)
{
v___x_3237_ = v___x_3234_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_a_3232_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0___redArg___boxed(lean_object* v_upperBound_3240_, lean_object* v_ctx_3241_, lean_object* v_a_3242_, lean_object* v_b_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_){
_start:
{
lean_object* v_res_3251_; 
v_res_3251_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0___redArg(v_upperBound_3240_, v_ctx_3241_, v_a_3242_, v_b_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_);
lean_dec(v_upperBound_3240_);
return v_res_3251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions(lean_object* v_ctx_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_){
_start:
{
lean_object* v_typeInfos_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v_auxDefs_3270_; lean_object* v___x_3271_; 
v_typeInfos_3267_ = lean_ctor_get(v_ctx_3259_, 1);
v___x_3268_ = lean_array_get_size(v_typeInfos_3267_);
v___x_3269_ = lean_unsigned_to_nat(0u);
v_auxDefs_3270_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__0));
lean_inc_ref(v_a_3264_);
v___x_3271_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0___redArg(v___x_3268_, v_ctx_3259_, v___x_3269_, v_auxDefs_3270_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_, v_a_3265_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v_a_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3292_; 
v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3274_ = v___x_3271_;
v_isShared_3275_ = v_isSharedCheck_3292_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_a_3272_);
lean_dec(v___x_3271_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3292_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v_ref_3276_; uint8_t v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3290_; 
v_ref_3276_ = lean_ctor_get(v_a_3264_, 5);
lean_inc(v_ref_3276_);
lean_dec_ref(v_a_3264_);
v___x_3277_ = 0;
v___x_3278_ = l_Lean_SourceInfo_fromRef(v_ref_3276_, v___x_3277_);
lean_dec(v_ref_3276_);
v___x_3279_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions___closed__0));
v___x_3280_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions___closed__1));
lean_inc(v___x_3278_);
v___x_3281_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3278_);
lean_ctor_set(v___x_3281_, 1, v___x_3279_);
v___x_3282_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_3283_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_3284_ = l_Array_append___redArg(v___x_3283_, v_a_3272_);
lean_dec(v_a_3272_);
lean_inc(v___x_3278_);
v___x_3285_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3278_);
lean_ctor_set(v___x_3285_, 1, v___x_3282_);
lean_ctor_set(v___x_3285_, 2, v___x_3284_);
v___x_3286_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions___closed__2));
lean_inc(v___x_3278_);
v___x_3287_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3287_, 0, v___x_3278_);
lean_ctor_set(v___x_3287_, 1, v___x_3286_);
v___x_3288_ = l_Lean_Syntax_node3(v___x_3278_, v___x_3280_, v___x_3281_, v___x_3285_, v___x_3287_);
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 0, v___x_3288_);
v___x_3290_ = v___x_3274_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v___x_3288_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
}
else
{
lean_object* v_a_3293_; lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3300_; 
lean_dec_ref(v_a_3264_);
v_a_3293_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3300_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3300_ == 0)
{
v___x_3295_ = v___x_3271_;
v_isShared_3296_ = v_isSharedCheck_3300_;
goto v_resetjp_3294_;
}
else
{
lean_inc(v_a_3293_);
lean_dec(v___x_3271_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3300_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
lean_object* v___x_3298_; 
if (v_isShared_3296_ == 0)
{
v___x_3298_ = v___x_3295_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v_a_3293_);
v___x_3298_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
return v___x_3298_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions___boxed(lean_object* v_ctx_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_){
_start:
{
lean_object* v_res_3309_; 
v_res_3309_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions(v_ctx_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_);
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0(lean_object* v_upperBound_3310_, lean_object* v_ctx_3311_, lean_object* v_inst_3312_, lean_object* v_R_3313_, lean_object* v_a_3314_, lean_object* v_b_3315_, lean_object* v_c_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
lean_object* v___x_3324_; 
v___x_3324_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0___redArg(v_upperBound_3310_, v_ctx_3311_, v_a_3314_, v_b_3315_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
return v___x_3324_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0___boxed(lean_object* v_upperBound_3325_, lean_object* v_ctx_3326_, lean_object* v_inst_3327_, lean_object* v_R_3328_, lean_object* v_a_3329_, lean_object* v_b_3330_, lean_object* v_c_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_){
_start:
{
lean_object* v_res_3339_; 
v_res_3339_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0(v_upperBound_3325_, v_ctx_3326_, v_inst_3327_, v_R_3328_, v_a_3329_, v_b_3330_, v_c_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
lean_dec(v_upperBound_3325_);
return v_res_3339_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0_spec__0(lean_object* v_a_3340_, lean_object* v_as_3341_, size_t v_i_3342_, size_t v_stop_3343_){
_start:
{
uint8_t v___x_3344_; 
v___x_3344_ = lean_usize_dec_eq(v_i_3342_, v_stop_3343_);
if (v___x_3344_ == 0)
{
lean_object* v___x_3345_; uint8_t v___x_3346_; 
v___x_3345_ = lean_array_uget_borrowed(v_as_3341_, v_i_3342_);
v___x_3346_ = lean_name_eq(v_a_3340_, v___x_3345_);
if (v___x_3346_ == 0)
{
size_t v___x_3347_; size_t v___x_3348_; 
v___x_3347_ = ((size_t)1ULL);
v___x_3348_ = lean_usize_add(v_i_3342_, v___x_3347_);
v_i_3342_ = v___x_3348_;
goto _start;
}
else
{
return v___x_3346_;
}
}
else
{
uint8_t v___x_3350_; 
v___x_3350_ = 0;
return v___x_3350_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0_spec__0___boxed(lean_object* v_a_3351_, lean_object* v_as_3352_, lean_object* v_i_3353_, lean_object* v_stop_3354_){
_start:
{
size_t v_i_boxed_3355_; size_t v_stop_boxed_3356_; uint8_t v_res_3357_; lean_object* v_r_3358_; 
v_i_boxed_3355_ = lean_unbox_usize(v_i_3353_);
lean_dec(v_i_3353_);
v_stop_boxed_3356_ = lean_unbox_usize(v_stop_3354_);
lean_dec(v_stop_3354_);
v_res_3357_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0_spec__0(v_a_3351_, v_as_3352_, v_i_boxed_3355_, v_stop_boxed_3356_);
lean_dec_ref(v_as_3352_);
lean_dec(v_a_3351_);
v_r_3358_ = lean_box(v_res_3357_);
return v_r_3358_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0(lean_object* v_as_3359_, lean_object* v_a_3360_){
_start:
{
lean_object* v___x_3361_; lean_object* v___x_3362_; uint8_t v___x_3363_; 
v___x_3361_ = lean_unsigned_to_nat(0u);
v___x_3362_ = lean_array_get_size(v_as_3359_);
v___x_3363_ = lean_nat_dec_lt(v___x_3361_, v___x_3362_);
if (v___x_3363_ == 0)
{
return v___x_3363_;
}
else
{
if (v___x_3363_ == 0)
{
return v___x_3363_;
}
else
{
size_t v___x_3364_; size_t v___x_3365_; uint8_t v___x_3366_; 
v___x_3364_ = ((size_t)0ULL);
v___x_3365_ = lean_usize_of_nat(v___x_3362_);
v___x_3366_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0_spec__0(v_a_3360_, v_as_3359_, v___x_3364_, v___x_3365_);
return v___x_3366_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0___boxed(lean_object* v_as_3367_, lean_object* v_a_3368_){
_start:
{
uint8_t v_res_3369_; lean_object* v_r_3370_; 
v_res_3369_ = l_Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0(v_as_3367_, v_a_3368_);
lean_dec(v_a_3368_);
lean_dec_ref(v_as_3367_);
v_r_3370_ = lean_box(v_res_3369_);
return v_r_3370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg(size_t v_sz_3377_, size_t v_i_3378_, lean_object* v_bs_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_){
_start:
{
uint8_t v___x_3383_; 
v___x_3383_ = lean_usize_dec_lt(v_i_3378_, v_sz_3377_);
if (v___x_3383_ == 0)
{
lean_object* v___x_3384_; 
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3380_);
v___x_3384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3384_, 0, v_bs_3379_);
return v___x_3384_;
}
else
{
lean_object* v___x_3385_; lean_object* v___x_3386_; 
v___x_3385_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__1));
lean_inc(v___y_3381_);
lean_inc_ref(v___y_3380_);
v___x_3386_ = l_Lean_Core_mkFreshUserName(v___x_3385_, v___y_3380_, v___y_3381_);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v_a_3387_; lean_object* v_ref_3388_; lean_object* v_quotContext_3389_; lean_object* v_currMacroScope_3390_; lean_object* v_v_3391_; lean_object* v___x_3392_; lean_object* v_bs_x27_3393_; lean_object* v___x_3394_; uint8_t v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; size_t v___x_3421_; size_t v___x_3422_; lean_object* v___x_3423_; 
v_a_3387_ = lean_ctor_get(v___x_3386_, 0);
lean_inc(v_a_3387_);
lean_dec_ref(v___x_3386_);
v_ref_3388_ = lean_ctor_get(v___y_3380_, 5);
v_quotContext_3389_ = lean_ctor_get(v___y_3380_, 10);
v_currMacroScope_3390_ = lean_ctor_get(v___y_3380_, 11);
v_v_3391_ = lean_array_uget(v_bs_3379_, v_i_3378_);
v___x_3392_ = lean_unsigned_to_nat(0u);
v_bs_x27_3393_ = lean_array_uset(v_bs_3379_, v_i_3378_, v___x_3392_);
v___x_3394_ = lean_mk_syntax_ident(v_a_3387_);
v___x_3395_ = 0;
v___x_3396_ = l_Lean_SourceInfo_fromRef(v_ref_3388_, v___x_3395_);
v___x_3397_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg___closed__1));
v___x_3398_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__13));
lean_inc(v___x_3396_);
v___x_3399_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3396_);
lean_ctor_set(v___x_3399_, 1, v___x_3398_);
v___x_3400_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_3401_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__11));
lean_inc(v___x_3396_);
v___x_3402_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3396_);
lean_ctor_set(v___x_3402_, 1, v___x_3401_);
lean_inc(v___x_3394_);
lean_inc(v___x_3396_);
v___x_3403_ = l_Lean_Syntax_node2(v___x_3396_, v___x_3400_, v___x_3394_, v___x_3402_);
v___x_3404_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__6));
v___x_3405_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__5);
v___x_3406_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__6));
lean_inc(v_currMacroScope_3390_);
lean_inc(v_quotContext_3389_);
v___x_3407_ = l_Lean_addMacroScope(v_quotContext_3389_, v___x_3406_, v_currMacroScope_3390_);
v___x_3408_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__12));
lean_inc(v___x_3396_);
v___x_3409_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3409_, 0, v___x_3396_);
lean_ctor_set(v___x_3409_, 1, v___x_3405_);
lean_ctor_set(v___x_3409_, 2, v___x_3407_);
lean_ctor_set(v___x_3409_, 3, v___x_3408_);
v___x_3410_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__7));
lean_inc(v___x_3396_);
v___x_3411_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3411_, 0, v___x_3396_);
lean_ctor_set(v___x_3411_, 1, v___x_3410_);
v___x_3412_ = lean_mk_syntax_ident(v_v_3391_);
lean_inc(v___x_3396_);
v___x_3413_ = l_Lean_Syntax_node1(v___x_3396_, v___x_3400_, v___x_3412_);
v___x_3414_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__10));
lean_inc(v___x_3396_);
v___x_3415_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3415_, 0, v___x_3396_);
lean_ctor_set(v___x_3415_, 1, v___x_3414_);
lean_inc(v___x_3396_);
v___x_3416_ = l_Lean_Syntax_node4(v___x_3396_, v___x_3404_, v___x_3409_, v___x_3411_, v___x_3413_, v___x_3415_);
v___x_3417_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__14));
lean_inc(v___x_3396_);
v___x_3418_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3396_);
lean_ctor_set(v___x_3418_, 1, v___x_3417_);
v___x_3419_ = l_Lean_Syntax_node4(v___x_3396_, v___x_3397_, v___x_3399_, v___x_3403_, v___x_3416_, v___x_3418_);
v___x_3420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3394_);
lean_ctor_set(v___x_3420_, 1, v___x_3419_);
v___x_3421_ = ((size_t)1ULL);
v___x_3422_ = lean_usize_add(v_i_3378_, v___x_3421_);
v___x_3423_ = lean_array_uset(v_bs_x27_3393_, v_i_3378_, v___x_3420_);
v_i_3378_ = v___x_3422_;
v_bs_3379_ = v___x_3423_;
goto _start;
}
else
{
lean_object* v_a_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3432_; 
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3380_);
lean_dec_ref(v_bs_3379_);
v_a_3425_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3432_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3432_ == 0)
{
v___x_3427_ = v___x_3386_;
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_a_3425_);
lean_dec(v___x_3386_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg___boxed(lean_object* v_sz_3433_, lean_object* v_i_3434_, lean_object* v_bs_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_){
_start:
{
size_t v_sz_boxed_3439_; size_t v_i_boxed_3440_; lean_object* v_res_3441_; 
v_sz_boxed_3439_ = lean_unbox_usize(v_sz_3433_);
lean_dec(v_sz_3433_);
v_i_boxed_3440_ = lean_unbox_usize(v_i_3434_);
lean_dec(v_i_3434_);
v_res_3441_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg(v_sz_boxed_3439_, v_i_boxed_3440_, v_bs_3435_, v___y_3436_, v___y_3437_);
return v_res_3441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__2(size_t v_sz_3442_, size_t v_i_3443_, lean_object* v_bs_3444_){
_start:
{
uint8_t v___x_3445_; 
v___x_3445_ = lean_usize_dec_lt(v_i_3443_, v_sz_3442_);
if (v___x_3445_ == 0)
{
return v_bs_3444_;
}
else
{
lean_object* v_v_3446_; lean_object* v___x_3447_; lean_object* v_bs_x27_3448_; size_t v___x_3449_; size_t v___x_3450_; lean_object* v___x_3451_; 
v_v_3446_ = lean_array_uget(v_bs_3444_, v_i_3443_);
v___x_3447_ = lean_unsigned_to_nat(0u);
v_bs_x27_3448_ = lean_array_uset(v_bs_3444_, v_i_3443_, v___x_3447_);
v___x_3449_ = ((size_t)1ULL);
v___x_3450_ = lean_usize_add(v_i_3443_, v___x_3449_);
v___x_3451_ = lean_array_uset(v_bs_x27_3448_, v_i_3443_, v_v_3446_);
v_i_3443_ = v___x_3450_;
v_bs_3444_ = v___x_3451_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__2___boxed(lean_object* v_sz_3453_, lean_object* v_i_3454_, lean_object* v_bs_3455_){
_start:
{
size_t v_sz_boxed_3456_; size_t v_i_boxed_3457_; lean_object* v_res_3458_; 
v_sz_boxed_3456_ = lean_unbox_usize(v_sz_3453_);
lean_dec(v_sz_3453_);
v_i_boxed_3457_ = lean_unbox_usize(v_i_3454_);
lean_dec(v_i_3454_);
v_res_3458_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__2(v_sz_boxed_3456_, v_i_boxed_3457_, v_bs_3455_);
return v_res_3458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3(lean_object* v_typeNames_3499_, lean_object* v_as_3500_, size_t v_sz_3501_, size_t v_i_3502_, lean_object* v_b_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_){
_start:
{
lean_object* v_a_3512_; uint8_t v___x_3516_; 
v___x_3516_ = lean_usize_dec_lt(v_i_3502_, v_sz_3501_);
if (v___x_3516_ == 0)
{
lean_object* v___x_3517_; 
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
v___x_3517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3517_, 0, v_b_3503_);
return v___x_3517_;
}
else
{
lean_object* v_snd_3518_; lean_object* v_fst_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3730_; 
v_snd_3518_ = lean_ctor_get(v_b_3503_, 1);
v_fst_3519_ = lean_ctor_get(v_b_3503_, 0);
v_isSharedCheck_3730_ = !lean_is_exclusive(v_b_3503_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3521_ = v_b_3503_;
v_isShared_3522_ = v_isSharedCheck_3730_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_snd_3518_);
lean_inc(v_fst_3519_);
lean_dec(v_b_3503_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3730_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v_array_3523_; lean_object* v_start_3524_; lean_object* v_stop_3525_; uint8_t v___x_3526_; 
v_array_3523_ = lean_ctor_get(v_snd_3518_, 0);
v_start_3524_ = lean_ctor_get(v_snd_3518_, 1);
v_stop_3525_ = lean_ctor_get(v_snd_3518_, 2);
v___x_3526_ = lean_nat_dec_lt(v_start_3524_, v_stop_3525_);
if (v___x_3526_ == 0)
{
lean_object* v___x_3528_; 
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
if (v_isShared_3522_ == 0)
{
v___x_3528_ = v___x_3521_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v_fst_3519_);
lean_ctor_set(v_reuseFailAlloc_3530_, 1, v_snd_3518_);
v___x_3528_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
lean_object* v___x_3529_; 
v___x_3529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3529_, 0, v___x_3528_);
return v___x_3529_;
}
}
else
{
lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3726_; 
lean_inc(v_stop_3525_);
lean_inc(v_start_3524_);
lean_inc_ref(v_array_3523_);
v_isSharedCheck_3726_ = !lean_is_exclusive(v_snd_3518_);
if (v_isSharedCheck_3726_ == 0)
{
lean_object* v_unused_3727_; lean_object* v_unused_3728_; lean_object* v_unused_3729_; 
v_unused_3727_ = lean_ctor_get(v_snd_3518_, 2);
lean_dec(v_unused_3727_);
v_unused_3728_ = lean_ctor_get(v_snd_3518_, 1);
lean_dec(v_unused_3728_);
v_unused_3729_ = lean_ctor_get(v_snd_3518_, 0);
lean_dec(v_unused_3729_);
v___x_3532_ = v_snd_3518_;
v_isShared_3533_ = v_isSharedCheck_3726_;
goto v_resetjp_3531_;
}
else
{
lean_dec(v_snd_3518_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3726_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
lean_object* v_a_3534_; lean_object* v_toConstantVal_3535_; lean_object* v_name_3536_; lean_object* v_levelParams_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3724_; 
v_a_3534_ = lean_array_uget_borrowed(v_as_3500_, v_i_3502_);
v_toConstantVal_3535_ = lean_ctor_get(v_a_3534_, 0);
lean_inc_ref(v_toConstantVal_3535_);
v_name_3536_ = lean_ctor_get(v_toConstantVal_3535_, 0);
v_levelParams_3537_ = lean_ctor_get(v_toConstantVal_3535_, 1);
v_isSharedCheck_3724_ = !lean_is_exclusive(v_toConstantVal_3535_);
if (v_isSharedCheck_3724_ == 0)
{
lean_object* v_unused_3725_; 
v_unused_3725_ = lean_ctor_get(v_toConstantVal_3535_, 2);
lean_dec(v_unused_3725_);
v___x_3539_ = v_toConstantVal_3535_;
v_isShared_3540_ = v_isSharedCheck_3724_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_levelParams_3537_);
lean_inc(v_name_3536_);
lean_dec(v_toConstantVal_3535_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3724_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3545_; 
v___x_3541_ = lean_array_fget(v_array_3523_, v_start_3524_);
v___x_3542_ = lean_unsigned_to_nat(1u);
v___x_3543_ = lean_nat_add(v_start_3524_, v___x_3542_);
lean_dec(v_start_3524_);
if (v_isShared_3533_ == 0)
{
lean_ctor_set(v___x_3532_, 1, v___x_3543_);
v___x_3545_ = v___x_3532_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_array_3523_);
lean_ctor_set(v_reuseFailAlloc_3723_, 1, v___x_3543_);
lean_ctor_set(v_reuseFailAlloc_3723_, 2, v_stop_3525_);
v___x_3545_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
uint8_t v___x_3546_; 
v___x_3546_ = l_Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0(v_typeNames_3499_, v_name_3536_);
if (v___x_3546_ == 0)
{
lean_object* v___x_3548_; 
lean_dec(v___x_3541_);
lean_del_object(v___x_3539_);
lean_dec(v_levelParams_3537_);
lean_dec(v_name_3536_);
if (v_isShared_3522_ == 0)
{
lean_ctor_set(v___x_3521_, 1, v___x_3545_);
v___x_3548_ = v___x_3521_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v_fst_3519_);
lean_ctor_set(v_reuseFailAlloc_3549_, 1, v___x_3545_);
v___x_3548_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
v_a_3512_ = v___x_3548_;
goto v___jp_3511_;
}
}
else
{
lean_object* v___x_3550_; 
lean_del_object(v___x_3521_);
lean_inc(v___y_3509_);
lean_inc_ref(v___y_3508_);
lean_inc(v___y_3507_);
lean_inc_ref(v___y_3506_);
lean_inc(v___y_3505_);
lean_inc_ref(v___y_3504_);
lean_inc(v_a_3534_);
v___x_3550_ = l_Lean_Elab_Deriving_mkInductArgNames(v_a_3534_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v_a_3551_; lean_object* v___x_3552_; 
v_a_3551_ = lean_ctor_get(v___x_3550_, 0);
lean_inc(v_a_3551_);
lean_dec_ref(v___x_3550_);
lean_inc(v_a_3551_);
v___x_3552_ = l_Lean_Elab_Deriving_mkImplicitBinders(v_a_3551_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
if (lean_obj_tag(v___x_3552_) == 0)
{
lean_object* v_a_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
v_a_3553_ = lean_ctor_get(v___x_3552_, 0);
lean_inc(v_a_3553_);
lean_dec_ref(v___x_3552_);
v___x_3554_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__14));
lean_inc(v___y_3509_);
lean_inc_ref(v___y_3508_);
lean_inc(v___y_3507_);
lean_inc_ref(v___y_3506_);
lean_inc(v___y_3505_);
lean_inc_ref(v___y_3504_);
lean_inc(v_a_3551_);
lean_inc(v_a_3534_);
v___x_3555_ = l_Lean_Elab_Deriving_mkInstImplicitBinders(v___x_3554_, v_a_3534_, v_a_3551_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_object* v_a_3556_; lean_object* v___x_3557_; size_t v_sz_3558_; size_t v___x_3559_; lean_object* v___x_3560_; 
v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
lean_inc(v_a_3556_);
lean_dec_ref(v___x_3555_);
v___x_3557_ = lean_array_mk(v_levelParams_3537_);
v_sz_3558_ = lean_array_size(v___x_3557_);
v___x_3559_ = ((size_t)0ULL);
lean_inc(v___y_3509_);
lean_inc_ref(v___y_3508_);
v___x_3560_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg(v_sz_3558_, v___x_3559_, v___x_3557_, v___y_3508_, v___y_3509_);
if (lean_obj_tag(v___x_3560_) == 0)
{
lean_object* v_a_3561_; lean_object* v___x_3562_; lean_object* v_fst_3563_; lean_object* v_snd_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3690_; 
v_a_3561_ = lean_ctor_get(v___x_3560_, 0);
lean_inc(v_a_3561_);
lean_dec_ref(v___x_3560_);
v___x_3562_ = l_Array_unzip___redArg(v_a_3561_);
lean_dec(v_a_3561_);
v_fst_3563_ = lean_ctor_get(v___x_3562_, 0);
v_snd_3564_ = lean_ctor_get(v___x_3562_, 1);
v_isSharedCheck_3690_ = !lean_is_exclusive(v___x_3562_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3566_ = v___x_3562_;
v_isShared_3567_ = v_isSharedCheck_3690_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_snd_3564_);
lean_inc(v_fst_3563_);
lean_dec(v___x_3562_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3690_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v___x_3568_; 
lean_inc(v_a_3551_);
lean_inc(v_a_3534_);
v___x_3568_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v_a_3534_, v_a_3551_, v___y_3508_);
if (lean_obj_tag(v___x_3568_) == 0)
{
lean_object* v_a_3569_; lean_object* v___x_3570_; 
v_a_3569_ = lean_ctor_get(v___x_3568_, 0);
lean_inc(v_a_3569_);
lean_dec_ref(v___x_3568_);
lean_inc_ref(v___y_3504_);
lean_inc(v_a_3534_);
v___x_3570_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType(v_a_3534_, v_a_3569_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
if (lean_obj_tag(v___x_3570_) == 0)
{
lean_object* v_a_3571_; lean_object* v___x_3572_; 
v_a_3571_ = lean_ctor_get(v___x_3570_, 0);
lean_inc(v_a_3571_);
lean_dec_ref(v___x_3570_);
lean_inc(v___y_3509_);
lean_inc_ref(v___y_3508_);
lean_inc(v___y_3507_);
lean_inc_ref(v___y_3506_);
lean_inc(v___y_3505_);
lean_inc_ref(v___y_3504_);
lean_inc(v_a_3534_);
v___x_3572_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr(v_a_3534_, v_a_3551_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
if (lean_obj_tag(v___x_3572_) == 0)
{
lean_object* v_a_3573_; lean_object* v___x_3574_; 
v_a_3573_ = lean_ctor_get(v___x_3572_, 0);
lean_inc(v_a_3573_);
lean_dec_ref(v___x_3572_);
lean_inc(v___y_3509_);
lean_inc_ref(v___y_3508_);
lean_inc(v___y_3507_);
lean_inc_ref(v___y_3506_);
lean_inc(v___y_3505_);
lean_inc_ref(v___y_3504_);
v___x_3574_ = l_Lean_Elab_Deriving_mkInstName(v___x_3554_, v_name_3536_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
if (lean_obj_tag(v___x_3574_) == 0)
{
lean_object* v_a_3575_; lean_object* v_ref_3576_; lean_object* v_quotContext_3577_; lean_object* v_currMacroScope_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; uint8_t v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3588_; 
v_a_3575_ = lean_ctor_get(v___x_3574_, 0);
lean_inc(v_a_3575_);
lean_dec_ref(v___x_3574_);
v_ref_3576_ = lean_ctor_get(v___y_3508_, 5);
v_quotContext_3577_ = lean_ctor_get(v___y_3508_, 10);
v_currMacroScope_3578_ = lean_ctor_get(v___y_3508_, 11);
v___x_3579_ = l_Array_append___redArg(v_a_3553_, v_a_3556_);
lean_dec(v_a_3556_);
v___x_3580_ = l_Array_append___redArg(v___x_3579_, v_snd_3564_);
lean_dec(v_snd_3564_);
v___x_3581_ = 0;
v___x_3582_ = l_Lean_SourceInfo_fromRef(v_ref_3576_, v___x_3581_);
v___x_3583_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__0));
v___x_3584_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__1));
v___x_3585_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_3586_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
lean_inc(v___x_3582_);
if (v_isShared_3540_ == 0)
{
lean_ctor_set_tag(v___x_3539_, 1);
lean_ctor_set(v___x_3539_, 2, v___x_3586_);
lean_ctor_set(v___x_3539_, 1, v___x_3585_);
lean_ctor_set(v___x_3539_, 0, v___x_3582_);
v___x_3588_ = v___x_3539_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v___x_3582_);
lean_ctor_set(v_reuseFailAlloc_3657_, 1, v___x_3585_);
lean_ctor_set(v_reuseFailAlloc_3657_, 2, v___x_3586_);
v___x_3588_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; size_t v_sz_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3655_; 
lean_inc_ref_n(v___x_3588_, 7);
lean_inc(v___x_3582_);
v___x_3589_ = l_Lean_Syntax_node7(v___x_3582_, v___x_3584_, v___x_3588_, v___x_3588_, v___x_3588_, v___x_3588_, v___x_3588_, v___x_3588_, v___x_3588_);
v___x_3590_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__2));
v___x_3591_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__3));
v___x_3592_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__5));
lean_inc_ref(v___x_3588_);
lean_inc(v___x_3582_);
v___x_3593_ = l_Lean_Syntax_node1(v___x_3582_, v___x_3592_, v___x_3588_);
lean_inc(v___x_3582_);
v___x_3594_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3594_, 0, v___x_3582_);
lean_ctor_set(v___x_3594_, 1, v___x_3590_);
v___x_3595_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__6));
v___x_3596_ = lean_mk_syntax_ident(v_a_3575_);
lean_inc_ref(v___x_3588_);
lean_inc(v___x_3582_);
v___x_3597_ = l_Lean_Syntax_node2(v___x_3582_, v___x_3595_, v___x_3596_, v___x_3588_);
lean_inc(v___x_3582_);
v___x_3598_ = l_Lean_Syntax_node1(v___x_3582_, v___x_3585_, v___x_3597_);
v___x_3599_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__8));
v___x_3600_ = l_Array_append___redArg(v___x_3586_, v___x_3580_);
lean_dec_ref(v___x_3580_);
lean_inc(v___x_3582_);
v___x_3601_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3601_, 0, v___x_3582_);
lean_ctor_set(v___x_3601_, 1, v___x_3585_);
lean_ctor_set(v___x_3601_, 2, v___x_3600_);
v___x_3602_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__10));
v___x_3603_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__11));
lean_inc(v___x_3582_);
v___x_3604_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3604_, 0, v___x_3582_);
lean_ctor_set(v___x_3604_, 1, v___x_3603_);
v___x_3605_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_3606_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__12);
v___x_3607_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__13));
lean_inc(v_currMacroScope_3578_);
lean_inc(v_quotContext_3577_);
v___x_3608_ = l_Lean_addMacroScope(v_quotContext_3577_, v___x_3607_, v_currMacroScope_3578_);
v___x_3609_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__26));
lean_inc(v___x_3582_);
v___x_3610_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3582_);
lean_ctor_set(v___x_3610_, 1, v___x_3606_);
lean_ctor_set(v___x_3610_, 2, v___x_3608_);
lean_ctor_set(v___x_3610_, 3, v___x_3609_);
lean_inc(v___x_3582_);
v___x_3611_ = l_Lean_Syntax_node1(v___x_3582_, v___x_3585_, v_a_3571_);
lean_inc(v___x_3582_);
v___x_3612_ = l_Lean_Syntax_node2(v___x_3582_, v___x_3605_, v___x_3610_, v___x_3611_);
lean_inc(v___x_3582_);
v___x_3613_ = l_Lean_Syntax_node2(v___x_3582_, v___x_3602_, v___x_3604_, v___x_3612_);
lean_inc(v___x_3582_);
v___x_3614_ = l_Lean_Syntax_node2(v___x_3582_, v___x_3599_, v___x_3601_, v___x_3613_);
v___x_3615_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__10));
v___x_3616_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__11));
lean_inc(v___x_3582_);
v___x_3617_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3582_);
lean_ctor_set(v___x_3617_, 1, v___x_3616_);
v___x_3618_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__32));
v___x_3619_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__34));
v___x_3620_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__36));
v___x_3621_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1);
v___x_3622_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__2));
lean_inc(v_currMacroScope_3578_);
lean_inc(v_quotContext_3577_);
v___x_3623_ = l_Lean_addMacroScope(v_quotContext_3577_, v___x_3622_, v_currMacroScope_3578_);
v___x_3624_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__6));
lean_inc(v___x_3582_);
v___x_3625_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3625_, 0, v___x_3582_);
lean_ctor_set(v___x_3625_, 1, v___x_3621_);
lean_ctor_set(v___x_3625_, 2, v___x_3623_);
lean_ctor_set(v___x_3625_, 3, v___x_3624_);
lean_inc_ref(v___x_3588_);
lean_inc(v___x_3582_);
v___x_3626_ = l_Lean_Syntax_node2(v___x_3582_, v___x_3620_, v___x_3625_, v___x_3588_);
v___x_3627_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__38));
v___x_3628_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__27));
lean_inc(v___x_3582_);
v___x_3629_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3629_, 0, v___x_3582_);
lean_ctor_set(v___x_3629_, 1, v___x_3628_);
v___x_3630_ = lean_mk_syntax_ident(v___x_3541_);
v_sz_3631_ = lean_array_size(v_fst_3563_);
v___x_3632_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__2(v_sz_3631_, v___x_3559_, v_fst_3563_);
v___x_3633_ = l_Array_append___redArg(v___x_3586_, v___x_3632_);
lean_dec_ref(v___x_3632_);
lean_inc(v___x_3582_);
v___x_3634_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3634_, 0, v___x_3582_);
lean_ctor_set(v___x_3634_, 1, v___x_3585_);
lean_ctor_set(v___x_3634_, 2, v___x_3633_);
lean_inc(v___x_3582_);
v___x_3635_ = l_Lean_Syntax_node2(v___x_3582_, v___x_3605_, v___x_3630_, v___x_3634_);
lean_inc_ref(v___x_3588_);
lean_inc_ref(v___x_3629_);
lean_inc(v___x_3582_);
v___x_3636_ = l_Lean_Syntax_node3(v___x_3582_, v___x_3627_, v___x_3629_, v___x_3588_, v___x_3635_);
lean_inc_ref_n(v___x_3588_, 2);
lean_inc(v___x_3582_);
v___x_3637_ = l_Lean_Syntax_node3(v___x_3582_, v___x_3585_, v___x_3588_, v___x_3588_, v___x_3636_);
lean_inc(v___x_3582_);
v___x_3638_ = l_Lean_Syntax_node2(v___x_3582_, v___x_3619_, v___x_3626_, v___x_3637_);
v___x_3639_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8);
v___x_3640_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__9));
lean_inc(v_currMacroScope_3578_);
lean_inc(v_quotContext_3577_);
v___x_3641_ = l_Lean_addMacroScope(v_quotContext_3577_, v___x_3640_, v_currMacroScope_3578_);
v___x_3642_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__12));
lean_inc(v___x_3582_);
v___x_3643_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3643_, 0, v___x_3582_);
lean_ctor_set(v___x_3643_, 1, v___x_3639_);
lean_ctor_set(v___x_3643_, 2, v___x_3641_);
lean_ctor_set(v___x_3643_, 3, v___x_3642_);
lean_inc_ref(v___x_3588_);
lean_inc(v___x_3582_);
v___x_3644_ = l_Lean_Syntax_node2(v___x_3582_, v___x_3620_, v___x_3643_, v___x_3588_);
lean_inc_ref(v___x_3588_);
lean_inc(v___x_3582_);
v___x_3645_ = l_Lean_Syntax_node3(v___x_3582_, v___x_3627_, v___x_3629_, v___x_3588_, v_a_3573_);
lean_inc_ref_n(v___x_3588_, 2);
lean_inc(v___x_3582_);
v___x_3646_ = l_Lean_Syntax_node3(v___x_3582_, v___x_3585_, v___x_3588_, v___x_3588_, v___x_3645_);
lean_inc(v___x_3582_);
v___x_3647_ = l_Lean_Syntax_node2(v___x_3582_, v___x_3619_, v___x_3644_, v___x_3646_);
lean_inc_ref(v___x_3588_);
lean_inc(v___x_3582_);
v___x_3648_ = l_Lean_Syntax_node3(v___x_3582_, v___x_3585_, v___x_3638_, v___x_3588_, v___x_3647_);
lean_inc(v___x_3582_);
v___x_3649_ = l_Lean_Syntax_node1(v___x_3582_, v___x_3618_, v___x_3648_);
lean_inc_ref(v___x_3588_);
lean_inc(v___x_3582_);
v___x_3650_ = l_Lean_Syntax_node3(v___x_3582_, v___x_3615_, v___x_3617_, v___x_3649_, v___x_3588_);
lean_inc(v___x_3582_);
v___x_3651_ = l_Lean_Syntax_node6(v___x_3582_, v___x_3591_, v___x_3593_, v___x_3594_, v___x_3588_, v___x_3598_, v___x_3614_, v___x_3650_);
v___x_3652_ = l_Lean_Syntax_node2(v___x_3582_, v___x_3583_, v___x_3589_, v___x_3651_);
v___x_3653_ = lean_array_push(v_fst_3519_, v___x_3652_);
if (v_isShared_3567_ == 0)
{
lean_ctor_set(v___x_3566_, 1, v___x_3545_);
lean_ctor_set(v___x_3566_, 0, v___x_3653_);
v___x_3655_ = v___x_3566_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v___x_3653_);
lean_ctor_set(v_reuseFailAlloc_3656_, 1, v___x_3545_);
v___x_3655_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
v_a_3512_ = v___x_3655_;
goto v___jp_3511_;
}
}
}
else
{
lean_object* v_a_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3665_; 
lean_dec(v_a_3573_);
lean_dec(v_a_3571_);
lean_del_object(v___x_3566_);
lean_dec(v_snd_3564_);
lean_dec(v_fst_3563_);
lean_dec(v_a_3556_);
lean_dec(v_a_3553_);
lean_dec_ref(v___x_3545_);
lean_dec(v___x_3541_);
lean_del_object(v___x_3539_);
lean_dec(v_fst_3519_);
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
v_a_3658_ = lean_ctor_get(v___x_3574_, 0);
v_isSharedCheck_3665_ = !lean_is_exclusive(v___x_3574_);
if (v_isSharedCheck_3665_ == 0)
{
v___x_3660_ = v___x_3574_;
v_isShared_3661_ = v_isSharedCheck_3665_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_a_3658_);
lean_dec(v___x_3574_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3665_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v___x_3663_; 
if (v_isShared_3661_ == 0)
{
v___x_3663_ = v___x_3660_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v_a_3658_);
v___x_3663_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
return v___x_3663_;
}
}
}
}
else
{
lean_object* v_a_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3673_; 
lean_dec(v_a_3571_);
lean_del_object(v___x_3566_);
lean_dec(v_snd_3564_);
lean_dec(v_fst_3563_);
lean_dec(v_a_3556_);
lean_dec(v_a_3553_);
lean_dec_ref(v___x_3545_);
lean_dec(v___x_3541_);
lean_del_object(v___x_3539_);
lean_dec(v_name_3536_);
lean_dec(v_fst_3519_);
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
v_a_3666_ = lean_ctor_get(v___x_3572_, 0);
v_isSharedCheck_3673_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_3673_ == 0)
{
v___x_3668_ = v___x_3572_;
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_a_3666_);
lean_dec(v___x_3572_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v___x_3671_; 
if (v_isShared_3669_ == 0)
{
v___x_3671_ = v___x_3668_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v_a_3666_);
v___x_3671_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
return v___x_3671_;
}
}
}
}
else
{
lean_object* v_a_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3681_; 
lean_del_object(v___x_3566_);
lean_dec(v_snd_3564_);
lean_dec(v_fst_3563_);
lean_dec(v_a_3556_);
lean_dec(v_a_3553_);
lean_dec(v_a_3551_);
lean_dec_ref(v___x_3545_);
lean_dec(v___x_3541_);
lean_del_object(v___x_3539_);
lean_dec(v_name_3536_);
lean_dec(v_fst_3519_);
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
v_a_3674_ = lean_ctor_get(v___x_3570_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v___x_3570_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3676_ = v___x_3570_;
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_a_3674_);
lean_dec(v___x_3570_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v___x_3679_; 
if (v_isShared_3677_ == 0)
{
v___x_3679_ = v___x_3676_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_a_3674_);
v___x_3679_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
return v___x_3679_;
}
}
}
}
else
{
lean_object* v_a_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3689_; 
lean_del_object(v___x_3566_);
lean_dec(v_snd_3564_);
lean_dec(v_fst_3563_);
lean_dec(v_a_3556_);
lean_dec(v_a_3553_);
lean_dec(v_a_3551_);
lean_dec_ref(v___x_3545_);
lean_dec(v___x_3541_);
lean_del_object(v___x_3539_);
lean_dec(v_name_3536_);
lean_dec(v_fst_3519_);
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
v_a_3682_ = lean_ctor_get(v___x_3568_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3568_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3684_ = v___x_3568_;
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_a_3682_);
lean_dec(v___x_3568_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3687_; 
if (v_isShared_3685_ == 0)
{
v___x_3687_ = v___x_3684_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_a_3682_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
}
}
}
else
{
lean_object* v_a_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3698_; 
lean_dec(v_a_3556_);
lean_dec(v_a_3553_);
lean_dec(v_a_3551_);
lean_dec_ref(v___x_3545_);
lean_dec(v___x_3541_);
lean_del_object(v___x_3539_);
lean_dec(v_name_3536_);
lean_dec(v_fst_3519_);
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
v_a_3691_ = lean_ctor_get(v___x_3560_, 0);
v_isSharedCheck_3698_ = !lean_is_exclusive(v___x_3560_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3693_ = v___x_3560_;
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_a_3691_);
lean_dec(v___x_3560_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v___x_3696_; 
if (v_isShared_3694_ == 0)
{
v___x_3696_ = v___x_3693_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_a_3691_);
v___x_3696_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
return v___x_3696_;
}
}
}
}
else
{
lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3706_; 
lean_dec(v_a_3553_);
lean_dec(v_a_3551_);
lean_dec_ref(v___x_3545_);
lean_dec(v___x_3541_);
lean_del_object(v___x_3539_);
lean_dec(v_levelParams_3537_);
lean_dec(v_name_3536_);
lean_dec(v_fst_3519_);
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
v_a_3699_ = lean_ctor_get(v___x_3555_, 0);
v_isSharedCheck_3706_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3701_ = v___x_3555_;
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_a_3699_);
lean_dec(v___x_3555_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3704_; 
if (v_isShared_3702_ == 0)
{
v___x_3704_ = v___x_3701_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_a_3699_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
}
}
else
{
lean_object* v_a_3707_; lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3714_; 
lean_dec(v_a_3551_);
lean_dec_ref(v___x_3545_);
lean_dec(v___x_3541_);
lean_del_object(v___x_3539_);
lean_dec(v_levelParams_3537_);
lean_dec(v_name_3536_);
lean_dec(v_fst_3519_);
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
v_a_3707_ = lean_ctor_get(v___x_3552_, 0);
v_isSharedCheck_3714_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3714_ == 0)
{
v___x_3709_ = v___x_3552_;
v_isShared_3710_ = v_isSharedCheck_3714_;
goto v_resetjp_3708_;
}
else
{
lean_inc(v_a_3707_);
lean_dec(v___x_3552_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3714_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
lean_object* v___x_3712_; 
if (v_isShared_3710_ == 0)
{
v___x_3712_ = v___x_3709_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v_a_3707_);
v___x_3712_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
return v___x_3712_;
}
}
}
}
else
{
lean_object* v_a_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3722_; 
lean_dec_ref(v___x_3545_);
lean_dec(v___x_3541_);
lean_del_object(v___x_3539_);
lean_dec(v_levelParams_3537_);
lean_dec(v_name_3536_);
lean_dec(v_fst_3519_);
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
v_a_3715_ = lean_ctor_get(v___x_3550_, 0);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3717_ = v___x_3550_;
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_a_3715_);
lean_dec(v___x_3550_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v___x_3720_; 
if (v_isShared_3718_ == 0)
{
v___x_3720_ = v___x_3717_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_a_3715_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
return v___x_3720_;
}
}
}
}
}
}
}
}
}
}
v___jp_3511_:
{
size_t v___x_3513_; size_t v___x_3514_; 
v___x_3513_ = ((size_t)1ULL);
v___x_3514_ = lean_usize_add(v_i_3502_, v___x_3513_);
v_i_3502_ = v___x_3514_;
v_b_3503_ = v_a_3512_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___boxed(lean_object* v_typeNames_3731_, lean_object* v_as_3732_, lean_object* v_sz_3733_, lean_object* v_i_3734_, lean_object* v_b_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_){
_start:
{
size_t v_sz_boxed_3743_; size_t v_i_boxed_3744_; lean_object* v_res_3745_; 
v_sz_boxed_3743_ = lean_unbox_usize(v_sz_3733_);
lean_dec(v_sz_3733_);
v_i_boxed_3744_ = lean_unbox_usize(v_i_3734_);
lean_dec(v_i_3734_);
v_res_3745_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3(v_typeNames_3731_, v_as_3732_, v_sz_boxed_3743_, v_i_boxed_3744_, v_b_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_);
lean_dec_ref(v_as_3732_);
lean_dec_ref(v_typeNames_3731_);
return v_res_3745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds(lean_object* v_ctx_3746_, lean_object* v_typeNames_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_, lean_object* v_a_3752_, lean_object* v_a_3753_){
_start:
{
lean_object* v_typeInfos_3755_; lean_object* v_auxFunNames_3756_; lean_object* v___x_3757_; lean_object* v_instances_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; size_t v_sz_3762_; size_t v___x_3763_; lean_object* v___x_3764_; 
v_typeInfos_3755_ = lean_ctor_get(v_ctx_3746_, 1);
lean_inc_ref(v_typeInfos_3755_);
v_auxFunNames_3756_ = lean_ctor_get(v_ctx_3746_, 2);
lean_inc_ref(v_auxFunNames_3756_);
lean_dec_ref(v_ctx_3746_);
v___x_3757_ = lean_unsigned_to_nat(0u);
v_instances_3758_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__0));
v___x_3759_ = lean_array_get_size(v_auxFunNames_3756_);
v___x_3760_ = l_Array_toSubarray___redArg(v_auxFunNames_3756_, v___x_3757_, v___x_3759_);
v___x_3761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3761_, 0, v_instances_3758_);
lean_ctor_set(v___x_3761_, 1, v___x_3760_);
v_sz_3762_ = lean_array_size(v_typeInfos_3755_);
v___x_3763_ = ((size_t)0ULL);
v___x_3764_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3(v_typeNames_3747_, v_typeInfos_3755_, v_sz_3762_, v___x_3763_, v___x_3761_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_, v_a_3753_);
lean_dec_ref(v_typeInfos_3755_);
if (lean_obj_tag(v___x_3764_) == 0)
{
lean_object* v_a_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3773_; 
v_a_3765_ = lean_ctor_get(v___x_3764_, 0);
v_isSharedCheck_3773_ = !lean_is_exclusive(v___x_3764_);
if (v_isSharedCheck_3773_ == 0)
{
v___x_3767_ = v___x_3764_;
v_isShared_3768_ = v_isSharedCheck_3773_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_a_3765_);
lean_dec(v___x_3764_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3773_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v_fst_3769_; lean_object* v___x_3771_; 
v_fst_3769_ = lean_ctor_get(v_a_3765_, 0);
lean_inc(v_fst_3769_);
lean_dec(v_a_3765_);
if (v_isShared_3768_ == 0)
{
lean_ctor_set(v___x_3767_, 0, v_fst_3769_);
v___x_3771_ = v___x_3767_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v_fst_3769_);
v___x_3771_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
return v___x_3771_;
}
}
}
else
{
lean_object* v_a_3774_; lean_object* v___x_3776_; uint8_t v_isShared_3777_; uint8_t v_isSharedCheck_3781_; 
v_a_3774_ = lean_ctor_get(v___x_3764_, 0);
v_isSharedCheck_3781_ = !lean_is_exclusive(v___x_3764_);
if (v_isSharedCheck_3781_ == 0)
{
v___x_3776_ = v___x_3764_;
v_isShared_3777_ = v_isSharedCheck_3781_;
goto v_resetjp_3775_;
}
else
{
lean_inc(v_a_3774_);
lean_dec(v___x_3764_);
v___x_3776_ = lean_box(0);
v_isShared_3777_ = v_isSharedCheck_3781_;
goto v_resetjp_3775_;
}
v_resetjp_3775_:
{
lean_object* v___x_3779_; 
if (v_isShared_3777_ == 0)
{
v___x_3779_ = v___x_3776_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_a_3774_);
v___x_3779_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
return v___x_3779_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds___boxed(lean_object* v_ctx_3782_, lean_object* v_typeNames_3783_, lean_object* v_a_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_){
_start:
{
lean_object* v_res_3791_; 
v_res_3791_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds(v_ctx_3782_, v_typeNames_3783_, v_a_3784_, v_a_3785_, v_a_3786_, v_a_3787_, v_a_3788_, v_a_3789_);
lean_dec_ref(v_typeNames_3783_);
return v_res_3791_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1(size_t v_sz_3792_, size_t v_i_3793_, lean_object* v_bs_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_){
_start:
{
lean_object* v___x_3802_; 
v___x_3802_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg(v_sz_3792_, v_i_3793_, v_bs_3794_, v___y_3799_, v___y_3800_);
return v___x_3802_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___boxed(lean_object* v_sz_3803_, lean_object* v_i_3804_, lean_object* v_bs_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_){
_start:
{
size_t v_sz_boxed_3813_; size_t v_i_boxed_3814_; lean_object* v_res_3815_; 
v_sz_boxed_3813_ = lean_unbox_usize(v_sz_3803_);
lean_dec(v_sz_3803_);
v_i_boxed_3814_ = lean_unbox_usize(v_i_3804_);
lean_dec(v_i_3804_);
v_res_3815_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1(v_sz_boxed_3813_, v_i_boxed_3814_, v_bs_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_);
lean_dec(v___y_3809_);
lean_dec_ref(v___y_3808_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
return v_res_3815_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__0___redArg(lean_object* v_cls_3819_, lean_object* v___y_3820_){
_start:
{
lean_object* v_options_3822_; uint8_t v_hasTrace_3823_; 
v_options_3822_ = lean_ctor_get(v___y_3820_, 2);
v_hasTrace_3823_ = lean_ctor_get_uint8(v_options_3822_, sizeof(void*)*1);
if (v_hasTrace_3823_ == 0)
{
lean_object* v___x_3824_; lean_object* v___x_3825_; 
lean_dec(v_cls_3819_);
v___x_3824_ = lean_box(v_hasTrace_3823_);
v___x_3825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3825_, 0, v___x_3824_);
return v___x_3825_;
}
else
{
lean_object* v_inheritedTraceOptions_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; uint8_t v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; 
v_inheritedTraceOptions_3826_ = lean_ctor_get(v___y_3820_, 13);
v___x_3827_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__0___redArg___closed__1));
v___x_3828_ = l_Lean_Name_append(v___x_3827_, v_cls_3819_);
v___x_3829_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3826_, v_options_3822_, v___x_3828_);
lean_dec(v___x_3828_);
v___x_3830_ = lean_box(v___x_3829_);
v___x_3831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3831_, 0, v___x_3830_);
return v___x_3831_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__0___redArg___boxed(lean_object* v_cls_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_){
_start:
{
lean_object* v_res_3835_; 
v_res_3835_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__0___redArg(v_cls_3832_, v___y_3833_);
lean_dec_ref(v___y_3833_);
return v_res_3835_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__0(lean_object* v_cls_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_){
_start:
{
lean_object* v___x_3844_; 
v___x_3844_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__0___redArg(v_cls_3836_, v___y_3841_);
return v___x_3844_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__0___boxed(lean_object* v_cls_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_){
_start:
{
lean_object* v_res_3853_; 
v_res_3853_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__0(v_cls_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_);
lean_dec(v___y_3851_);
lean_dec_ref(v___y_3850_);
lean_dec(v___y_3849_);
lean_dec_ref(v___y_3848_);
lean_dec(v___y_3847_);
lean_dec_ref(v___y_3846_);
return v_res_3853_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3854_; double v___x_3855_; 
v___x_3854_ = lean_unsigned_to_nat(0u);
v___x_3855_ = lean_float_of_nat(v___x_3854_);
return v___x_3855_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2___redArg(lean_object* v_cls_3859_, lean_object* v_msg_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_){
_start:
{
lean_object* v_ref_3866_; lean_object* v___x_3867_; lean_object* v_a_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3912_; 
v_ref_3866_ = lean_ctor_get(v___y_3863_, 5);
v___x_3867_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__0(v_msg_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_);
v_a_3868_ = lean_ctor_get(v___x_3867_, 0);
v_isSharedCheck_3912_ = !lean_is_exclusive(v___x_3867_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3870_ = v___x_3867_;
v_isShared_3871_ = v_isSharedCheck_3912_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_a_3868_);
lean_dec(v___x_3867_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3912_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v___x_3872_; lean_object* v_traceState_3873_; lean_object* v_env_3874_; lean_object* v_nextMacroScope_3875_; lean_object* v_ngen_3876_; lean_object* v_auxDeclNGen_3877_; lean_object* v_cache_3878_; lean_object* v_messages_3879_; lean_object* v_infoState_3880_; lean_object* v_snapshotTasks_3881_; lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3911_; 
v___x_3872_ = lean_st_ref_take(v___y_3864_);
v_traceState_3873_ = lean_ctor_get(v___x_3872_, 4);
v_env_3874_ = lean_ctor_get(v___x_3872_, 0);
v_nextMacroScope_3875_ = lean_ctor_get(v___x_3872_, 1);
v_ngen_3876_ = lean_ctor_get(v___x_3872_, 2);
v_auxDeclNGen_3877_ = lean_ctor_get(v___x_3872_, 3);
v_cache_3878_ = lean_ctor_get(v___x_3872_, 5);
v_messages_3879_ = lean_ctor_get(v___x_3872_, 6);
v_infoState_3880_ = lean_ctor_get(v___x_3872_, 7);
v_snapshotTasks_3881_ = lean_ctor_get(v___x_3872_, 8);
v_isSharedCheck_3911_ = !lean_is_exclusive(v___x_3872_);
if (v_isSharedCheck_3911_ == 0)
{
v___x_3883_ = v___x_3872_;
v_isShared_3884_ = v_isSharedCheck_3911_;
goto v_resetjp_3882_;
}
else
{
lean_inc(v_snapshotTasks_3881_);
lean_inc(v_infoState_3880_);
lean_inc(v_messages_3879_);
lean_inc(v_cache_3878_);
lean_inc(v_traceState_3873_);
lean_inc(v_auxDeclNGen_3877_);
lean_inc(v_ngen_3876_);
lean_inc(v_nextMacroScope_3875_);
lean_inc(v_env_3874_);
lean_dec(v___x_3872_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3911_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
uint64_t v_tid_3885_; lean_object* v_traces_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3910_; 
v_tid_3885_ = lean_ctor_get_uint64(v_traceState_3873_, sizeof(void*)*1);
v_traces_3886_ = lean_ctor_get(v_traceState_3873_, 0);
v_isSharedCheck_3910_ = !lean_is_exclusive(v_traceState_3873_);
if (v_isSharedCheck_3910_ == 0)
{
v___x_3888_ = v_traceState_3873_;
v_isShared_3889_ = v_isSharedCheck_3910_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_traces_3886_);
lean_dec(v_traceState_3873_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3910_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
lean_object* v___x_3890_; double v___x_3891_; uint8_t v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3900_; 
v___x_3890_ = lean_box(0);
v___x_3891_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2___redArg___closed__0);
v___x_3892_ = 0;
v___x_3893_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2___redArg___closed__1));
v___x_3894_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3894_, 0, v_cls_3859_);
lean_ctor_set(v___x_3894_, 1, v___x_3890_);
lean_ctor_set(v___x_3894_, 2, v___x_3893_);
lean_ctor_set_float(v___x_3894_, sizeof(void*)*3, v___x_3891_);
lean_ctor_set_float(v___x_3894_, sizeof(void*)*3 + 8, v___x_3891_);
lean_ctor_set_uint8(v___x_3894_, sizeof(void*)*3 + 16, v___x_3892_);
v___x_3895_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2___redArg___closed__2));
v___x_3896_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3896_, 0, v___x_3894_);
lean_ctor_set(v___x_3896_, 1, v_a_3868_);
lean_ctor_set(v___x_3896_, 2, v___x_3895_);
lean_inc(v_ref_3866_);
v___x_3897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3897_, 0, v_ref_3866_);
lean_ctor_set(v___x_3897_, 1, v___x_3896_);
v___x_3898_ = l_Lean_PersistentArray_push___redArg(v_traces_3886_, v___x_3897_);
if (v_isShared_3889_ == 0)
{
lean_ctor_set(v___x_3888_, 0, v___x_3898_);
v___x_3900_ = v___x_3888_;
goto v_reusejp_3899_;
}
else
{
lean_object* v_reuseFailAlloc_3909_; 
v_reuseFailAlloc_3909_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3909_, 0, v___x_3898_);
lean_ctor_set_uint64(v_reuseFailAlloc_3909_, sizeof(void*)*1, v_tid_3885_);
v___x_3900_ = v_reuseFailAlloc_3909_;
goto v_reusejp_3899_;
}
v_reusejp_3899_:
{
lean_object* v___x_3902_; 
if (v_isShared_3884_ == 0)
{
lean_ctor_set(v___x_3883_, 4, v___x_3900_);
v___x_3902_ = v___x_3883_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v_env_3874_);
lean_ctor_set(v_reuseFailAlloc_3908_, 1, v_nextMacroScope_3875_);
lean_ctor_set(v_reuseFailAlloc_3908_, 2, v_ngen_3876_);
lean_ctor_set(v_reuseFailAlloc_3908_, 3, v_auxDeclNGen_3877_);
lean_ctor_set(v_reuseFailAlloc_3908_, 4, v___x_3900_);
lean_ctor_set(v_reuseFailAlloc_3908_, 5, v_cache_3878_);
lean_ctor_set(v_reuseFailAlloc_3908_, 6, v_messages_3879_);
lean_ctor_set(v_reuseFailAlloc_3908_, 7, v_infoState_3880_);
lean_ctor_set(v_reuseFailAlloc_3908_, 8, v_snapshotTasks_3881_);
v___x_3902_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3906_; 
v___x_3903_ = lean_st_ref_set(v___y_3864_, v___x_3902_);
v___x_3904_ = lean_box(0);
if (v_isShared_3871_ == 0)
{
lean_ctor_set(v___x_3870_, 0, v___x_3904_);
v___x_3906_ = v___x_3870_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v___x_3904_);
v___x_3906_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
return v___x_3906_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2___redArg___boxed(lean_object* v_cls_3913_, lean_object* v_msg_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_){
_start:
{
lean_object* v_res_3920_; 
v_res_3920_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2___redArg(v_cls_3913_, v_msg_3914_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_);
lean_dec(v___y_3918_);
lean_dec_ref(v___y_3917_);
lean_dec(v___y_3916_);
lean_dec_ref(v___y_3915_);
return v_res_3920_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1(lean_object* v_a_3921_, lean_object* v_a_3922_){
_start:
{
if (lean_obj_tag(v_a_3921_) == 0)
{
lean_object* v___x_3923_; 
v___x_3923_ = l_List_reverse___redArg(v_a_3922_);
return v___x_3923_;
}
else
{
lean_object* v_head_3924_; lean_object* v_tail_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3934_; 
v_head_3924_ = lean_ctor_get(v_a_3921_, 0);
v_tail_3925_ = lean_ctor_get(v_a_3921_, 1);
v_isSharedCheck_3934_ = !lean_is_exclusive(v_a_3921_);
if (v_isSharedCheck_3934_ == 0)
{
v___x_3927_ = v_a_3921_;
v_isShared_3928_ = v_isSharedCheck_3934_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_tail_3925_);
lean_inc(v_head_3924_);
lean_dec(v_a_3921_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3934_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3929_; lean_object* v___x_3931_; 
v___x_3929_ = l_Lean_MessageData_ofSyntax(v_head_3924_);
if (v_isShared_3928_ == 0)
{
lean_ctor_set(v___x_3927_, 1, v_a_3922_);
lean_ctor_set(v___x_3927_, 0, v___x_3929_);
v___x_3931_ = v___x_3927_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v___x_3929_);
lean_ctor_set(v_reuseFailAlloc_3933_, 1, v_a_3922_);
v___x_3931_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
v_a_3921_ = v_tail_3925_;
v_a_3922_ = v___x_3931_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__2(void){
_start:
{
lean_object* v___x_3940_; lean_object* v___x_3941_; 
v___x_3940_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__1));
v___x_3941_ = l_Lean_stringToMessageData(v___x_3940_);
return v___x_3941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds(lean_object* v_declNames_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_){
_start:
{
lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; uint8_t v___x_3955_; lean_object* v___x_3956_; 
v___x_3950_ = lean_box(0);
v___x_3951_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__14));
v___x_3952_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__0));
v___x_3953_ = lean_unsigned_to_nat(0u);
v___x_3954_ = lean_array_get_borrowed(v___x_3950_, v_declNames_3942_, v___x_3953_);
v___x_3955_ = 1;
lean_inc(v_a_3948_);
lean_inc_ref(v_a_3947_);
lean_inc(v_a_3946_);
lean_inc_ref(v_a_3945_);
lean_inc(v_a_3944_);
lean_inc_ref(v_a_3943_);
lean_inc(v___x_3954_);
v___x_3956_ = l_Lean_Elab_Deriving_mkContext(v___x_3951_, v___x_3952_, v___x_3954_, v___x_3955_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_);
if (lean_obj_tag(v___x_3956_) == 0)
{
lean_object* v_a_3957_; lean_object* v___x_3958_; 
v_a_3957_ = lean_ctor_get(v___x_3956_, 0);
lean_inc(v_a_3957_);
lean_dec_ref(v___x_3956_);
lean_inc(v_a_3948_);
lean_inc_ref(v_a_3947_);
lean_inc(v_a_3946_);
lean_inc_ref(v_a_3945_);
lean_inc(v_a_3944_);
lean_inc_ref(v_a_3943_);
lean_inc(v_a_3957_);
v___x_3958_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions(v_a_3957_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_);
if (lean_obj_tag(v___x_3958_) == 0)
{
lean_object* v_a_3959_; lean_object* v___x_3960_; 
v_a_3959_ = lean_ctor_get(v___x_3958_, 0);
lean_inc(v_a_3959_);
lean_dec_ref(v___x_3958_);
lean_inc(v_a_3948_);
lean_inc_ref(v_a_3947_);
lean_inc(v_a_3946_);
lean_inc_ref(v_a_3945_);
v___x_3960_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds(v_a_3957_, v_declNames_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_);
if (lean_obj_tag(v___x_3960_) == 0)
{
lean_object* v_a_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v_a_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3999_; 
v_a_3961_ = lean_ctor_get(v___x_3960_, 0);
lean_inc(v_a_3961_);
lean_dec_ref(v___x_3960_);
v___x_3962_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__0));
v___x_3963_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__0___redArg(v___x_3962_, v_a_3947_);
v_a_3964_ = lean_ctor_get(v___x_3963_, 0);
v_isSharedCheck_3999_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_3999_ == 0)
{
v___x_3966_ = v___x_3963_;
v_isShared_3967_ = v_isSharedCheck_3999_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_a_3964_);
lean_dec(v___x_3963_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3999_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; uint8_t v___x_3972_; 
v___x_3968_ = lean_unsigned_to_nat(1u);
v___x_3969_ = lean_mk_empty_array_with_capacity(v___x_3968_);
v___x_3970_ = lean_array_push(v___x_3969_, v_a_3959_);
v___x_3971_ = l_Array_append___redArg(v___x_3970_, v_a_3961_);
lean_dec(v_a_3961_);
v___x_3972_ = lean_unbox(v_a_3964_);
lean_dec(v_a_3964_);
if (v___x_3972_ == 0)
{
lean_object* v___x_3974_; 
lean_dec(v_a_3948_);
lean_dec_ref(v_a_3947_);
lean_dec(v_a_3946_);
lean_dec_ref(v_a_3945_);
if (v_isShared_3967_ == 0)
{
lean_ctor_set(v___x_3966_, 0, v___x_3971_);
v___x_3974_ = v___x_3966_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v___x_3971_);
v___x_3974_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
return v___x_3974_;
}
}
else
{
lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; 
lean_del_object(v___x_3966_);
v___x_3976_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__2, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__2_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__2);
lean_inc_ref(v___x_3971_);
v___x_3977_ = lean_array_to_list(v___x_3971_);
v___x_3978_ = lean_box(0);
v___x_3979_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1(v___x_3977_, v___x_3978_);
v___x_3980_ = l_Lean_MessageData_ofList(v___x_3979_);
v___x_3981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3981_, 0, v___x_3976_);
lean_ctor_set(v___x_3981_, 1, v___x_3980_);
v___x_3982_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2___redArg(v___x_3962_, v___x_3981_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_);
lean_dec(v_a_3948_);
lean_dec_ref(v_a_3947_);
lean_dec(v_a_3946_);
lean_dec_ref(v_a_3945_);
if (lean_obj_tag(v___x_3982_) == 0)
{
lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_3989_; 
v_isSharedCheck_3989_ = !lean_is_exclusive(v___x_3982_);
if (v_isSharedCheck_3989_ == 0)
{
lean_object* v_unused_3990_; 
v_unused_3990_ = lean_ctor_get(v___x_3982_, 0);
lean_dec(v_unused_3990_);
v___x_3984_ = v___x_3982_;
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
else
{
lean_dec(v___x_3982_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___x_3987_; 
if (v_isShared_3985_ == 0)
{
lean_ctor_set(v___x_3984_, 0, v___x_3971_);
v___x_3987_ = v___x_3984_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v___x_3971_);
v___x_3987_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
return v___x_3987_;
}
}
}
else
{
lean_object* v_a_3991_; lean_object* v___x_3993_; uint8_t v_isShared_3994_; uint8_t v_isSharedCheck_3998_; 
lean_dec_ref(v___x_3971_);
v_a_3991_ = lean_ctor_get(v___x_3982_, 0);
v_isSharedCheck_3998_ = !lean_is_exclusive(v___x_3982_);
if (v_isSharedCheck_3998_ == 0)
{
v___x_3993_ = v___x_3982_;
v_isShared_3994_ = v_isSharedCheck_3998_;
goto v_resetjp_3992_;
}
else
{
lean_inc(v_a_3991_);
lean_dec(v___x_3982_);
v___x_3993_ = lean_box(0);
v_isShared_3994_ = v_isSharedCheck_3998_;
goto v_resetjp_3992_;
}
v_resetjp_3992_:
{
lean_object* v___x_3996_; 
if (v_isShared_3994_ == 0)
{
v___x_3996_ = v___x_3993_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v_a_3991_);
v___x_3996_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
return v___x_3996_;
}
}
}
}
}
}
else
{
lean_object* v_a_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4007_; 
lean_dec(v_a_3959_);
lean_dec(v_a_3948_);
lean_dec_ref(v_a_3947_);
lean_dec(v_a_3946_);
lean_dec_ref(v_a_3945_);
v_a_4000_ = lean_ctor_get(v___x_3960_, 0);
v_isSharedCheck_4007_ = !lean_is_exclusive(v___x_3960_);
if (v_isSharedCheck_4007_ == 0)
{
v___x_4002_ = v___x_3960_;
v_isShared_4003_ = v_isSharedCheck_4007_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_a_4000_);
lean_dec(v___x_3960_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4007_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
lean_object* v___x_4005_; 
if (v_isShared_4003_ == 0)
{
v___x_4005_ = v___x_4002_;
goto v_reusejp_4004_;
}
else
{
lean_object* v_reuseFailAlloc_4006_; 
v_reuseFailAlloc_4006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4006_, 0, v_a_4000_);
v___x_4005_ = v_reuseFailAlloc_4006_;
goto v_reusejp_4004_;
}
v_reusejp_4004_:
{
return v___x_4005_;
}
}
}
}
else
{
lean_object* v_a_4008_; lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4015_; 
lean_dec(v_a_3957_);
lean_dec(v_a_3948_);
lean_dec_ref(v_a_3947_);
lean_dec(v_a_3946_);
lean_dec_ref(v_a_3945_);
lean_dec(v_a_3944_);
lean_dec_ref(v_a_3943_);
v_a_4008_ = lean_ctor_get(v___x_3958_, 0);
v_isSharedCheck_4015_ = !lean_is_exclusive(v___x_3958_);
if (v_isSharedCheck_4015_ == 0)
{
v___x_4010_ = v___x_3958_;
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
else
{
lean_inc(v_a_4008_);
lean_dec(v___x_3958_);
v___x_4010_ = lean_box(0);
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
v_resetjp_4009_:
{
lean_object* v___x_4013_; 
if (v_isShared_4011_ == 0)
{
v___x_4013_ = v___x_4010_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v_a_4008_);
v___x_4013_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
return v___x_4013_;
}
}
}
}
else
{
lean_object* v_a_4016_; lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4023_; 
lean_dec(v_a_3948_);
lean_dec_ref(v_a_3947_);
lean_dec(v_a_3946_);
lean_dec_ref(v_a_3945_);
lean_dec(v_a_3944_);
lean_dec_ref(v_a_3943_);
v_a_4016_ = lean_ctor_get(v___x_3956_, 0);
v_isSharedCheck_4023_ = !lean_is_exclusive(v___x_3956_);
if (v_isSharedCheck_4023_ == 0)
{
v___x_4018_ = v___x_3956_;
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
else
{
lean_inc(v_a_4016_);
lean_dec(v___x_3956_);
v___x_4018_ = lean_box(0);
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
v_resetjp_4017_:
{
lean_object* v___x_4021_; 
if (v_isShared_4019_ == 0)
{
v___x_4021_ = v___x_4018_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_a_4016_);
v___x_4021_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
return v___x_4021_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___boxed(lean_object* v_declNames_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_){
_start:
{
lean_object* v_res_4032_; 
v_res_4032_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds(v_declNames_4024_, v_a_4025_, v_a_4026_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_);
lean_dec_ref(v_declNames_4024_);
return v_res_4032_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2(lean_object* v_cls_4033_, lean_object* v_msg_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_){
_start:
{
lean_object* v___x_4042_; 
v___x_4042_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2___redArg(v_cls_4033_, v_msg_4034_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_);
return v___x_4042_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2___boxed(lean_object* v_cls_4043_, lean_object* v_msg_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_){
_start:
{
lean_object* v_res_4052_; 
v_res_4052_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2(v_cls_4043_, v_msg_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_);
lean_dec(v___y_4050_);
lean_dec_ref(v___y_4049_);
lean_dec(v___y_4048_);
lean_dec_ref(v___y_4047_);
lean_dec(v___y_4046_);
lean_dec_ref(v___y_4045_);
return v_res_4052_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0___redArg(lean_object* v_declName_4053_, lean_object* v___y_4054_){
_start:
{
lean_object* v___x_4056_; lean_object* v_env_4057_; uint8_t v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; 
v___x_4056_ = lean_st_ref_get(v___y_4054_);
v_env_4057_ = lean_ctor_get(v___x_4056_, 0);
lean_inc_ref(v_env_4057_);
lean_dec(v___x_4056_);
v___x_4058_ = l_Lean_isInductiveCore(v_env_4057_, v_declName_4053_);
v___x_4059_ = lean_box(v___x_4058_);
v___x_4060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4060_, 0, v___x_4059_);
return v___x_4060_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0___redArg___boxed(lean_object* v_declName_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_){
_start:
{
lean_object* v_res_4064_; 
v_res_4064_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0___redArg(v_declName_4061_, v___y_4062_);
lean_dec(v___y_4062_);
return v_res_4064_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0(lean_object* v_declName_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_){
_start:
{
lean_object* v___x_4069_; 
v___x_4069_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0___redArg(v_declName_4065_, v___y_4067_);
return v___x_4069_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0___boxed(lean_object* v_declName_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_){
_start:
{
lean_object* v_res_4074_; 
v_res_4074_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0(v_declName_4070_, v___y_4071_, v___y_4072_);
lean_dec(v___y_4072_);
lean_dec_ref(v___y_4071_);
return v_res_4074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__0(uint8_t v_____do__lift_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_){
_start:
{
if (v_____do__lift_4075_ == 0)
{
uint8_t v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; 
v___x_4079_ = 1;
v___x_4080_ = lean_box(v___x_4079_);
v___x_4081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4081_, 0, v___x_4080_);
return v___x_4081_;
}
else
{
uint8_t v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; 
v___x_4082_ = 0;
v___x_4083_ = lean_box(v___x_4082_);
v___x_4084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4084_, 0, v___x_4083_);
return v___x_4084_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__0___boxed(lean_object* v_____do__lift_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_){
_start:
{
uint8_t v_____do__lift_1844__boxed_4089_; lean_object* v_res_4090_; 
v_____do__lift_1844__boxed_4089_ = lean_unbox(v_____do__lift_4085_);
v_res_4090_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__0(v_____do__lift_1844__boxed_4089_, v___y_4086_, v___y_4087_);
lean_dec(v___y_4087_);
lean_dec_ref(v___y_4086_);
return v_res_4090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1_spec__1(lean_object* v_o_4091_, lean_object* v_k_4092_, uint8_t v_v_4093_){
_start:
{
lean_object* v_map_4094_; uint8_t v_hasTrace_4095_; lean_object* v___x_4097_; uint8_t v_isShared_4098_; uint8_t v_isSharedCheck_4109_; 
v_map_4094_ = lean_ctor_get(v_o_4091_, 0);
v_hasTrace_4095_ = lean_ctor_get_uint8(v_o_4091_, sizeof(void*)*1);
v_isSharedCheck_4109_ = !lean_is_exclusive(v_o_4091_);
if (v_isSharedCheck_4109_ == 0)
{
v___x_4097_ = v_o_4091_;
v_isShared_4098_ = v_isSharedCheck_4109_;
goto v_resetjp_4096_;
}
else
{
lean_inc(v_map_4094_);
lean_dec(v_o_4091_);
v___x_4097_ = lean_box(0);
v_isShared_4098_ = v_isSharedCheck_4109_;
goto v_resetjp_4096_;
}
v_resetjp_4096_:
{
lean_object* v___x_4099_; lean_object* v___x_4100_; 
v___x_4099_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4099_, 0, v_v_4093_);
lean_inc(v_k_4092_);
v___x_4100_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4092_, v___x_4099_, v_map_4094_);
if (v_hasTrace_4095_ == 0)
{
lean_object* v___x_4101_; uint8_t v___x_4102_; lean_object* v___x_4104_; 
v___x_4101_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__0___redArg___closed__1));
v___x_4102_ = l_Lean_Name_isPrefixOf(v___x_4101_, v_k_4092_);
lean_dec(v_k_4092_);
if (v_isShared_4098_ == 0)
{
lean_ctor_set(v___x_4097_, 0, v___x_4100_);
v___x_4104_ = v___x_4097_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v___x_4100_);
v___x_4104_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
lean_ctor_set_uint8(v___x_4104_, sizeof(void*)*1, v___x_4102_);
return v___x_4104_;
}
}
else
{
lean_object* v___x_4107_; 
lean_dec(v_k_4092_);
if (v_isShared_4098_ == 0)
{
lean_ctor_set(v___x_4097_, 0, v___x_4100_);
v___x_4107_ = v___x_4097_;
goto v_reusejp_4106_;
}
else
{
lean_object* v_reuseFailAlloc_4108_; 
v_reuseFailAlloc_4108_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4108_, 0, v___x_4100_);
lean_ctor_set_uint8(v_reuseFailAlloc_4108_, sizeof(void*)*1, v_hasTrace_4095_);
v___x_4107_ = v_reuseFailAlloc_4108_;
goto v_reusejp_4106_;
}
v_reusejp_4106_:
{
return v___x_4107_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1_spec__1___boxed(lean_object* v_o_4110_, lean_object* v_k_4111_, lean_object* v_v_4112_){
_start:
{
uint8_t v_v_boxed_4113_; lean_object* v_res_4114_; 
v_v_boxed_4113_ = lean_unbox(v_v_4112_);
v_res_4114_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1_spec__1(v_o_4110_, v_k_4111_, v_v_boxed_4113_);
return v_res_4114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1(lean_object* v_opts_4115_, lean_object* v_opt_4116_, uint8_t v_val_4117_){
_start:
{
lean_object* v_name_4118_; lean_object* v___x_4119_; 
v_name_4118_ = lean_ctor_get(v_opt_4116_, 0);
lean_inc(v_name_4118_);
lean_dec_ref(v_opt_4116_);
v___x_4119_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1_spec__1(v_opts_4115_, v_name_4118_, v_val_4117_);
return v___x_4119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1___boxed(lean_object* v_opts_4120_, lean_object* v_opt_4121_, lean_object* v_val_4122_){
_start:
{
uint8_t v_val_boxed_4123_; lean_object* v_res_4124_; 
v_val_boxed_4123_ = lean_unbox(v_val_4122_);
v_res_4124_ = l_Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1(v_opts_4120_, v_opt_4121_, v_val_boxed_4123_);
return v_res_4124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__1(uint8_t v_a_4125_, lean_object* v_scope_4126_){
_start:
{
lean_object* v_header_4127_; lean_object* v_opts_4128_; lean_object* v_currNamespace_4129_; lean_object* v_openDecls_4130_; lean_object* v_levelNames_4131_; lean_object* v_varDecls_4132_; lean_object* v_varUIds_4133_; lean_object* v_includedVars_4134_; lean_object* v_omittedVars_4135_; uint8_t v_isNoncomputable_4136_; uint8_t v_isPublic_4137_; uint8_t v_isMeta_4138_; lean_object* v_attrs_4139_; lean_object* v___x_4141_; uint8_t v_isShared_4142_; uint8_t v_isSharedCheck_4148_; 
v_header_4127_ = lean_ctor_get(v_scope_4126_, 0);
v_opts_4128_ = lean_ctor_get(v_scope_4126_, 1);
v_currNamespace_4129_ = lean_ctor_get(v_scope_4126_, 2);
v_openDecls_4130_ = lean_ctor_get(v_scope_4126_, 3);
v_levelNames_4131_ = lean_ctor_get(v_scope_4126_, 4);
v_varDecls_4132_ = lean_ctor_get(v_scope_4126_, 5);
v_varUIds_4133_ = lean_ctor_get(v_scope_4126_, 6);
v_includedVars_4134_ = lean_ctor_get(v_scope_4126_, 7);
v_omittedVars_4135_ = lean_ctor_get(v_scope_4126_, 8);
v_isNoncomputable_4136_ = lean_ctor_get_uint8(v_scope_4126_, sizeof(void*)*10);
v_isPublic_4137_ = lean_ctor_get_uint8(v_scope_4126_, sizeof(void*)*10 + 1);
v_isMeta_4138_ = lean_ctor_get_uint8(v_scope_4126_, sizeof(void*)*10 + 2);
v_attrs_4139_ = lean_ctor_get(v_scope_4126_, 9);
v_isSharedCheck_4148_ = !lean_is_exclusive(v_scope_4126_);
if (v_isSharedCheck_4148_ == 0)
{
v___x_4141_ = v_scope_4126_;
v_isShared_4142_ = v_isSharedCheck_4148_;
goto v_resetjp_4140_;
}
else
{
lean_inc(v_attrs_4139_);
lean_inc(v_omittedVars_4135_);
lean_inc(v_includedVars_4134_);
lean_inc(v_varUIds_4133_);
lean_inc(v_varDecls_4132_);
lean_inc(v_levelNames_4131_);
lean_inc(v_openDecls_4130_);
lean_inc(v_currNamespace_4129_);
lean_inc(v_opts_4128_);
lean_inc(v_header_4127_);
lean_dec(v_scope_4126_);
v___x_4141_ = lean_box(0);
v_isShared_4142_ = v_isSharedCheck_4148_;
goto v_resetjp_4140_;
}
v_resetjp_4140_:
{
lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4146_; 
v___x_4143_ = l_Lean_Elab_autoImplicit;
v___x_4144_ = l_Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1(v_opts_4128_, v___x_4143_, v_a_4125_);
if (v_isShared_4142_ == 0)
{
lean_ctor_set(v___x_4141_, 1, v___x_4144_);
v___x_4146_ = v___x_4141_;
goto v_reusejp_4145_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_header_4127_);
lean_ctor_set(v_reuseFailAlloc_4147_, 1, v___x_4144_);
lean_ctor_set(v_reuseFailAlloc_4147_, 2, v_currNamespace_4129_);
lean_ctor_set(v_reuseFailAlloc_4147_, 3, v_openDecls_4130_);
lean_ctor_set(v_reuseFailAlloc_4147_, 4, v_levelNames_4131_);
lean_ctor_set(v_reuseFailAlloc_4147_, 5, v_varDecls_4132_);
lean_ctor_set(v_reuseFailAlloc_4147_, 6, v_varUIds_4133_);
lean_ctor_set(v_reuseFailAlloc_4147_, 7, v_includedVars_4134_);
lean_ctor_set(v_reuseFailAlloc_4147_, 8, v_omittedVars_4135_);
lean_ctor_set(v_reuseFailAlloc_4147_, 9, v_attrs_4139_);
lean_ctor_set_uint8(v_reuseFailAlloc_4147_, sizeof(void*)*10, v_isNoncomputable_4136_);
lean_ctor_set_uint8(v_reuseFailAlloc_4147_, sizeof(void*)*10 + 1, v_isPublic_4137_);
lean_ctor_set_uint8(v_reuseFailAlloc_4147_, sizeof(void*)*10 + 2, v_isMeta_4138_);
v___x_4146_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4145_;
}
v_reusejp_4145_:
{
return v___x_4146_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__1___boxed(lean_object* v_a_4149_, lean_object* v_scope_4150_){
_start:
{
uint8_t v_a_1902__boxed_4151_; lean_object* v_res_4152_; 
v_a_1902__boxed_4151_ = lean_unbox(v_a_4149_);
v_res_4152_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__1(v_a_1902__boxed_4151_, v_scope_4150_);
return v_res_4152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__2(lean_object* v_as_4153_, size_t v_i_4154_, size_t v_stop_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_){
_start:
{
uint8_t v___x_4159_; 
v___x_4159_ = lean_usize_dec_eq(v_i_4154_, v_stop_4155_);
if (v___x_4159_ == 0)
{
uint8_t v___x_4160_; uint8_t v_a_4162_; lean_object* v___x_4168_; lean_object* v___x_4169_; 
v___x_4160_ = 1;
v___x_4168_ = lean_array_uget_borrowed(v_as_4153_, v_i_4154_);
lean_inc(v___x_4168_);
v___x_4169_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0___redArg(v___x_4168_, v___y_4157_);
if (lean_obj_tag(v___x_4169_) == 0)
{
lean_object* v_a_4170_; lean_object* v___x_4172_; uint8_t v_isShared_4173_; uint8_t v_isSharedCheck_4179_; 
v_a_4170_ = lean_ctor_get(v___x_4169_, 0);
v_isSharedCheck_4179_ = !lean_is_exclusive(v___x_4169_);
if (v_isSharedCheck_4179_ == 0)
{
v___x_4172_ = v___x_4169_;
v_isShared_4173_ = v_isSharedCheck_4179_;
goto v_resetjp_4171_;
}
else
{
lean_inc(v_a_4170_);
lean_dec(v___x_4169_);
v___x_4172_ = lean_box(0);
v_isShared_4173_ = v_isSharedCheck_4179_;
goto v_resetjp_4171_;
}
v_resetjp_4171_:
{
uint8_t v___x_4174_; 
v___x_4174_ = lean_unbox(v_a_4170_);
lean_dec(v_a_4170_);
if (v___x_4174_ == 0)
{
lean_object* v___x_4175_; lean_object* v___x_4177_; 
v___x_4175_ = lean_box(v___x_4160_);
if (v_isShared_4173_ == 0)
{
lean_ctor_set(v___x_4172_, 0, v___x_4175_);
v___x_4177_ = v___x_4172_;
goto v_reusejp_4176_;
}
else
{
lean_object* v_reuseFailAlloc_4178_; 
v_reuseFailAlloc_4178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4178_, 0, v___x_4175_);
v___x_4177_ = v_reuseFailAlloc_4178_;
goto v_reusejp_4176_;
}
v_reusejp_4176_:
{
return v___x_4177_;
}
}
else
{
lean_del_object(v___x_4172_);
v_a_4162_ = v___x_4159_;
goto v___jp_4161_;
}
}
}
else
{
if (lean_obj_tag(v___x_4169_) == 0)
{
lean_object* v_a_4180_; uint8_t v___x_4181_; 
v_a_4180_ = lean_ctor_get(v___x_4169_, 0);
lean_inc(v_a_4180_);
lean_dec_ref(v___x_4169_);
v___x_4181_ = lean_unbox(v_a_4180_);
lean_dec(v_a_4180_);
v_a_4162_ = v___x_4181_;
goto v___jp_4161_;
}
else
{
return v___x_4169_;
}
}
v___jp_4161_:
{
if (v_a_4162_ == 0)
{
size_t v___x_4163_; size_t v___x_4164_; 
v___x_4163_ = ((size_t)1ULL);
v___x_4164_ = lean_usize_add(v_i_4154_, v___x_4163_);
v_i_4154_ = v___x_4164_;
goto _start;
}
else
{
lean_object* v___x_4166_; lean_object* v___x_4167_; 
v___x_4166_ = lean_box(v___x_4160_);
v___x_4167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4166_);
return v___x_4167_;
}
}
}
else
{
uint8_t v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; 
v___x_4182_ = 0;
v___x_4183_ = lean_box(v___x_4182_);
v___x_4184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4184_, 0, v___x_4183_);
return v___x_4184_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__2___boxed(lean_object* v_as_4185_, lean_object* v_i_4186_, lean_object* v_stop_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_){
_start:
{
size_t v_i_boxed_4191_; size_t v_stop_boxed_4192_; lean_object* v_res_4193_; 
v_i_boxed_4191_ = lean_unbox_usize(v_i_4186_);
lean_dec(v_i_4186_);
v_stop_boxed_4192_ = lean_unbox_usize(v_stop_4187_);
lean_dec(v_stop_4187_);
v_res_4193_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__2(v_as_4185_, v_i_boxed_4191_, v_stop_boxed_4192_, v___y_4188_, v___y_4189_);
lean_dec(v___y_4189_);
lean_dec_ref(v___y_4188_);
lean_dec_ref(v_as_4185_);
return v_res_4193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler(lean_object* v_declNames_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_){
_start:
{
lean_object* v___x_4198_; lean_object* v___x_4199_; uint8_t v___x_4200_; uint8_t v_a_4202_; lean_object* v___y_4242_; 
v___x_4198_ = lean_unsigned_to_nat(0u);
v___x_4199_ = lean_array_get_size(v_declNames_4194_);
v___x_4200_ = lean_nat_dec_lt(v___x_4198_, v___x_4199_);
if (v___x_4200_ == 0)
{
lean_object* v___x_4246_; 
v___x_4246_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__0(v___x_4200_, v_a_4195_, v_a_4196_);
v___y_4242_ = v___x_4246_;
goto v___jp_4241_;
}
else
{
if (v___x_4200_ == 0)
{
v_a_4202_ = v___x_4200_;
goto v___jp_4201_;
}
else
{
size_t v___x_4247_; size_t v___x_4248_; lean_object* v___x_4249_; 
v___x_4247_ = ((size_t)0ULL);
v___x_4248_ = lean_usize_of_nat(v___x_4199_);
v___x_4249_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__2(v_declNames_4194_, v___x_4247_, v___x_4248_, v_a_4195_, v_a_4196_);
if (lean_obj_tag(v___x_4249_) == 0)
{
lean_object* v_a_4250_; uint8_t v___x_4251_; lean_object* v___x_4252_; 
v_a_4250_ = lean_ctor_get(v___x_4249_, 0);
lean_inc(v_a_4250_);
lean_dec_ref(v___x_4249_);
v___x_4251_ = lean_unbox(v_a_4250_);
lean_dec(v_a_4250_);
v___x_4252_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__0(v___x_4251_, v_a_4195_, v_a_4196_);
v___y_4242_ = v___x_4252_;
goto v___jp_4241_;
}
else
{
v___y_4242_ = v___x_4249_;
goto v___jp_4241_;
}
}
}
v___jp_4201_:
{
if (v___x_4200_ == 0)
{
lean_object* v___x_4203_; lean_object* v___x_4204_; 
lean_dec(v_a_4196_);
lean_dec_ref(v_a_4195_);
lean_dec_ref(v_declNames_4194_);
v___x_4203_ = lean_box(v___x_4200_);
v___x_4204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4204_, 0, v___x_4203_);
return v___x_4204_;
}
else
{
lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; 
v___x_4205_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___boxed), 8, 1);
lean_closure_set(v___x_4205_, 0, v_declNames_4194_);
v___x_4206_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftTermElabM___boxed), 5, 2);
lean_closure_set(v___x_4206_, 0, lean_box(0));
lean_closure_set(v___x_4206_, 1, v___x_4205_);
lean_inc(v_a_4196_);
lean_inc_ref(v_a_4195_);
v___x_4207_ = l_Lean_Elab_Command_withFreshMacroScope___redArg(v___x_4206_, v_a_4195_, v_a_4196_);
if (lean_obj_tag(v___x_4207_) == 0)
{
lean_object* v_a_4208_; lean_object* v___x_4209_; lean_object* v___f_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; 
v_a_4208_ = lean_ctor_get(v___x_4207_, 0);
lean_inc(v_a_4208_);
lean_dec_ref(v___x_4207_);
v___x_4209_ = lean_box(v_a_4202_);
v___f_4210_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__1___boxed), 2, 1);
lean_closure_set(v___f_4210_, 0, v___x_4209_);
v___x_4211_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_4212_ = lean_box(2);
v___x_4213_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4213_, 0, v___x_4212_);
lean_ctor_set(v___x_4213_, 1, v___x_4211_);
lean_ctor_set(v___x_4213_, 2, v_a_4208_);
v___x_4214_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(v___x_4214_, 0, v___x_4213_);
v___x_4215_ = l_Lean_Elab_Command_withScope___redArg(v___f_4210_, v___x_4214_, v_a_4195_, v_a_4196_);
if (lean_obj_tag(v___x_4215_) == 0)
{
lean_object* v___x_4217_; uint8_t v_isShared_4218_; uint8_t v_isSharedCheck_4223_; 
v_isSharedCheck_4223_ = !lean_is_exclusive(v___x_4215_);
if (v_isSharedCheck_4223_ == 0)
{
lean_object* v_unused_4224_; 
v_unused_4224_ = lean_ctor_get(v___x_4215_, 0);
lean_dec(v_unused_4224_);
v___x_4217_ = v___x_4215_;
v_isShared_4218_ = v_isSharedCheck_4223_;
goto v_resetjp_4216_;
}
else
{
lean_dec(v___x_4215_);
v___x_4217_ = lean_box(0);
v_isShared_4218_ = v_isSharedCheck_4223_;
goto v_resetjp_4216_;
}
v_resetjp_4216_:
{
lean_object* v___x_4219_; lean_object* v___x_4221_; 
v___x_4219_ = lean_box(v_a_4202_);
if (v_isShared_4218_ == 0)
{
lean_ctor_set(v___x_4217_, 0, v___x_4219_);
v___x_4221_ = v___x_4217_;
goto v_reusejp_4220_;
}
else
{
lean_object* v_reuseFailAlloc_4222_; 
v_reuseFailAlloc_4222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4222_, 0, v___x_4219_);
v___x_4221_ = v_reuseFailAlloc_4222_;
goto v_reusejp_4220_;
}
v_reusejp_4220_:
{
return v___x_4221_;
}
}
}
else
{
lean_object* v_a_4225_; lean_object* v___x_4227_; uint8_t v_isShared_4228_; uint8_t v_isSharedCheck_4232_; 
v_a_4225_ = lean_ctor_get(v___x_4215_, 0);
v_isSharedCheck_4232_ = !lean_is_exclusive(v___x_4215_);
if (v_isSharedCheck_4232_ == 0)
{
v___x_4227_ = v___x_4215_;
v_isShared_4228_ = v_isSharedCheck_4232_;
goto v_resetjp_4226_;
}
else
{
lean_inc(v_a_4225_);
lean_dec(v___x_4215_);
v___x_4227_ = lean_box(0);
v_isShared_4228_ = v_isSharedCheck_4232_;
goto v_resetjp_4226_;
}
v_resetjp_4226_:
{
lean_object* v___x_4230_; 
if (v_isShared_4228_ == 0)
{
v___x_4230_ = v___x_4227_;
goto v_reusejp_4229_;
}
else
{
lean_object* v_reuseFailAlloc_4231_; 
v_reuseFailAlloc_4231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4231_, 0, v_a_4225_);
v___x_4230_ = v_reuseFailAlloc_4231_;
goto v_reusejp_4229_;
}
v_reusejp_4229_:
{
return v___x_4230_;
}
}
}
}
else
{
lean_object* v_a_4233_; lean_object* v___x_4235_; uint8_t v_isShared_4236_; uint8_t v_isSharedCheck_4240_; 
lean_dec(v_a_4196_);
lean_dec_ref(v_a_4195_);
v_a_4233_ = lean_ctor_get(v___x_4207_, 0);
v_isSharedCheck_4240_ = !lean_is_exclusive(v___x_4207_);
if (v_isSharedCheck_4240_ == 0)
{
v___x_4235_ = v___x_4207_;
v_isShared_4236_ = v_isSharedCheck_4240_;
goto v_resetjp_4234_;
}
else
{
lean_inc(v_a_4233_);
lean_dec(v___x_4207_);
v___x_4235_ = lean_box(0);
v_isShared_4236_ = v_isSharedCheck_4240_;
goto v_resetjp_4234_;
}
v_resetjp_4234_:
{
lean_object* v___x_4238_; 
if (v_isShared_4236_ == 0)
{
v___x_4238_ = v___x_4235_;
goto v_reusejp_4237_;
}
else
{
lean_object* v_reuseFailAlloc_4239_; 
v_reuseFailAlloc_4239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4239_, 0, v_a_4233_);
v___x_4238_ = v_reuseFailAlloc_4239_;
goto v_reusejp_4237_;
}
v_reusejp_4237_:
{
return v___x_4238_;
}
}
}
}
}
v___jp_4241_:
{
if (lean_obj_tag(v___y_4242_) == 0)
{
lean_object* v_a_4243_; uint8_t v___x_4244_; 
v_a_4243_ = lean_ctor_get(v___y_4242_, 0);
v___x_4244_ = lean_unbox(v_a_4243_);
if (v___x_4244_ == 0)
{
lean_dec(v_a_4196_);
lean_dec_ref(v_a_4195_);
lean_dec_ref(v_declNames_4194_);
return v___y_4242_;
}
else
{
uint8_t v___x_4245_; 
lean_inc(v_a_4243_);
lean_dec_ref(v___y_4242_);
v___x_4245_ = lean_unbox(v_a_4243_);
lean_dec(v_a_4243_);
v_a_4202_ = v___x_4245_;
goto v___jp_4201_;
}
}
else
{
lean_dec(v_a_4196_);
lean_dec_ref(v_a_4195_);
lean_dec_ref(v_declNames_4194_);
return v___y_4242_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___boxed(lean_object* v_declNames_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_){
_start:
{
lean_object* v_res_4257_; 
v_res_4257_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler(v_declNames_4253_, v_a_4254_, v_a_4255_);
return v_res_4257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; 
v___x_4325_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__14));
v___x_4326_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__0_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_));
v___x_4327_ = l_Lean_Elab_registerDerivingHandler(v___x_4325_, v___x_4326_);
if (lean_obj_tag(v___x_4327_) == 0)
{
lean_object* v___x_4328_; uint8_t v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; 
lean_dec_ref(v___x_4327_);
v___x_4328_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__0));
v___x_4329_ = 0;
v___x_4330_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__25_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_));
v___x_4331_ = l_Lean_registerTraceClass(v___x_4328_, v___x_4329_, v___x_4330_);
return v___x_4331_;
}
else
{
return v___x_4327_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2____boxed(lean_object* v_a_4332_){
_start:
{
lean_object* v_res_4333_; 
v_res_4333_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_();
return v_res_4333_;
}
}
lean_object* runtime_initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Deriving_ToExpr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Deriving_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Deriving_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Deriving_ToExpr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Deriving_ToExpr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Deriving_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Deriving_ToExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Deriving_ToExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Deriving_ToExpr(builtin);
}
#ifdef __cplusplus
}
#endif
