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
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
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
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdent(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
lean_object* l_Lean_quoteNameMk(lean_object*);
lean_object* lean_string_intercalate(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
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
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkInductArgNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_Elab_Deriving_mkImplicitBinders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkInductiveApp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_autoImplicit;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkContext(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkInstImplicitBinders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkInstName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withFreshMacroScope___redArg(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "quotedName"};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__15 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__16_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__16_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__16_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__15_value),LEAN_SCALAR_PTR_LITERAL(217, 120, 158, 75, 195, 162, 2, 130)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__16 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__16_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__17 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__17_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__18 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__18_value;
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
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__2;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(199, 20, 136, 12, 168, 217, 46, 241)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__3_value;
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
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__0;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__1 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__1_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__2;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__3 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__3_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__4_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__5 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__5_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__6;
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__0(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__0_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(195, 196, 35, 37, 101, 57, 52, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__0_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 5, 156, 161, 41, 140, 236, 158)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__1_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__3;
static const lean_string_object l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_toCold_45_; lean_object* v_ref_46_; lean_object* v_quotContext_47_; lean_object* v_currMacroScope_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; size_t v___x_60_; size_t v___x_61_; 
v_toCold_45_ = lean_ctor_get(v___y_42_, 0);
v_ref_46_ = lean_ctor_get(v___y_42_, 2);
v_quotContext_47_ = lean_ctor_get(v_toCold_45_, 8);
v_currMacroScope_48_ = lean_ctor_get(v_toCold_45_, 9);
v___x_49_ = lean_array_uget_borrowed(v_as_38_, v_i_39_);
v___x_50_ = l_Lean_SourceInfo_fromRef(v_ref_46_, v___x_44_);
v___x_51_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_52_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__6, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__6);
v___x_53_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__8));
lean_inc(v_currMacroScope_48_);
lean_inc(v_quotContext_47_);
v___x_54_ = l_Lean_addMacroScope(v_quotContext_47_, v___x_53_, v_currMacroScope_48_);
v___x_55_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__14));
lean_inc_n(v___x_50_, 2);
v___x_56_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_56_, 0, v___x_50_);
lean_ctor_set(v___x_56_, 1, v___x_52_);
lean_ctor_set(v___x_56_, 2, v___x_54_);
lean_ctor_set(v___x_56_, 3, v___x_55_);
v___x_57_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
lean_inc(v___x_49_);
v___x_58_ = l_Lean_Syntax_node2(v___x_50_, v___x_57_, v_b_41_, v___x_49_);
v___x_59_ = l_Lean_Syntax_node2(v___x_50_, v___x_51_, v___x_56_, v___x_58_);
v___x_60_ = ((size_t)1ULL);
v___x_61_ = lean_usize_add(v_i_39_, v___x_60_);
v_i_39_ = v___x_61_;
v_b_41_ = v___x_59_;
goto _start;
}
else
{
lean_object* v___x_63_; 
v___x_63_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_63_, 0, v_b_41_);
return v___x_63_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___boxed(lean_object* v_as_64_, lean_object* v_i_65_, lean_object* v_stop_66_, lean_object* v_b_67_, lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
size_t v_i_boxed_70_; size_t v_stop_boxed_71_; lean_object* v_res_72_; 
v_i_boxed_70_ = lean_unbox_usize(v_i_65_);
lean_dec(v_i_65_);
v_stop_boxed_71_ = lean_unbox_usize(v_stop_66_);
lean_dec(v_stop_66_);
v_res_72_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg(v_as_64_, v_i_boxed_70_, v_stop_boxed_71_, v_b_67_, v___y_68_);
lean_dec_ref(v___y_68_);
lean_dec_ref(v_as_64_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm(lean_object* v_f_73_, lean_object* v_args_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_80_ = lean_unsigned_to_nat(0u);
v___x_81_ = lean_array_get_size(v_args_74_);
v___x_82_ = lean_nat_dec_lt(v___x_80_, v___x_81_);
if (v___x_82_ == 0)
{
lean_object* v___x_83_; 
v___x_83_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_83_, 0, v_f_73_);
return v___x_83_;
}
else
{
uint8_t v___x_84_; 
v___x_84_ = lean_nat_dec_le(v___x_81_, v___x_81_);
if (v___x_84_ == 0)
{
if (v___x_82_ == 0)
{
lean_object* v___x_85_; 
v___x_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_85_, 0, v_f_73_);
return v___x_85_;
}
else
{
size_t v___x_86_; size_t v___x_87_; lean_object* v___x_88_; 
v___x_86_ = ((size_t)0ULL);
v___x_87_ = lean_usize_of_nat(v___x_81_);
v___x_88_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg(v_args_74_, v___x_86_, v___x_87_, v_f_73_, v_a_77_);
return v___x_88_;
}
}
else
{
size_t v___x_89_; size_t v___x_90_; lean_object* v___x_91_; 
v___x_89_ = ((size_t)0ULL);
v___x_90_ = lean_usize_of_nat(v___x_81_);
v___x_91_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg(v_args_74_, v___x_89_, v___x_90_, v_f_73_, v_a_77_);
return v___x_91_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm___boxed(lean_object* v_f_92_, lean_object* v_args_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm(v_f_92_, v_args_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_);
lean_dec(v_a_97_);
lean_dec_ref(v_a_96_);
lean_dec(v_a_95_);
lean_dec_ref(v_a_94_);
lean_dec_ref(v_args_93_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0(lean_object* v_as_100_, size_t v_i_101_, size_t v_stop_102_, lean_object* v_b_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg(v_as_100_, v_i_101_, v_stop_102_, v_b_103_, v___y_106_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___boxed(lean_object* v_as_110_, lean_object* v_i_111_, lean_object* v_stop_112_, lean_object* v_b_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_){
_start:
{
size_t v_i_boxed_119_; size_t v_stop_boxed_120_; lean_object* v_res_121_; 
v_i_boxed_119_ = lean_unbox_usize(v_i_111_);
lean_dec(v_i_111_);
v_stop_boxed_120_ = lean_unbox_usize(v_stop_112_);
lean_dec(v_stop_112_);
v_res_121_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0(v_as_110_, v_i_boxed_119_, v_stop_boxed_120_, v_b_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec_ref(v_as_110_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__2(size_t v_sz_122_, size_t v_i_123_, lean_object* v_bs_124_){
_start:
{
uint8_t v___x_125_; 
v___x_125_ = lean_usize_dec_lt(v_i_123_, v_sz_122_);
if (v___x_125_ == 0)
{
return v_bs_124_;
}
else
{
lean_object* v_v_126_; lean_object* v___x_127_; lean_object* v_bs_x27_128_; size_t v___x_129_; size_t v___x_130_; lean_object* v___x_131_; 
v_v_126_ = lean_array_uget(v_bs_124_, v_i_123_);
v___x_127_ = lean_unsigned_to_nat(0u);
v_bs_x27_128_ = lean_array_uset(v_bs_124_, v_i_123_, v___x_127_);
v___x_129_ = ((size_t)1ULL);
v___x_130_ = lean_usize_add(v_i_123_, v___x_129_);
v___x_131_ = lean_array_uset(v_bs_x27_128_, v_i_123_, v_v_126_);
v_i_123_ = v___x_130_;
v_bs_124_ = v___x_131_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__2___boxed(lean_object* v_sz_133_, lean_object* v_i_134_, lean_object* v_bs_135_){
_start:
{
size_t v_sz_boxed_136_; size_t v_i_boxed_137_; lean_object* v_res_138_; 
v_sz_boxed_136_ = lean_unbox_usize(v_sz_133_);
lean_dec(v_sz_133_);
v_i_boxed_137_ = lean_unbox_usize(v_i_134_);
lean_dec(v_i_134_);
v_res_138_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__2(v_sz_boxed_136_, v_i_boxed_137_, v_bs_135_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__1(size_t v_sz_139_, size_t v_i_140_, lean_object* v_bs_141_){
_start:
{
uint8_t v___x_142_; 
v___x_142_ = lean_usize_dec_lt(v_i_140_, v_sz_139_);
if (v___x_142_ == 0)
{
return v_bs_141_;
}
else
{
lean_object* v_v_143_; lean_object* v___x_144_; lean_object* v_bs_x27_145_; lean_object* v___x_146_; size_t v___x_147_; size_t v___x_148_; lean_object* v___x_149_; 
v_v_143_ = lean_array_uget(v_bs_141_, v_i_140_);
v___x_144_ = lean_unsigned_to_nat(0u);
v_bs_x27_145_ = lean_array_uset(v_bs_141_, v_i_140_, v___x_144_);
v___x_146_ = l_Lean_mkIdent(v_v_143_);
v___x_147_ = ((size_t)1ULL);
v___x_148_ = lean_usize_add(v_i_140_, v___x_147_);
v___x_149_ = lean_array_uset(v_bs_x27_145_, v_i_140_, v___x_146_);
v_i_140_ = v___x_148_;
v_bs_141_ = v___x_149_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__1___boxed(lean_object* v_sz_151_, lean_object* v_i_152_, lean_object* v_bs_153_){
_start:
{
size_t v_sz_boxed_154_; size_t v_i_boxed_155_; lean_object* v_res_156_; 
v_sz_boxed_154_ = lean_unbox_usize(v_sz_151_);
lean_dec(v_sz_151_);
v_i_boxed_155_ = lean_unbox_usize(v_i_152_);
lean_dec(v_i_152_);
v_res_156_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__1(v_sz_boxed_154_, v_i_boxed_155_, v_bs_153_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__0(lean_object* v_msgData_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
lean_object* v___x_163_; lean_object* v_env_164_; lean_object* v___x_165_; lean_object* v_toCold_166_; lean_object* v_mctx_167_; lean_object* v_lctx_168_; lean_object* v_options_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_163_ = lean_st_ref_get(v___y_161_);
v_env_164_ = lean_ctor_get(v___x_163_, 0);
lean_inc_ref(v_env_164_);
lean_dec(v___x_163_);
v___x_165_ = lean_st_ref_get(v___y_159_);
v_toCold_166_ = lean_ctor_get(v___y_160_, 0);
v_mctx_167_ = lean_ctor_get(v___x_165_, 0);
lean_inc_ref(v_mctx_167_);
lean_dec(v___x_165_);
v_lctx_168_ = lean_ctor_get(v___y_158_, 2);
v_options_169_ = lean_ctor_get(v_toCold_166_, 2);
lean_inc_ref(v_options_169_);
lean_inc_ref(v_lctx_168_);
v___x_170_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_170_, 0, v_env_164_);
lean_ctor_set(v___x_170_, 1, v_mctx_167_);
lean_ctor_set(v___x_170_, 2, v_lctx_168_);
lean_ctor_set(v___x_170_, 3, v_options_169_);
v___x_171_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v_msgData_157_);
v___x_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__0___boxed(lean_object* v_msgData_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__0(v_msgData_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
return v_res_179_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = lean_box(1);
v___x_181_ = l_Lean_MessageData_ofFormat(v___x_180_);
return v___x_181_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__2));
v___x_186_ = l_Lean_MessageData_ofFormat(v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3(lean_object* v_x_187_, lean_object* v_x_188_){
_start:
{
if (lean_obj_tag(v_x_188_) == 0)
{
return v_x_187_;
}
else
{
lean_object* v_head_189_; lean_object* v_tail_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_212_; 
v_head_189_ = lean_ctor_get(v_x_188_, 0);
v_tail_190_ = lean_ctor_get(v_x_188_, 1);
v_isSharedCheck_212_ = !lean_is_exclusive(v_x_188_);
if (v_isSharedCheck_212_ == 0)
{
v___x_192_ = v_x_188_;
v_isShared_193_ = v_isSharedCheck_212_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_tail_190_);
lean_inc(v_head_189_);
lean_dec(v_x_188_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_212_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v_before_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_210_; 
v_before_194_ = lean_ctor_get(v_head_189_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v_head_189_);
if (v_isSharedCheck_210_ == 0)
{
lean_object* v_unused_211_; 
v_unused_211_ = lean_ctor_get(v_head_189_, 1);
lean_dec(v_unused_211_);
v___x_196_ = v_head_189_;
v_isShared_197_ = v_isSharedCheck_210_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_before_194_);
lean_dec(v_head_189_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_210_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_198_; lean_object* v___x_200_; 
v___x_198_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_197_ == 0)
{
lean_ctor_set_tag(v___x_196_, 7);
lean_ctor_set(v___x_196_, 1, v___x_198_);
lean_ctor_set(v___x_196_, 0, v_x_187_);
v___x_200_ = v___x_196_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_x_187_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v___x_198_);
v___x_200_ = v_reuseFailAlloc_209_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
lean_object* v___x_201_; lean_object* v___x_203_; 
v___x_201_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__3);
if (v_isShared_193_ == 0)
{
lean_ctor_set_tag(v___x_192_, 7);
lean_ctor_set(v___x_192_, 1, v___x_201_);
lean_ctor_set(v___x_192_, 0, v___x_200_);
v___x_203_ = v___x_192_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_200_);
lean_ctor_set(v_reuseFailAlloc_208_, 1, v___x_201_);
v___x_203_ = v_reuseFailAlloc_208_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_204_ = l_Lean_MessageData_ofSyntax(v_before_194_);
v___x_205_ = l_Lean_indentD(v___x_204_);
v___x_206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_203_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
v_x_187_ = v___x_206_;
v_x_188_ = v_tail_190_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__2(lean_object* v_opts_213_, lean_object* v_opt_214_){
_start:
{
lean_object* v_name_215_; lean_object* v_defValue_216_; lean_object* v_map_217_; lean_object* v___x_218_; 
v_name_215_ = lean_ctor_get(v_opt_214_, 0);
v_defValue_216_ = lean_ctor_get(v_opt_214_, 1);
v_map_217_ = lean_ctor_get(v_opts_213_, 0);
v___x_218_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_217_, v_name_215_);
if (lean_obj_tag(v___x_218_) == 0)
{
uint8_t v___x_219_; 
v___x_219_ = lean_unbox(v_defValue_216_);
return v___x_219_;
}
else
{
lean_object* v_val_220_; 
v_val_220_ = lean_ctor_get(v___x_218_, 0);
lean_inc(v_val_220_);
lean_dec_ref_known(v___x_218_, 1);
if (lean_obj_tag(v_val_220_) == 1)
{
uint8_t v_v_221_; 
v_v_221_ = lean_ctor_get_uint8(v_val_220_, 0);
lean_dec_ref_known(v_val_220_, 0);
return v_v_221_;
}
else
{
uint8_t v___x_222_; 
lean_dec(v_val_220_);
v___x_222_ = lean_unbox(v_defValue_216_);
return v___x_222_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__2___boxed(lean_object* v_opts_223_, lean_object* v_opt_224_){
_start:
{
uint8_t v_res_225_; lean_object* v_r_226_; 
v_res_225_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__2(v_opts_223_, v_opt_224_);
lean_dec_ref(v_opt_224_);
lean_dec_ref(v_opts_223_);
v_r_226_ = lean_box(v_res_225_);
return v_r_226_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg___closed__1));
v___x_231_ = l_Lean_MessageData_ofFormat(v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg(lean_object* v_msgData_232_, lean_object* v_macroStack_233_, lean_object* v___y_234_){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_236_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_234_);
v___x_237_ = l_Lean_Elab_pp_macroStack;
v___x_238_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__2(v___x_236_, v___x_237_);
lean_dec_ref(v___x_236_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; 
lean_dec(v_macroStack_233_);
v___x_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_239_, 0, v_msgData_232_);
return v___x_239_;
}
else
{
if (lean_obj_tag(v_macroStack_233_) == 0)
{
lean_object* v___x_240_; 
v___x_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_240_, 0, v_msgData_232_);
return v___x_240_;
}
else
{
lean_object* v_head_241_; lean_object* v_after_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_257_; 
v_head_241_ = lean_ctor_get(v_macroStack_233_, 0);
lean_inc(v_head_241_);
v_after_242_ = lean_ctor_get(v_head_241_, 1);
v_isSharedCheck_257_ = !lean_is_exclusive(v_head_241_);
if (v_isSharedCheck_257_ == 0)
{
lean_object* v_unused_258_; 
v_unused_258_ = lean_ctor_get(v_head_241_, 0);
lean_dec(v_unused_258_);
v___x_244_ = v_head_241_;
v_isShared_245_ = v_isSharedCheck_257_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_after_242_);
lean_dec(v_head_241_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_257_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_246_; lean_object* v___x_248_; 
v___x_246_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_245_ == 0)
{
lean_ctor_set_tag(v___x_244_, 7);
lean_ctor_set(v___x_244_, 1, v___x_246_);
lean_ctor_set(v___x_244_, 0, v_msgData_232_);
v___x_248_ = v___x_244_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_msgData_232_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v___x_246_);
v___x_248_ = v_reuseFailAlloc_256_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v_msgData_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_249_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg___closed__2);
v___x_250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_248_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
v___x_251_ = l_Lean_MessageData_ofSyntax(v_after_242_);
v___x_252_ = l_Lean_indentD(v___x_251_);
v_msgData_253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_253_, 0, v___x_250_);
lean_ctor_set(v_msgData_253_, 1, v___x_252_);
v___x_254_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3(v_msgData_253_, v_macroStack_233_);
v___x_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
return v___x_255_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_259_, lean_object* v_macroStack_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg(v_msgData_259_, v_macroStack_260_, v___y_261_);
lean_dec_ref(v___y_261_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(lean_object* v_msg_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v_ref_272_; lean_object* v_macroStack_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v_a_276_; lean_object* v___x_277_; lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_286_; 
v_ref_272_ = lean_ctor_get(v___y_269_, 2);
v_macroStack_273_ = lean_ctor_get(v___y_265_, 1);
v___x_274_ = l_Lean_Elab_getBetterRef(v_ref_272_, v_macroStack_273_);
v___x_275_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__0(v_msg_264_, v___y_267_, v___y_268_, v___y_269_, v___y_270_);
v_a_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_276_);
lean_dec_ref(v___x_275_);
lean_inc(v_macroStack_273_);
v___x_277_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg(v_a_276_, v_macroStack_273_, v___y_269_);
v_a_278_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_286_ == 0)
{
v___x_280_ = v___x_277_;
v_isShared_281_ = v_isSharedCheck_286_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_277_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_286_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_282_; lean_object* v___x_284_; 
v___x_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_274_);
lean_ctor_set(v___x_282_, 1, v_a_278_);
if (v_isShared_281_ == 0)
{
lean_ctor_set_tag(v___x_280_, 1);
lean_ctor_set(v___x_280_, 0, v___x_282_);
v___x_284_ = v___x_280_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_282_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg___boxed(lean_object* v_msg_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v_msg_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
return v_res_295_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__1(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__0));
v___x_298_ = l_Lean_stringToMessageData(v___x_297_);
return v___x_298_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8(void){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l_Array_mkArray0___redArg();
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType(lean_object* v_indVal_316_, lean_object* v_t_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_){
_start:
{
lean_object* v_toConstantVal_325_; lean_object* v_levelParams_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_374_; 
v_toConstantVal_325_ = lean_ctor_get(v_indVal_316_, 0);
lean_inc_ref(v_toConstantVal_325_);
lean_dec_ref(v_indVal_316_);
v_levelParams_326_ = lean_ctor_get(v_toConstantVal_325_, 1);
v_isSharedCheck_374_ = !lean_is_exclusive(v_toConstantVal_325_);
if (v_isSharedCheck_374_ == 0)
{
lean_object* v_unused_375_; lean_object* v_unused_376_; 
v_unused_375_ = lean_ctor_get(v_toConstantVal_325_, 2);
lean_dec(v_unused_375_);
v_unused_376_ = lean_ctor_get(v_toConstantVal_325_, 0);
lean_dec(v_unused_376_);
v___x_328_ = v_toConstantVal_325_;
v_isShared_329_ = v_isSharedCheck_374_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_levelParams_326_);
lean_dec(v_toConstantVal_325_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_374_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_330_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
lean_inc(v_t_317_);
v___x_331_ = l_Lean_Syntax_isOfKind(v_t_317_, v___x_330_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; lean_object* v___x_333_; 
lean_del_object(v___x_328_);
lean_dec(v_levelParams_326_);
lean_dec(v_t_317_);
v___x_332_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__1, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__1_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__1);
v___x_333_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v___x_332_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
return v___x_333_;
}
else
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; 
v___x_334_ = lean_unsigned_to_nat(0u);
v___x_335_ = l_Lean_Syntax_getArg(v_t_317_, v___x_334_);
v___x_336_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__3));
lean_inc(v___x_335_);
v___x_337_ = l_Lean_Syntax_isOfKind(v___x_335_, v___x_336_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; lean_object* v___x_339_; 
lean_dec(v___x_335_);
lean_del_object(v___x_328_);
lean_dec(v_levelParams_326_);
lean_dec(v_t_317_);
v___x_338_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__1, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__1_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__1);
v___x_339_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v___x_338_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
return v___x_339_;
}
else
{
lean_object* v_ref_340_; lean_object* v___x_341_; size_t v_sz_342_; size_t v___x_343_; lean_object* v_levels_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v_args_348_; uint8_t v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; size_t v_sz_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_364_; 
v_ref_340_ = lean_ctor_get(v_a_322_, 2);
v___x_341_ = lean_array_mk(v_levelParams_326_);
v_sz_342_ = lean_array_size(v___x_341_);
v___x_343_ = ((size_t)0ULL);
v_levels_344_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__1(v_sz_342_, v___x_343_, v___x_341_);
v___x_345_ = lean_unsigned_to_nat(1u);
v___x_346_ = l_Lean_Syntax_getArg(v___x_335_, v___x_345_);
lean_dec(v___x_335_);
v___x_347_ = l_Lean_Syntax_getArg(v_t_317_, v___x_345_);
lean_dec(v_t_317_);
v_args_348_ = l_Lean_Syntax_getArgs(v___x_347_);
lean_dec(v___x_347_);
v___x_349_ = 0;
v___x_350_ = l_Lean_SourceInfo_fromRef(v_ref_340_, v___x_349_);
v___x_351_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__4));
lean_inc_n(v___x_350_, 3);
v___x_352_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_350_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
v___x_353_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__6));
v___x_354_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__7));
v___x_355_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_350_);
lean_ctor_set(v___x_355_, 1, v___x_354_);
v___x_356_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_357_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_358_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__9));
v_sz_359_ = lean_array_size(v_levels_344_);
v___x_360_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__2(v_sz_359_, v___x_343_, v_levels_344_);
v___x_361_ = l_Lean_Syntax_SepArray_ofElems(v___x_358_, v___x_360_);
lean_dec_ref(v___x_360_);
v___x_362_ = l_Array_append___redArg(v___x_357_, v___x_361_);
lean_dec_ref(v___x_361_);
if (v_isShared_329_ == 0)
{
lean_ctor_set_tag(v___x_328_, 1);
lean_ctor_set(v___x_328_, 2, v___x_362_);
lean_ctor_set(v___x_328_, 1, v___x_356_);
lean_ctor_set(v___x_328_, 0, v___x_350_);
v___x_364_ = v___x_328_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_350_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v___x_356_);
lean_ctor_set(v_reuseFailAlloc_373_, 2, v___x_362_);
v___x_364_ = v_reuseFailAlloc_373_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_365_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__10));
lean_inc_n(v___x_350_, 4);
v___x_366_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_350_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
v___x_367_ = l_Lean_Syntax_node4(v___x_350_, v___x_353_, v___x_346_, v___x_355_, v___x_364_, v___x_366_);
v___x_368_ = l_Lean_Syntax_node2(v___x_350_, v___x_336_, v___x_352_, v___x_367_);
v___x_369_ = l_Array_append___redArg(v___x_357_, v_args_348_);
lean_dec_ref(v_args_348_);
v___x_370_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_370_, 0, v___x_350_);
lean_ctor_set(v___x_370_, 1, v___x_356_);
lean_ctor_set(v___x_370_, 2, v___x_369_);
v___x_371_ = l_Lean_Syntax_node2(v___x_350_, v___x_330_, v___x_368_, v___x_370_);
v___x_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
return v___x_372_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___boxed(lean_object* v_indVal_377_, lean_object* v_t_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType(v_indVal_377_, v_t_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_);
lean_dec(v_a_384_);
lean_dec_ref(v_a_383_);
lean_dec(v_a_382_);
lean_dec_ref(v_a_381_);
lean_dec(v_a_380_);
lean_dec_ref(v_a_379_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0(lean_object* v_00_u03b1_387_, lean_object* v_msg_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v_msg_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___boxed(lean_object* v_00_u03b1_397_, lean_object* v_msg_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0(v_00_u03b1_397_, v_msg_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1(lean_object* v_msgData_407_, lean_object* v_macroStack_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg(v_msgData_407_, v_macroStack_408_, v___y_413_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___boxed(lean_object* v_msgData_417_, lean_object* v_macroStack_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1(v_msgData_417_, v_macroStack_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg___lam__0(lean_object* v_k_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v_b_430_, lean_object* v_c_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v___x_437_; 
lean_inc(v___y_435_);
lean_inc_ref(v___y_434_);
lean_inc(v___y_433_);
lean_inc_ref(v___y_432_);
lean_inc(v___y_429_);
lean_inc_ref(v___y_428_);
v___x_437_ = lean_apply_9(v_k_427_, v_b_430_, v_c_431_, v___y_428_, v___y_429_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, lean_box(0));
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg___lam__0___boxed(lean_object* v_k_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v_b_441_, lean_object* v_c_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg___lam__0(v_k_438_, v___y_439_, v___y_440_, v_b_441_, v_c_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec(v___y_444_);
lean_dec_ref(v___y_443_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg(lean_object* v_type_449_, lean_object* v_k_450_, uint8_t v_cleanupAnnotations_451_, uint8_t v_whnfType_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
lean_object* v___f_460_; lean_object* v___x_461_; 
lean_inc(v___y_454_);
lean_inc_ref(v___y_453_);
v___f_460_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_460_, 0, v_k_450_);
lean_closure_set(v___f_460_, 1, v___y_453_);
lean_closure_set(v___f_460_, 2, v___y_454_);
v___x_461_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_449_, v___f_460_, v_cleanupAnnotations_451_, v_whnfType_452_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
if (lean_obj_tag(v___x_461_) == 0)
{
return v___x_461_;
}
else
{
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_469_; 
v_a_462_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_469_ == 0)
{
v___x_464_ = v___x_461_;
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___x_461_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_a_462_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg___boxed(lean_object* v_type_470_, lean_object* v_k_471_, lean_object* v_cleanupAnnotations_472_, lean_object* v_whnfType_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_481_; uint8_t v_whnfType_boxed_482_; lean_object* v_res_483_; 
v_cleanupAnnotations_boxed_481_ = lean_unbox(v_cleanupAnnotations_472_);
v_whnfType_boxed_482_ = lean_unbox(v_whnfType_473_);
v_res_483_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg(v_type_470_, v_k_471_, v_cleanupAnnotations_boxed_481_, v_whnfType_boxed_482_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2(lean_object* v_00_u03b1_484_, lean_object* v_type_485_, lean_object* v_k_486_, uint8_t v_cleanupAnnotations_487_, uint8_t v_whnfType_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg(v_type_485_, v_k_486_, v_cleanupAnnotations_487_, v_whnfType_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___boxed(lean_object* v_00_u03b1_497_, lean_object* v_type_498_, lean_object* v_k_499_, lean_object* v_cleanupAnnotations_500_, lean_object* v_whnfType_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_509_; uint8_t v_whnfType_boxed_510_; lean_object* v_res_511_; 
v_cleanupAnnotations_boxed_509_ = lean_unbox(v_cleanupAnnotations_500_);
v_whnfType_boxed_510_ = lean_unbox(v_whnfType_501_);
v_res_511_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2(v_00_u03b1_497_, v_type_498_, v_k_499_, v_cleanupAnnotations_boxed_509_, v_whnfType_boxed_510_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
return v_res_511_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__0));
v___x_514_ = l_String_toRawSubstring_x27(v___x_513_);
return v___x_514_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__7));
v___x_530_ = l_String_toRawSubstring_x27(v___x_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg(lean_object* v_as_543_, size_t v_sz_544_, size_t v_i_545_, lean_object* v_b_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
lean_object* v_a_553_; uint8_t v___x_557_; 
v___x_557_ = lean_usize_dec_lt(v_i_545_, v_sz_544_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; 
v___x_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_558_, 0, v_b_546_);
return v___x_558_;
}
else
{
lean_object* v_snd_559_; lean_object* v_fst_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_636_; 
v_snd_559_ = lean_ctor_get(v_b_546_, 1);
v_fst_560_ = lean_ctor_get(v_b_546_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v_b_546_);
if (v_isSharedCheck_636_ == 0)
{
v___x_562_ = v_b_546_;
v_isShared_563_ = v_isSharedCheck_636_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_snd_559_);
lean_inc(v_fst_560_);
lean_dec(v_b_546_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_636_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v_array_564_; lean_object* v_start_565_; lean_object* v_stop_566_; uint8_t v___x_567_; 
v_array_564_ = lean_ctor_get(v_snd_559_, 0);
v_start_565_ = lean_ctor_get(v_snd_559_, 1);
v_stop_566_ = lean_ctor_get(v_snd_559_, 2);
v___x_567_ = lean_nat_dec_lt(v_start_565_, v_stop_566_);
if (v___x_567_ == 0)
{
lean_object* v___x_569_; 
if (v_isShared_563_ == 0)
{
v___x_569_ = v___x_562_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_fst_560_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_snd_559_);
v___x_569_ = v_reuseFailAlloc_571_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
lean_object* v___x_570_; 
v___x_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
return v___x_570_;
}
}
else
{
lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_632_; 
lean_inc(v_stop_566_);
lean_inc(v_start_565_);
lean_inc_ref(v_array_564_);
v_isSharedCheck_632_ = !lean_is_exclusive(v_snd_559_);
if (v_isSharedCheck_632_ == 0)
{
lean_object* v_unused_633_; lean_object* v_unused_634_; lean_object* v_unused_635_; 
v_unused_633_ = lean_ctor_get(v_snd_559_, 2);
lean_dec(v_unused_633_);
v_unused_634_ = lean_ctor_get(v_snd_559_, 1);
lean_dec(v_unused_634_);
v_unused_635_ = lean_ctor_get(v_snd_559_, 0);
lean_dec(v_unused_635_);
v___x_573_ = v_snd_559_;
v_isShared_574_ = v_isSharedCheck_632_;
goto v_resetjp_572_;
}
else
{
lean_dec(v_snd_559_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_632_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v_a_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_580_; 
v_a_575_ = lean_array_uget_borrowed(v_as_543_, v_i_545_);
v___x_576_ = lean_array_fget(v_array_564_, v_start_565_);
v___x_577_ = lean_unsigned_to_nat(1u);
v___x_578_ = lean_nat_add(v_start_565_, v___x_577_);
lean_dec(v_start_565_);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 1, v___x_578_);
v___x_580_ = v___x_573_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_array_564_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v___x_578_);
lean_ctor_set(v_reuseFailAlloc_631_, 2, v_stop_566_);
v___x_580_ = v_reuseFailAlloc_631_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
lean_object* v___x_581_; lean_object* v___x_582_; 
lean_inc(v_a_575_);
v___x_581_ = l_Lean_mkIdent(v_a_575_);
v___x_582_ = l_Lean_Meta_isType(v___x_576_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; uint8_t v___x_584_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_a_583_);
lean_dec_ref_known(v___x_582_, 1);
v___x_584_ = lean_unbox(v_a_583_);
if (v___x_584_ == 0)
{
lean_object* v_toCold_585_; lean_object* v_ref_586_; lean_object* v_quotContext_587_; lean_object* v_currMacroScope_588_; uint8_t v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_602_; 
v_toCold_585_ = lean_ctor_get(v___y_549_, 0);
v_ref_586_ = lean_ctor_get(v___y_549_, 2);
v_quotContext_587_ = lean_ctor_get(v_toCold_585_, 8);
v_currMacroScope_588_ = lean_ctor_get(v_toCold_585_, 9);
v___x_589_ = lean_unbox(v_a_583_);
lean_dec(v_a_583_);
v___x_590_ = l_Lean_SourceInfo_fromRef(v_ref_586_, v___x_589_);
v___x_591_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_592_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1);
v___x_593_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__2));
lean_inc(v_currMacroScope_588_);
lean_inc(v_quotContext_587_);
v___x_594_ = l_Lean_addMacroScope(v_quotContext_587_, v___x_593_, v_currMacroScope_588_);
v___x_595_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__6));
lean_inc_n(v___x_590_, 2);
v___x_596_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_596_, 0, v___x_590_);
lean_ctor_set(v___x_596_, 1, v___x_592_);
lean_ctor_set(v___x_596_, 2, v___x_594_);
lean_ctor_set(v___x_596_, 3, v___x_595_);
v___x_597_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_598_ = l_Lean_Syntax_node1(v___x_590_, v___x_597_, v___x_581_);
v___x_599_ = l_Lean_Syntax_node2(v___x_590_, v___x_591_, v___x_596_, v___x_598_);
v___x_600_ = lean_array_push(v_fst_560_, v___x_599_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 1, v___x_580_);
lean_ctor_set(v___x_562_, 0, v___x_600_);
v___x_602_ = v___x_562_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_600_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v___x_580_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
v_a_553_ = v___x_602_;
goto v___jp_552_;
}
}
else
{
lean_object* v_toCold_604_; lean_object* v_ref_605_; lean_object* v_quotContext_606_; lean_object* v_currMacroScope_607_; uint8_t v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_621_; 
lean_dec(v_a_583_);
v_toCold_604_ = lean_ctor_get(v___y_549_, 0);
v_ref_605_ = lean_ctor_get(v___y_549_, 2);
v_quotContext_606_ = lean_ctor_get(v_toCold_604_, 8);
v_currMacroScope_607_ = lean_ctor_get(v_toCold_604_, 9);
v___x_608_ = 0;
v___x_609_ = l_Lean_SourceInfo_fromRef(v_ref_605_, v___x_608_);
v___x_610_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_611_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8);
v___x_612_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__9));
lean_inc(v_currMacroScope_607_);
lean_inc(v_quotContext_606_);
v___x_613_ = l_Lean_addMacroScope(v_quotContext_606_, v___x_612_, v_currMacroScope_607_);
v___x_614_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__12));
lean_inc_n(v___x_609_, 2);
v___x_615_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_615_, 0, v___x_609_);
lean_ctor_set(v___x_615_, 1, v___x_611_);
lean_ctor_set(v___x_615_, 2, v___x_613_);
lean_ctor_set(v___x_615_, 3, v___x_614_);
v___x_616_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_617_ = l_Lean_Syntax_node1(v___x_609_, v___x_616_, v___x_581_);
v___x_618_ = l_Lean_Syntax_node2(v___x_609_, v___x_610_, v___x_615_, v___x_617_);
v___x_619_ = lean_array_push(v_fst_560_, v___x_618_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 1, v___x_580_);
lean_ctor_set(v___x_562_, 0, v___x_619_);
v___x_621_ = v___x_562_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_619_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v___x_580_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
v_a_553_ = v___x_621_;
goto v___jp_552_;
}
}
}
else
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
lean_dec(v___x_581_);
lean_dec_ref(v___x_580_);
lean_del_object(v___x_562_);
lean_dec(v_fst_560_);
v_a_623_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_582_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_582_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
}
}
}
}
v___jp_552_:
{
size_t v___x_554_; size_t v___x_555_; 
v___x_554_ = ((size_t)1ULL);
v___x_555_ = lean_usize_add(v_i_545_, v___x_554_);
v_i_545_ = v___x_555_;
v_b_546_ = v_a_553_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___boxed(lean_object* v_as_637_, lean_object* v_sz_638_, lean_object* v_i_639_, lean_object* v_b_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
size_t v_sz_boxed_646_; size_t v_i_boxed_647_; lean_object* v_res_648_; 
v_sz_boxed_646_ = lean_unbox_usize(v_sz_638_);
lean_dec(v_sz_638_);
v_i_boxed_647_ = lean_unbox_usize(v_i_639_);
lean_dec(v_i_639_);
v_res_648_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg(v_as_637_, v_sz_boxed_646_, v_i_boxed_647_, v_b_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec_ref(v_as_637_);
return v_res_648_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__1));
v___x_653_ = l_String_toRawSubstring_x27(v___x_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0(lean_object* v_argNames_689_, size_t v___x_690_, lean_object* v_a_691_, lean_object* v_name_692_, lean_object* v_xs_693_, lean_object* v_x_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; size_t v_sz_707_; lean_object* v___x_708_; 
v___x_702_ = lean_unsigned_to_nat(0u);
v___x_703_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__0));
v___x_704_ = lean_array_get_size(v_xs_693_);
v___x_705_ = l_Array_toSubarray___redArg(v_xs_693_, v___x_702_, v___x_704_);
v___x_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_703_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
v_sz_707_ = lean_array_size(v_argNames_689_);
v___x_708_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg(v_argNames_689_, v_sz_707_, v___x_690_, v___x_706_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v_toCold_710_; lean_object* v_fst_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_760_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_a_709_);
lean_dec_ref_known(v___x_708_, 1);
v_toCold_710_ = lean_ctor_get(v___y_699_, 0);
v_fst_711_ = lean_ctor_get(v_a_709_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v_a_709_);
if (v_isSharedCheck_760_ == 0)
{
lean_object* v_unused_761_; 
v_unused_761_ = lean_ctor_get(v_a_709_, 1);
lean_dec(v_unused_761_);
v___x_713_ = v_a_709_;
v_isShared_714_ = v_isSharedCheck_760_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_fst_711_);
lean_dec(v_a_709_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_760_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v_ref_715_; lean_object* v_quotContext_716_; lean_object* v_currMacroScope_717_; uint8_t v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___y_729_; lean_object* v___x_746_; 
v_ref_715_ = lean_ctor_get(v___y_699_, 2);
v_quotContext_716_ = lean_ctor_get(v_toCold_710_, 8);
v_currMacroScope_717_ = lean_ctor_get(v_toCold_710_, 9);
v___x_718_ = 0;
v___x_719_ = l_Lean_SourceInfo_fromRef(v_ref_715_, v___x_718_);
v___x_720_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_721_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__2, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__2_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__2);
v___x_722_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__4));
lean_inc(v_currMacroScope_717_);
lean_inc(v_quotContext_716_);
v___x_723_ = l_Lean_addMacroScope(v_quotContext_716_, v___x_722_, v_currMacroScope_717_);
v___x_724_ = lean_box(0);
v___x_725_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__10));
lean_inc(v___x_719_);
v___x_726_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_726_, 0, v___x_719_);
lean_ctor_set(v___x_726_, 1, v___x_721_);
lean_ctor_set(v___x_726_, 2, v___x_723_);
lean_ctor_set(v___x_726_, 3, v___x_725_);
v___x_727_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
lean_inc(v_name_692_);
v___x_746_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_724_, v_name_692_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v___x_747_; 
v___x_747_ = l_Lean_quoteNameMk(v_name_692_);
v___y_729_ = v___x_747_;
goto v___jp_728_;
}
else
{
lean_object* v_val_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
lean_dec(v_name_692_);
v_val_748_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_val_748_);
lean_dec_ref_known(v___x_746_, 1);
v___x_749_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__16));
v___x_750_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__17));
v___x_751_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__18));
v___x_752_ = lean_string_intercalate(v___x_751_, v_val_748_);
v___x_753_ = lean_string_append(v___x_750_, v___x_752_);
lean_dec_ref(v___x_752_);
v___x_754_ = lean_box(2);
v___x_755_ = l_Lean_Syntax_mkNameLit(v___x_753_, v___x_754_);
v___x_756_ = lean_unsigned_to_nat(1u);
v___x_757_ = lean_mk_empty_array_with_capacity(v___x_756_);
v___x_758_ = lean_array_push(v___x_757_, v___x_755_);
v___x_759_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_759_, 0, v___x_754_);
lean_ctor_set(v___x_759_, 1, v___x_749_);
lean_ctor_set(v___x_759_, 2, v___x_758_);
v___y_729_ = v___x_759_;
goto v___jp_728_;
}
v___jp_728_:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_733_; 
v___x_730_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__12));
v___x_731_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__13));
lean_inc(v___x_719_);
if (v_isShared_714_ == 0)
{
lean_ctor_set_tag(v___x_713_, 2);
lean_ctor_set(v___x_713_, 1, v___x_731_);
lean_ctor_set(v___x_713_, 0, v___x_719_);
v___x_733_ = v___x_713_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_719_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v___x_731_);
v___x_733_ = v_reuseFailAlloc_745_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_734_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_735_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__9));
v___x_736_ = l_Lean_Syntax_SepArray_ofElems(v___x_735_, v_a_691_);
v___x_737_ = l_Array_append___redArg(v___x_734_, v___x_736_);
lean_dec_ref(v___x_736_);
lean_inc_n(v___x_719_, 4);
v___x_738_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_738_, 0, v___x_719_);
lean_ctor_set(v___x_738_, 1, v___x_727_);
lean_ctor_set(v___x_738_, 2, v___x_737_);
v___x_739_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__14));
v___x_740_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_719_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
v___x_741_ = l_Lean_Syntax_node3(v___x_719_, v___x_730_, v___x_733_, v___x_738_, v___x_740_);
v___x_742_ = l_Lean_Syntax_node2(v___x_719_, v___x_727_, v___y_729_, v___x_741_);
v___x_743_ = l_Lean_Syntax_node2(v___x_719_, v___x_720_, v___x_726_, v___x_742_);
v___x_744_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm(v___x_743_, v_fst_711_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
lean_dec(v_fst_711_);
return v___x_744_;
}
}
}
}
else
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
lean_dec(v_name_692_);
v_a_762_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_708_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_708_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_762_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___boxed(lean_object* v_argNames_770_, lean_object* v___x_771_, lean_object* v_a_772_, lean_object* v_name_773_, lean_object* v_xs_774_, lean_object* v_x_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
size_t v___x_11423__boxed_783_; lean_object* v_res_784_; 
v___x_11423__boxed_783_ = lean_unbox_usize(v___x_771_);
lean_dec(v___x_771_);
v_res_784_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0(v_argNames_770_, v___x_11423__boxed_783_, v_a_772_, v_name_773_, v_xs_774_, v_x_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec_ref(v_x_775_);
lean_dec_ref(v_a_772_);
lean_dec_ref(v_argNames_770_);
return v_res_784_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__0));
v___x_787_ = l_String_toRawSubstring_x27(v___x_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg(size_t v_sz_803_, size_t v_i_804_, lean_object* v_bs_805_, lean_object* v___y_806_){
_start:
{
uint8_t v___x_808_; 
v___x_808_ = lean_usize_dec_lt(v_i_804_, v_sz_803_);
if (v___x_808_ == 0)
{
lean_object* v___x_809_; 
v___x_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_809_, 0, v_bs_805_);
return v___x_809_;
}
else
{
lean_object* v_toCold_810_; lean_object* v_ref_811_; lean_object* v_quotContext_812_; lean_object* v_currMacroScope_813_; lean_object* v_v_814_; lean_object* v___x_815_; lean_object* v_bs_x27_816_; uint8_t v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; size_t v___x_833_; size_t v___x_834_; lean_object* v___x_835_; 
v_toCold_810_ = lean_ctor_get(v___y_806_, 0);
v_ref_811_ = lean_ctor_get(v___y_806_, 2);
v_quotContext_812_ = lean_ctor_get(v_toCold_810_, 8);
v_currMacroScope_813_ = lean_ctor_get(v_toCold_810_, 9);
v_v_814_ = lean_array_uget(v_bs_805_, v_i_804_);
v___x_815_ = lean_unsigned_to_nat(0u);
v_bs_x27_816_ = lean_array_uset(v_bs_805_, v_i_804_, v___x_815_);
v___x_817_ = 0;
v___x_818_ = l_Lean_SourceInfo_fromRef(v_ref_811_, v___x_817_);
v___x_819_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__6));
v___x_820_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__1);
v___x_821_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__3));
lean_inc(v_currMacroScope_813_);
lean_inc(v_quotContext_812_);
v___x_822_ = l_Lean_addMacroScope(v_quotContext_812_, v___x_821_, v_currMacroScope_813_);
v___x_823_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__7));
lean_inc_n(v___x_818_, 4);
v___x_824_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_824_, 0, v___x_818_);
lean_ctor_set(v___x_824_, 1, v___x_820_);
lean_ctor_set(v___x_824_, 2, v___x_822_);
lean_ctor_set(v___x_824_, 3, v___x_823_);
v___x_825_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__7));
v___x_826_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_818_);
lean_ctor_set(v___x_826_, 1, v___x_825_);
v___x_827_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_828_ = l_Lean_mkIdent(v_v_814_);
v___x_829_ = l_Lean_Syntax_node1(v___x_818_, v___x_827_, v___x_828_);
v___x_830_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__10));
v___x_831_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_818_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
v___x_832_ = l_Lean_Syntax_node4(v___x_818_, v___x_819_, v___x_824_, v___x_826_, v___x_829_, v___x_831_);
v___x_833_ = ((size_t)1ULL);
v___x_834_ = lean_usize_add(v_i_804_, v___x_833_);
v___x_835_ = lean_array_uset(v_bs_x27_816_, v_i_804_, v___x_832_);
v_i_804_ = v___x_834_;
v_bs_805_ = v___x_835_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___boxed(lean_object* v_sz_837_, lean_object* v_i_838_, lean_object* v_bs_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
size_t v_sz_boxed_842_; size_t v_i_boxed_843_; lean_object* v_res_844_; 
v_sz_boxed_842_ = lean_unbox_usize(v_sz_837_);
lean_dec(v_sz_837_);
v_i_boxed_843_ = lean_unbox_usize(v_i_838_);
lean_dec(v_i_838_);
v_res_844_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg(v_sz_boxed_842_, v_i_boxed_843_, v_bs_839_, v___y_840_);
lean_dec_ref(v___y_840_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr(lean_object* v_indVal_847_, lean_object* v_argNames_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_){
_start:
{
lean_object* v_toConstantVal_856_; lean_object* v_name_857_; lean_object* v_levelParams_858_; lean_object* v_type_859_; lean_object* v___x_860_; size_t v_sz_861_; size_t v___x_862_; lean_object* v___x_863_; 
v_toConstantVal_856_ = lean_ctor_get(v_indVal_847_, 0);
lean_inc_ref(v_toConstantVal_856_);
lean_dec_ref(v_indVal_847_);
v_name_857_ = lean_ctor_get(v_toConstantVal_856_, 0);
lean_inc(v_name_857_);
v_levelParams_858_ = lean_ctor_get(v_toConstantVal_856_, 1);
lean_inc(v_levelParams_858_);
v_type_859_ = lean_ctor_get(v_toConstantVal_856_, 2);
lean_inc_ref(v_type_859_);
lean_dec_ref(v_toConstantVal_856_);
v___x_860_ = lean_array_mk(v_levelParams_858_);
v_sz_861_ = lean_array_size(v___x_860_);
v___x_862_ = ((size_t)0ULL);
v___x_863_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg(v_sz_861_, v___x_862_, v___x_860_, v_a_853_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; lean_object* v___x_865_; lean_object* v___f_866_; uint8_t v___x_867_; lean_object* v___x_868_; 
v_a_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_a_864_);
lean_dec_ref_known(v___x_863_, 1);
v___x_865_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___boxed__const__1));
v___f_866_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___boxed), 13, 4);
lean_closure_set(v___f_866_, 0, v_argNames_848_);
lean_closure_set(v___f_866_, 1, v___x_865_);
lean_closure_set(v___f_866_, 2, v_a_864_);
lean_closure_set(v___f_866_, 3, v_name_857_);
v___x_867_ = 0;
v___x_868_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg(v_type_859_, v___f_866_, v___x_867_, v___x_867_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_);
return v___x_868_;
}
else
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
lean_dec_ref(v_type_859_);
lean_dec(v_name_857_);
lean_dec_ref(v_argNames_848_);
v_a_869_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_863_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_863_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_869_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___boxed(lean_object* v_indVal_877_, lean_object* v_argNames_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr(v_indVal_877_, v_argNames_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_);
lean_dec(v_a_884_);
lean_dec_ref(v_a_883_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
lean_dec(v_a_880_);
lean_dec_ref(v_a_879_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0(size_t v_sz_887_, size_t v_i_888_, lean_object* v_bs_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg(v_sz_887_, v_i_888_, v_bs_889_, v___y_894_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___boxed(lean_object* v_sz_898_, lean_object* v_i_899_, lean_object* v_bs_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
size_t v_sz_boxed_908_; size_t v_i_boxed_909_; lean_object* v_res_910_; 
v_sz_boxed_908_ = lean_unbox_usize(v_sz_898_);
lean_dec(v_sz_898_);
v_i_boxed_909_ = lean_unbox_usize(v_i_899_);
lean_dec(v_i_899_);
v_res_910_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0(v_sz_boxed_908_, v_i_boxed_909_, v_bs_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1(lean_object* v_as_911_, size_t v_sz_912_, size_t v_i_913_, lean_object* v_b_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg(v_as_911_, v_sz_912_, v_i_913_, v_b_914_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___boxed(lean_object* v_as_923_, lean_object* v_sz_924_, lean_object* v_i_925_, lean_object* v_b_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
size_t v_sz_boxed_934_; size_t v_i_boxed_935_; lean_object* v_res_936_; 
v_sz_boxed_934_ = lean_unbox_usize(v_sz_924_);
lean_dec(v_sz_924_);
v_i_boxed_935_ = lean_unbox_usize(v_i_925_);
lean_dec(v_i_925_);
v_res_936_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1(v_as_923_, v_sz_boxed_934_, v_i_boxed_935_, v_b_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec_ref(v_as_923_);
return v_res_936_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__2));
v___x_944_ = l_String_toRawSubstring_x27(v___x_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg(size_t v_sz_947_, size_t v_i_948_, lean_object* v_bs_949_, lean_object* v___y_950_){
_start:
{
uint8_t v___x_952_; 
v___x_952_ = lean_usize_dec_lt(v_i_948_, v_sz_947_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; 
v___x_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_953_, 0, v_bs_949_);
return v___x_953_;
}
else
{
lean_object* v_toCold_954_; lean_object* v_ref_955_; lean_object* v_quotContext_956_; lean_object* v_currMacroScope_957_; lean_object* v_v_958_; lean_object* v___x_959_; lean_object* v_bs_x27_960_; uint8_t v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; size_t v___x_972_; size_t v___x_973_; lean_object* v___x_974_; 
v_toCold_954_ = lean_ctor_get(v___y_950_, 0);
v_ref_955_ = lean_ctor_get(v___y_950_, 2);
v_quotContext_956_ = lean_ctor_get(v_toCold_954_, 8);
v_currMacroScope_957_ = lean_ctor_get(v_toCold_954_, 9);
v_v_958_ = lean_array_uget(v_bs_949_, v_i_948_);
v___x_959_ = lean_unsigned_to_nat(0u);
v_bs_x27_960_ = lean_array_uset(v_bs_949_, v_i_948_, v___x_959_);
v___x_961_ = 0;
v___x_962_ = l_Lean_SourceInfo_fromRef(v_ref_955_, v___x_961_);
v___x_963_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__1));
v___x_964_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__18));
lean_inc_n(v___x_962_, 2);
v___x_965_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_962_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__2);
v___x_967_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__3));
lean_inc(v_currMacroScope_957_);
lean_inc(v_quotContext_956_);
v___x_968_ = l_Lean_addMacroScope(v_quotContext_956_, v___x_967_, v_currMacroScope_957_);
v___x_969_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__7));
v___x_970_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_970_, 0, v___x_962_);
lean_ctor_set(v___x_970_, 1, v___x_966_);
lean_ctor_set(v___x_970_, 2, v___x_968_);
lean_ctor_set(v___x_970_, 3, v___x_969_);
v___x_971_ = l_Lean_Syntax_node3(v___x_962_, v___x_963_, v_v_958_, v___x_965_, v___x_970_);
v___x_972_ = ((size_t)1ULL);
v___x_973_ = lean_usize_add(v_i_948_, v___x_972_);
v___x_974_ = lean_array_uset(v_bs_x27_960_, v_i_948_, v___x_971_);
v_i_948_ = v___x_973_;
v_bs_949_ = v___x_974_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___boxed(lean_object* v_sz_976_, lean_object* v_i_977_, lean_object* v_bs_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
size_t v_sz_boxed_981_; size_t v_i_boxed_982_; lean_object* v_res_983_; 
v_sz_boxed_981_ = lean_unbox_usize(v_sz_976_);
lean_dec(v_sz_976_);
v_i_boxed_982_ = lean_unbox_usize(v_i_977_);
lean_dec(v_i_977_);
v_res_983_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg(v_sz_boxed_981_, v_i_boxed_982_, v_bs_978_, v___y_979_);
lean_dec_ref(v___y_979_);
return v_res_983_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_instMonadEIO___redArg();
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1(lean_object* v_msg_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v_toApplicative_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1092_; 
v___x_999_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__0);
v___x_1000_ = l_StateRefT_x27_instMonad___redArg(v___x_999_);
v_toApplicative_1001_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1092_ == 0)
{
lean_object* v_unused_1093_; 
v_unused_1093_ = lean_ctor_get(v___x_1000_, 1);
lean_dec(v_unused_1093_);
v___x_1003_ = v___x_1000_;
v_isShared_1004_ = v_isSharedCheck_1092_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_toApplicative_1001_);
lean_dec(v___x_1000_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1092_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v_toFunctor_1005_; lean_object* v_toSeq_1006_; lean_object* v_toSeqLeft_1007_; lean_object* v_toSeqRight_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1090_; 
v_toFunctor_1005_ = lean_ctor_get(v_toApplicative_1001_, 0);
v_toSeq_1006_ = lean_ctor_get(v_toApplicative_1001_, 2);
v_toSeqLeft_1007_ = lean_ctor_get(v_toApplicative_1001_, 3);
v_toSeqRight_1008_ = lean_ctor_get(v_toApplicative_1001_, 4);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_toApplicative_1001_);
if (v_isSharedCheck_1090_ == 0)
{
lean_object* v_unused_1091_; 
v_unused_1091_ = lean_ctor_get(v_toApplicative_1001_, 1);
lean_dec(v_unused_1091_);
v___x_1010_ = v_toApplicative_1001_;
v_isShared_1011_ = v_isSharedCheck_1090_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_toSeqRight_1008_);
lean_inc(v_toSeqLeft_1007_);
lean_inc(v_toSeq_1006_);
lean_inc(v_toFunctor_1005_);
lean_dec(v_toApplicative_1001_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1090_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___f_1012_; lean_object* v___f_1013_; lean_object* v___f_1014_; lean_object* v___f_1015_; lean_object* v___x_1016_; lean_object* v___f_1017_; lean_object* v___f_1018_; lean_object* v___f_1019_; lean_object* v___x_1021_; 
v___f_1012_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__1));
v___f_1013_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1005_);
v___f_1014_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1014_, 0, v_toFunctor_1005_);
v___f_1015_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1015_, 0, v_toFunctor_1005_);
v___x_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___f_1014_);
lean_ctor_set(v___x_1016_, 1, v___f_1015_);
v___f_1017_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1017_, 0, v_toSeqRight_1008_);
v___f_1018_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1018_, 0, v_toSeqLeft_1007_);
v___f_1019_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1019_, 0, v_toSeq_1006_);
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 4, v___f_1017_);
lean_ctor_set(v___x_1010_, 3, v___f_1018_);
lean_ctor_set(v___x_1010_, 2, v___f_1019_);
lean_ctor_set(v___x_1010_, 1, v___f_1012_);
lean_ctor_set(v___x_1010_, 0, v___x_1016_);
v___x_1021_ = v___x_1010_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1016_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v___f_1012_);
lean_ctor_set(v_reuseFailAlloc_1089_, 2, v___f_1019_);
lean_ctor_set(v_reuseFailAlloc_1089_, 3, v___f_1018_);
lean_ctor_set(v_reuseFailAlloc_1089_, 4, v___f_1017_);
v___x_1021_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
lean_object* v___x_1023_; 
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 1, v___f_1013_);
lean_ctor_set(v___x_1003_, 0, v___x_1021_);
v___x_1023_ = v___x_1003_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1021_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v___f_1013_);
v___x_1023_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
lean_object* v___x_1024_; lean_object* v_toApplicative_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1086_; 
v___x_1024_ = l_StateRefT_x27_instMonad___redArg(v___x_1023_);
v_toApplicative_1025_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1086_ == 0)
{
lean_object* v_unused_1087_; 
v_unused_1087_ = lean_ctor_get(v___x_1024_, 1);
lean_dec(v_unused_1087_);
v___x_1027_ = v___x_1024_;
v_isShared_1028_ = v_isSharedCheck_1086_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_toApplicative_1025_);
lean_dec(v___x_1024_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1086_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v_toFunctor_1029_; lean_object* v_toSeq_1030_; lean_object* v_toSeqLeft_1031_; lean_object* v_toSeqRight_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1084_; 
v_toFunctor_1029_ = lean_ctor_get(v_toApplicative_1025_, 0);
v_toSeq_1030_ = lean_ctor_get(v_toApplicative_1025_, 2);
v_toSeqLeft_1031_ = lean_ctor_get(v_toApplicative_1025_, 3);
v_toSeqRight_1032_ = lean_ctor_get(v_toApplicative_1025_, 4);
v_isSharedCheck_1084_ = !lean_is_exclusive(v_toApplicative_1025_);
if (v_isSharedCheck_1084_ == 0)
{
lean_object* v_unused_1085_; 
v_unused_1085_ = lean_ctor_get(v_toApplicative_1025_, 1);
lean_dec(v_unused_1085_);
v___x_1034_ = v_toApplicative_1025_;
v_isShared_1035_ = v_isSharedCheck_1084_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_toSeqRight_1032_);
lean_inc(v_toSeqLeft_1031_);
lean_inc(v_toSeq_1030_);
lean_inc(v_toFunctor_1029_);
lean_dec(v_toApplicative_1025_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1084_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___f_1036_; lean_object* v___f_1037_; lean_object* v___f_1038_; lean_object* v___f_1039_; lean_object* v___x_1040_; lean_object* v___f_1041_; lean_object* v___f_1042_; lean_object* v___f_1043_; lean_object* v___x_1045_; 
v___f_1036_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__3));
v___f_1037_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1029_);
v___f_1038_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1038_, 0, v_toFunctor_1029_);
v___f_1039_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1039_, 0, v_toFunctor_1029_);
v___x_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___f_1038_);
lean_ctor_set(v___x_1040_, 1, v___f_1039_);
v___f_1041_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1041_, 0, v_toSeqRight_1032_);
v___f_1042_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1042_, 0, v_toSeqLeft_1031_);
v___f_1043_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1043_, 0, v_toSeq_1030_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 4, v___f_1041_);
lean_ctor_set(v___x_1034_, 3, v___f_1042_);
lean_ctor_set(v___x_1034_, 2, v___f_1043_);
lean_ctor_set(v___x_1034_, 1, v___f_1036_);
lean_ctor_set(v___x_1034_, 0, v___x_1040_);
v___x_1045_ = v___x_1034_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1040_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v___f_1036_);
lean_ctor_set(v_reuseFailAlloc_1083_, 2, v___f_1043_);
lean_ctor_set(v_reuseFailAlloc_1083_, 3, v___f_1042_);
lean_ctor_set(v_reuseFailAlloc_1083_, 4, v___f_1041_);
v___x_1045_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
lean_object* v___x_1047_; 
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 1, v___f_1037_);
lean_ctor_set(v___x_1027_, 0, v___x_1045_);
v___x_1047_ = v___x_1027_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v___f_1037_);
v___x_1047_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
lean_object* v___x_1048_; lean_object* v_toApplicative_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1080_; 
v___x_1048_ = l_StateRefT_x27_instMonad___redArg(v___x_1047_);
v_toApplicative_1049_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1080_ == 0)
{
lean_object* v_unused_1081_; 
v_unused_1081_ = lean_ctor_get(v___x_1048_, 1);
lean_dec(v_unused_1081_);
v___x_1051_ = v___x_1048_;
v_isShared_1052_ = v_isSharedCheck_1080_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_toApplicative_1049_);
lean_dec(v___x_1048_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1080_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v_toFunctor_1053_; lean_object* v_toSeq_1054_; lean_object* v_toSeqLeft_1055_; lean_object* v_toSeqRight_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1078_; 
v_toFunctor_1053_ = lean_ctor_get(v_toApplicative_1049_, 0);
v_toSeq_1054_ = lean_ctor_get(v_toApplicative_1049_, 2);
v_toSeqLeft_1055_ = lean_ctor_get(v_toApplicative_1049_, 3);
v_toSeqRight_1056_ = lean_ctor_get(v_toApplicative_1049_, 4);
v_isSharedCheck_1078_ = !lean_is_exclusive(v_toApplicative_1049_);
if (v_isSharedCheck_1078_ == 0)
{
lean_object* v_unused_1079_; 
v_unused_1079_ = lean_ctor_get(v_toApplicative_1049_, 1);
lean_dec(v_unused_1079_);
v___x_1058_ = v_toApplicative_1049_;
v_isShared_1059_ = v_isSharedCheck_1078_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_toSeqRight_1056_);
lean_inc(v_toSeqLeft_1055_);
lean_inc(v_toSeq_1054_);
lean_inc(v_toFunctor_1053_);
lean_dec(v_toApplicative_1049_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1078_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___f_1060_; lean_object* v___f_1061_; lean_object* v___f_1062_; lean_object* v___f_1063_; lean_object* v___x_1064_; lean_object* v___f_1065_; lean_object* v___f_1066_; lean_object* v___f_1067_; lean_object* v___x_1069_; 
v___f_1060_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__5));
v___f_1061_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__6));
lean_inc_ref(v_toFunctor_1053_);
v___f_1062_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1062_, 0, v_toFunctor_1053_);
v___f_1063_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1063_, 0, v_toFunctor_1053_);
v___x_1064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___f_1062_);
lean_ctor_set(v___x_1064_, 1, v___f_1063_);
v___f_1065_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1065_, 0, v_toSeqRight_1056_);
v___f_1066_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1066_, 0, v_toSeqLeft_1055_);
v___f_1067_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1067_, 0, v_toSeq_1054_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 4, v___f_1065_);
lean_ctor_set(v___x_1058_, 3, v___f_1066_);
lean_ctor_set(v___x_1058_, 2, v___f_1067_);
lean_ctor_set(v___x_1058_, 1, v___f_1060_);
lean_ctor_set(v___x_1058_, 0, v___x_1064_);
v___x_1069_ = v___x_1058_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1064_);
lean_ctor_set(v_reuseFailAlloc_1077_, 1, v___f_1060_);
lean_ctor_set(v_reuseFailAlloc_1077_, 2, v___f_1067_);
lean_ctor_set(v_reuseFailAlloc_1077_, 3, v___f_1066_);
lean_ctor_set(v_reuseFailAlloc_1077_, 4, v___f_1065_);
v___x_1069_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
lean_object* v___x_1071_; 
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 1, v___f_1061_);
lean_ctor_set(v___x_1051_, 0, v___x_1069_);
v___x_1071_ = v___x_1051_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1069_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v___f_1061_);
v___x_1071_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_27701__overap_1074_; lean_object* v___x_1075_; 
v___x_1072_ = lean_box(0);
v___x_1073_ = l_instInhabitedOfMonad___redArg(v___x_1071_, v___x_1072_);
v___x_27701__overap_1074_ = lean_panic_fn_borrowed(v___x_1073_, v_msg_991_);
lean_dec(v___x_1073_);
lean_inc(v___y_997_);
lean_inc_ref(v___y_996_);
lean_inc(v___y_995_);
lean_inc_ref(v___y_994_);
lean_inc(v___y_993_);
lean_inc_ref(v___y_992_);
v___x_1075_ = lean_apply_7(v___x_27701__overap_1074_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, lean_box(0));
return v___x_1075_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___boxed(lean_object* v_msg_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1(v_msg_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
return v_res_1102_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__17));
v___x_1104_ = l_Lean_stringToMessageData(v___x_1103_);
return v___x_1104_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__2(void){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__1));
v___x_1107_ = l_Lean_stringToMessageData(v___x_1106_);
return v___x_1107_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__6(void){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1111_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__5));
v___x_1112_ = lean_unsigned_to_nat(11u);
v___x_1113_ = lean_unsigned_to_nat(122u);
v___x_1114_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__4));
v___x_1115_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__3));
v___x_1116_ = l_mkPanicMessageWithDecl(v___x_1115_, v___x_1114_, v___x_1113_, v___x_1112_, v___x_1111_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1(lean_object* v_constName_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v___x_1133_; lean_object* v_env_1134_; uint8_t v___x_1135_; lean_object* v___x_1136_; 
v___x_1133_ = lean_st_ref_get(v___y_1123_);
v_env_1134_ = lean_ctor_get(v___x_1133_, 0);
lean_inc_ref(v_env_1134_);
lean_dec(v___x_1133_);
v___x_1135_ = 0;
lean_inc(v_constName_1117_);
v___x_1136_ = l_Lean_Environment_findAsync_x3f(v_env_1134_, v_constName_1117_, v___x_1135_);
if (lean_obj_tag(v___x_1136_) == 1)
{
lean_object* v_val_1137_; uint8_t v_kind_1138_; 
v_val_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc(v_val_1137_);
lean_dec_ref_known(v___x_1136_, 1);
v_kind_1138_ = lean_ctor_get_uint8(v_val_1137_, sizeof(void*)*3);
if (v_kind_1138_ == 6)
{
lean_object* v___x_1139_; 
v___x_1139_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1137_);
if (lean_obj_tag(v___x_1139_) == 6)
{
lean_object* v_val_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
lean_dec(v_constName_1117_);
v_val_1140_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1142_ = v___x_1139_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_val_1140_);
lean_dec(v___x_1139_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
lean_ctor_set_tag(v___x_1142_, 0);
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_val_1140_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
else
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
lean_dec_ref(v___x_1139_);
v___x_1148_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__6, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__6_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__6);
v___x_1149_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1(v___x_1148_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1158_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1158_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1158_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
if (lean_obj_tag(v_a_1150_) == 0)
{
lean_del_object(v___x_1152_);
goto v___jp_1125_;
}
else
{
lean_object* v_val_1154_; lean_object* v___x_1156_; 
lean_dec(v_constName_1117_);
v_val_1154_ = lean_ctor_get(v_a_1150_, 0);
lean_inc(v_val_1154_);
lean_dec_ref_known(v_a_1150_, 1);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v_val_1154_);
v___x_1156_ = v___x_1152_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_val_1154_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
else
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
lean_dec(v_constName_1117_);
v_a_1159_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v___x_1149_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1149_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1159_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
}
else
{
lean_dec(v_val_1137_);
goto v___jp_1125_;
}
}
else
{
lean_dec(v___x_1136_);
goto v___jp_1125_;
}
v___jp_1125_:
{
lean_object* v___x_1126_; uint8_t v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1126_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__0, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__0_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__0);
v___x_1127_ = 0;
v___x_1128_ = l_Lean_MessageData_ofConstName(v_constName_1117_, v___x_1127_);
v___x_1129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1126_);
lean_ctor_set(v___x_1129_, 1, v___x_1128_);
v___x_1130_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__2, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__2_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__2);
v___x_1131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1129_);
lean_ctor_set(v___x_1131_, 1, v___x_1130_);
v___x_1132_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v___x_1131_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
return v___x_1132_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___boxed(lean_object* v_constName_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1(v_constName_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__0(lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v_ref_1183_; uint8_t v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v_ref_1183_ = lean_ctor_get(v___y_1180_, 2);
v___x_1184_ = 0;
v___x_1185_ = l_Lean_SourceInfo_fromRef(v_ref_1183_, v___x_1184_);
v___x_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__0___boxed(lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__0(v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg(lean_object* v_upperBound_1202_, lean_object* v_a_1203_, lean_object* v_b_1204_, lean_object* v___y_1205_){
_start:
{
uint8_t v___x_1207_; 
v___x_1207_ = lean_nat_dec_lt(v_a_1203_, v_upperBound_1202_);
if (v___x_1207_ == 0)
{
lean_object* v___x_1208_; 
lean_dec(v_a_1203_);
v___x_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1208_, 0, v_b_1204_);
return v___x_1208_;
}
else
{
lean_object* v_ref_1209_; uint8_t v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v_ref_1209_ = lean_ctor_get(v___y_1205_, 2);
v___x_1210_ = 0;
v___x_1211_ = l_Lean_SourceInfo_fromRef(v_ref_1209_, v___x_1210_);
v___x_1212_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__1));
v___x_1213_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__2));
lean_inc(v___x_1211_);
v___x_1214_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1211_);
lean_ctor_set(v___x_1214_, 1, v___x_1213_);
v___x_1215_ = l_Lean_Syntax_node1(v___x_1211_, v___x_1212_, v___x_1214_);
v___x_1216_ = lean_array_push(v_b_1204_, v___x_1215_);
v___x_1217_ = lean_unsigned_to_nat(1u);
v___x_1218_ = lean_nat_add(v_a_1203_, v___x_1217_);
lean_dec(v_a_1203_);
v_a_1203_ = v___x_1218_;
v_b_1204_ = v___x_1216_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___boxed(lean_object* v_upperBound_1220_, lean_object* v_a_1221_, lean_object* v_b_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg(v_upperBound_1220_, v_a_1221_, v_b_1222_, v___y_1223_);
lean_dec_ref(v___y_1223_);
lean_dec(v_upperBound_1220_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6___redArg(lean_object* v_upperBound_1226_, lean_object* v_header_1227_, lean_object* v_xs_1228_, lean_object* v_indVal_1229_, lean_object* v_auxFunName_1230_, lean_object* v_levelInsts_1231_, lean_object* v_a_1232_, lean_object* v_b_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
uint8_t v___x_1239_; 
v___x_1239_ = lean_nat_dec_lt(v_a_1232_, v_upperBound_1226_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; 
lean_dec(v_a_1232_);
lean_dec(v_auxFunName_1230_);
lean_dec_ref(v_indVal_1229_);
v___x_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1240_, 0, v_b_1233_);
return v___x_1240_;
}
else
{
lean_object* v_fst_1241_; lean_object* v_snd_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1335_; 
v_fst_1241_ = lean_ctor_get(v_b_1233_, 0);
v_snd_1242_ = lean_ctor_get(v_b_1233_, 1);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_b_1233_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1244_ = v_b_1233_;
v_isShared_1245_ = v_isSharedCheck_1335_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_snd_1242_);
lean_inc(v_fst_1241_);
lean_dec(v_b_1233_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1335_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v_argNames_1246_; lean_object* v_toCold_1247_; lean_object* v_ref_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; uint8_t v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v_a_1261_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v_argNames_1246_ = lean_ctor_get(v_header_1227_, 1);
v_toCold_1247_ = lean_ctor_get(v___y_1236_, 0);
v_ref_1248_ = lean_ctor_get(v___y_1236_, 2);
v___x_1249_ = lean_box(0);
v___x_1250_ = l_Lean_instInhabitedExpr;
v___x_1251_ = lean_array_get_borrowed(v___x_1249_, v_argNames_1246_, v_a_1232_);
lean_inc(v___x_1251_);
v___x_1252_ = l_Lean_mkIdent(v___x_1251_);
v___x_1253_ = 0;
v___x_1254_ = l_Lean_SourceInfo_fromRef(v_ref_1248_, v___x_1253_);
v___x_1255_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__1));
v___x_1256_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__2));
lean_inc_n(v___x_1254_, 2);
v___x_1257_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1254_);
lean_ctor_set(v___x_1257_, 1, v___x_1256_);
v___x_1258_ = l_Lean_Syntax_node1(v___x_1254_, v___x_1255_, v___x_1257_);
v___x_1259_ = lean_array_push(v_fst_1241_, v___x_1258_);
v___x_1269_ = lean_array_get_borrowed(v___x_1250_, v_xs_1228_, v_a_1232_);
lean_inc(v___y_1237_);
lean_inc_ref(v___y_1236_);
lean_inc(v___y_1235_);
lean_inc_ref(v___y_1234_);
lean_inc(v___x_1269_);
v___x_1270_ = lean_infer_type(v___x_1269_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v_toConstantVal_1271_; lean_object* v_a_1272_; lean_object* v_name_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1324_; 
v_toConstantVal_1271_ = lean_ctor_get(v_indVal_1229_, 0);
lean_inc_ref(v_toConstantVal_1271_);
v_a_1272_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_a_1272_);
lean_dec_ref_known(v___x_1270_, 1);
v_name_1273_ = lean_ctor_get(v_toConstantVal_1271_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v_toConstantVal_1271_);
if (v_isSharedCheck_1324_ == 0)
{
lean_object* v_unused_1325_; lean_object* v_unused_1326_; 
v_unused_1325_ = lean_ctor_get(v_toConstantVal_1271_, 2);
lean_dec(v_unused_1325_);
v_unused_1326_ = lean_ctor_get(v_toConstantVal_1271_, 1);
lean_dec(v_unused_1326_);
v___x_1275_ = v_toConstantVal_1271_;
v_isShared_1276_ = v_isSharedCheck_1324_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_name_1273_);
lean_dec(v_toConstantVal_1271_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1324_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
uint8_t v___x_1277_; 
v___x_1277_ = l_Lean_Expr_isAppOf(v_a_1272_, v_name_1273_);
lean_dec(v_name_1273_);
lean_dec(v_a_1272_);
if (v___x_1277_ == 0)
{
lean_object* v___x_1278_; 
lean_del_object(v___x_1275_);
lean_dec(v___x_1254_);
lean_inc(v___x_1269_);
v___x_1278_ = l_Lean_Meta_isType(v___x_1269_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; uint8_t v___x_1280_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1279_);
lean_dec_ref_known(v___x_1278_, 1);
v___x_1280_ = lean_unbox(v_a_1279_);
if (v___x_1280_ == 0)
{
lean_object* v_quotContext_1281_; lean_object* v_currMacroScope_1282_; uint8_t v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v_quotContext_1281_ = lean_ctor_get(v_toCold_1247_, 8);
v_currMacroScope_1282_ = lean_ctor_get(v_toCold_1247_, 9);
v___x_1283_ = lean_unbox(v_a_1279_);
lean_dec(v_a_1279_);
v___x_1284_ = l_Lean_SourceInfo_fromRef(v_ref_1248_, v___x_1283_);
v___x_1285_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1286_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1);
v___x_1287_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__2));
lean_inc(v_currMacroScope_1282_);
lean_inc(v_quotContext_1281_);
v___x_1288_ = l_Lean_addMacroScope(v_quotContext_1281_, v___x_1287_, v_currMacroScope_1282_);
v___x_1289_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__6));
lean_inc_n(v___x_1284_, 2);
v___x_1290_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1284_);
lean_ctor_set(v___x_1290_, 1, v___x_1286_);
lean_ctor_set(v___x_1290_, 2, v___x_1288_);
lean_ctor_set(v___x_1290_, 3, v___x_1289_);
v___x_1291_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1292_ = l_Lean_Syntax_node1(v___x_1284_, v___x_1291_, v___x_1252_);
v___x_1293_ = l_Lean_Syntax_node2(v___x_1284_, v___x_1285_, v___x_1290_, v___x_1292_);
v_a_1261_ = v___x_1293_;
goto v___jp_1260_;
}
else
{
lean_object* v_quotContext_1294_; lean_object* v_currMacroScope_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
lean_dec(v_a_1279_);
v_quotContext_1294_ = lean_ctor_get(v_toCold_1247_, 8);
v_currMacroScope_1295_ = lean_ctor_get(v_toCold_1247_, 9);
v___x_1296_ = l_Lean_SourceInfo_fromRef(v_ref_1248_, v___x_1277_);
v___x_1297_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1298_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8);
v___x_1299_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__9));
lean_inc(v_currMacroScope_1295_);
lean_inc(v_quotContext_1294_);
v___x_1300_ = l_Lean_addMacroScope(v_quotContext_1294_, v___x_1299_, v_currMacroScope_1295_);
v___x_1301_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__12));
lean_inc_n(v___x_1296_, 2);
v___x_1302_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1296_);
lean_ctor_set(v___x_1302_, 1, v___x_1298_);
lean_ctor_set(v___x_1302_, 2, v___x_1300_);
lean_ctor_set(v___x_1302_, 3, v___x_1301_);
v___x_1303_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1304_ = l_Lean_Syntax_node1(v___x_1296_, v___x_1303_, v___x_1252_);
v___x_1305_ = l_Lean_Syntax_node2(v___x_1296_, v___x_1297_, v___x_1302_, v___x_1304_);
v_a_1261_ = v___x_1305_;
goto v___jp_1260_;
}
}
else
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
lean_dec_ref(v___x_1259_);
lean_dec(v___x_1252_);
lean_del_object(v___x_1244_);
lean_dec(v_snd_1242_);
lean_dec(v_a_1232_);
lean_dec(v_auxFunName_1230_);
lean_dec_ref(v_indVal_1229_);
v_a_1306_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v___x_1278_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1278_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1306_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
else
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1321_; 
v___x_1314_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
lean_inc(v_auxFunName_1230_);
v___x_1315_ = l_Lean_mkIdent(v_auxFunName_1230_);
v___x_1316_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1317_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_1318_ = l_Array_append___redArg(v___x_1317_, v_levelInsts_1231_);
v___x_1319_ = lean_array_push(v___x_1318_, v___x_1252_);
lean_inc(v___x_1254_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set_tag(v___x_1275_, 1);
lean_ctor_set(v___x_1275_, 2, v___x_1319_);
lean_ctor_set(v___x_1275_, 1, v___x_1316_);
lean_ctor_set(v___x_1275_, 0, v___x_1254_);
v___x_1321_ = v___x_1275_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1254_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v___x_1316_);
lean_ctor_set(v_reuseFailAlloc_1323_, 2, v___x_1319_);
v___x_1321_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
lean_object* v___x_1322_; 
v___x_1322_ = l_Lean_Syntax_node2(v___x_1254_, v___x_1314_, v___x_1315_, v___x_1321_);
v_a_1261_ = v___x_1322_;
goto v___jp_1260_;
}
}
}
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
lean_dec_ref(v___x_1259_);
lean_dec(v___x_1254_);
lean_dec(v___x_1252_);
lean_del_object(v___x_1244_);
lean_dec(v_snd_1242_);
lean_dec(v_a_1232_);
lean_dec(v_auxFunName_1230_);
lean_dec_ref(v_indVal_1229_);
v_a_1327_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1270_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1270_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
v___jp_1260_:
{
lean_object* v___x_1262_; lean_object* v___x_1264_; 
v___x_1262_ = lean_array_push(v_snd_1242_, v_a_1261_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 1, v___x_1262_);
lean_ctor_set(v___x_1244_, 0, v___x_1259_);
v___x_1264_ = v___x_1244_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1259_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v___x_1262_);
v___x_1264_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1265_ = lean_unsigned_to_nat(1u);
v___x_1266_ = lean_nat_add(v_a_1232_, v___x_1265_);
lean_dec(v_a_1232_);
v_a_1232_ = v___x_1266_;
v_b_1233_ = v___x_1264_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6___redArg___boxed(lean_object* v_upperBound_1336_, lean_object* v_header_1337_, lean_object* v_xs_1338_, lean_object* v_indVal_1339_, lean_object* v_auxFunName_1340_, lean_object* v_levelInsts_1341_, lean_object* v_a_1342_, lean_object* v_b_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6___redArg(v_upperBound_1336_, v_header_1337_, v_xs_1338_, v_indVal_1339_, v_auxFunName_1340_, v_levelInsts_1341_, v_a_1342_, v_b_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec_ref(v_levelInsts_1341_);
lean_dec_ref(v_xs_1338_);
lean_dec_ref(v_header_1337_);
lean_dec(v_upperBound_1336_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4___redArg(lean_object* v_upperBound_1350_, lean_object* v_header_1351_, lean_object* v_xs_1352_, lean_object* v_indVal_1353_, lean_object* v_auxFunName_1354_, lean_object* v_levelInsts_1355_, lean_object* v_a_1356_, lean_object* v_b_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
uint8_t v___x_1365_; 
v___x_1365_ = lean_nat_dec_lt(v_a_1356_, v_upperBound_1350_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1366_; 
lean_dec(v_auxFunName_1354_);
lean_dec_ref(v_indVal_1353_);
v___x_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1366_, 0, v_b_1357_);
return v___x_1366_;
}
else
{
lean_object* v_fst_1367_; lean_object* v_snd_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1461_; 
v_fst_1367_ = lean_ctor_get(v_b_1357_, 0);
v_snd_1368_ = lean_ctor_get(v_b_1357_, 1);
v_isSharedCheck_1461_ = !lean_is_exclusive(v_b_1357_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1370_ = v_b_1357_;
v_isShared_1371_ = v_isSharedCheck_1461_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_snd_1368_);
lean_inc(v_fst_1367_);
lean_dec(v_b_1357_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1461_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v_argNames_1372_; lean_object* v_toCold_1373_; lean_object* v_ref_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; uint8_t v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v_a_1387_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v_argNames_1372_ = lean_ctor_get(v_header_1351_, 1);
v_toCold_1373_ = lean_ctor_get(v___y_1362_, 0);
v_ref_1374_ = lean_ctor_get(v___y_1362_, 2);
v___x_1375_ = lean_box(0);
v___x_1376_ = l_Lean_instInhabitedExpr;
v___x_1377_ = lean_array_get_borrowed(v___x_1375_, v_argNames_1372_, v_a_1356_);
lean_inc(v___x_1377_);
v___x_1378_ = l_Lean_mkIdent(v___x_1377_);
v___x_1379_ = 0;
v___x_1380_ = l_Lean_SourceInfo_fromRef(v_ref_1374_, v___x_1379_);
v___x_1381_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__1));
v___x_1382_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__2));
lean_inc_n(v___x_1380_, 2);
v___x_1383_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1380_);
lean_ctor_set(v___x_1383_, 1, v___x_1382_);
v___x_1384_ = l_Lean_Syntax_node1(v___x_1380_, v___x_1381_, v___x_1383_);
v___x_1385_ = lean_array_push(v_fst_1367_, v___x_1384_);
v___x_1395_ = lean_array_get_borrowed(v___x_1376_, v_xs_1352_, v_a_1356_);
lean_inc(v___y_1363_);
lean_inc_ref(v___y_1362_);
lean_inc(v___y_1361_);
lean_inc_ref(v___y_1360_);
lean_inc(v___x_1395_);
v___x_1396_ = lean_infer_type(v___x_1395_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_toConstantVal_1397_; lean_object* v_a_1398_; lean_object* v_name_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1450_; 
v_toConstantVal_1397_ = lean_ctor_get(v_indVal_1353_, 0);
lean_inc_ref(v_toConstantVal_1397_);
v_a_1398_ = lean_ctor_get(v___x_1396_, 0);
lean_inc(v_a_1398_);
lean_dec_ref_known(v___x_1396_, 1);
v_name_1399_ = lean_ctor_get(v_toConstantVal_1397_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v_toConstantVal_1397_);
if (v_isSharedCheck_1450_ == 0)
{
lean_object* v_unused_1451_; lean_object* v_unused_1452_; 
v_unused_1451_ = lean_ctor_get(v_toConstantVal_1397_, 2);
lean_dec(v_unused_1451_);
v_unused_1452_ = lean_ctor_get(v_toConstantVal_1397_, 1);
lean_dec(v_unused_1452_);
v___x_1401_ = v_toConstantVal_1397_;
v_isShared_1402_ = v_isSharedCheck_1450_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_name_1399_);
lean_dec(v_toConstantVal_1397_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1450_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
uint8_t v___x_1403_; 
v___x_1403_ = l_Lean_Expr_isAppOf(v_a_1398_, v_name_1399_);
lean_dec(v_name_1399_);
lean_dec(v_a_1398_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; 
lean_del_object(v___x_1401_);
lean_dec(v___x_1380_);
lean_inc(v___x_1395_);
v___x_1404_ = l_Lean_Meta_isType(v___x_1395_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; uint8_t v___x_1406_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_a_1405_);
lean_dec_ref_known(v___x_1404_, 1);
v___x_1406_ = lean_unbox(v_a_1405_);
if (v___x_1406_ == 0)
{
lean_object* v_quotContext_1407_; lean_object* v_currMacroScope_1408_; uint8_t v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v_quotContext_1407_ = lean_ctor_get(v_toCold_1373_, 8);
v_currMacroScope_1408_ = lean_ctor_get(v_toCold_1373_, 9);
v___x_1409_ = lean_unbox(v_a_1405_);
lean_dec(v_a_1405_);
v___x_1410_ = l_Lean_SourceInfo_fromRef(v_ref_1374_, v___x_1409_);
v___x_1411_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1412_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1);
v___x_1413_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__2));
lean_inc(v_currMacroScope_1408_);
lean_inc(v_quotContext_1407_);
v___x_1414_ = l_Lean_addMacroScope(v_quotContext_1407_, v___x_1413_, v_currMacroScope_1408_);
v___x_1415_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__6));
lean_inc_n(v___x_1410_, 2);
v___x_1416_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1410_);
lean_ctor_set(v___x_1416_, 1, v___x_1412_);
lean_ctor_set(v___x_1416_, 2, v___x_1414_);
lean_ctor_set(v___x_1416_, 3, v___x_1415_);
v___x_1417_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1418_ = l_Lean_Syntax_node1(v___x_1410_, v___x_1417_, v___x_1378_);
v___x_1419_ = l_Lean_Syntax_node2(v___x_1410_, v___x_1411_, v___x_1416_, v___x_1418_);
v_a_1387_ = v___x_1419_;
goto v___jp_1386_;
}
else
{
lean_object* v_quotContext_1420_; lean_object* v_currMacroScope_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
lean_dec(v_a_1405_);
v_quotContext_1420_ = lean_ctor_get(v_toCold_1373_, 8);
v_currMacroScope_1421_ = lean_ctor_get(v_toCold_1373_, 9);
v___x_1422_ = l_Lean_SourceInfo_fromRef(v_ref_1374_, v___x_1403_);
v___x_1423_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1424_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8);
v___x_1425_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__9));
lean_inc(v_currMacroScope_1421_);
lean_inc(v_quotContext_1420_);
v___x_1426_ = l_Lean_addMacroScope(v_quotContext_1420_, v___x_1425_, v_currMacroScope_1421_);
v___x_1427_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__12));
lean_inc_n(v___x_1422_, 2);
v___x_1428_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1422_);
lean_ctor_set(v___x_1428_, 1, v___x_1424_);
lean_ctor_set(v___x_1428_, 2, v___x_1426_);
lean_ctor_set(v___x_1428_, 3, v___x_1427_);
v___x_1429_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1430_ = l_Lean_Syntax_node1(v___x_1422_, v___x_1429_, v___x_1378_);
v___x_1431_ = l_Lean_Syntax_node2(v___x_1422_, v___x_1423_, v___x_1428_, v___x_1430_);
v_a_1387_ = v___x_1431_;
goto v___jp_1386_;
}
}
else
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1439_; 
lean_dec_ref(v___x_1385_);
lean_dec(v___x_1378_);
lean_del_object(v___x_1370_);
lean_dec(v_snd_1368_);
lean_dec(v_auxFunName_1354_);
lean_dec_ref(v_indVal_1353_);
v_a_1432_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1434_ = v___x_1404_;
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1404_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1437_; 
if (v_isShared_1435_ == 0)
{
v___x_1437_ = v___x_1434_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_a_1432_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
else
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1447_; 
v___x_1440_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
lean_inc(v_auxFunName_1354_);
v___x_1441_ = l_Lean_mkIdent(v_auxFunName_1354_);
v___x_1442_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1443_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_1444_ = l_Array_append___redArg(v___x_1443_, v_levelInsts_1355_);
v___x_1445_ = lean_array_push(v___x_1444_, v___x_1378_);
lean_inc(v___x_1380_);
if (v_isShared_1402_ == 0)
{
lean_ctor_set_tag(v___x_1401_, 1);
lean_ctor_set(v___x_1401_, 2, v___x_1445_);
lean_ctor_set(v___x_1401_, 1, v___x_1442_);
lean_ctor_set(v___x_1401_, 0, v___x_1380_);
v___x_1447_ = v___x_1401_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v___x_1380_);
lean_ctor_set(v_reuseFailAlloc_1449_, 1, v___x_1442_);
lean_ctor_set(v_reuseFailAlloc_1449_, 2, v___x_1445_);
v___x_1447_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
lean_object* v___x_1448_; 
v___x_1448_ = l_Lean_Syntax_node2(v___x_1380_, v___x_1440_, v___x_1441_, v___x_1447_);
v_a_1387_ = v___x_1448_;
goto v___jp_1386_;
}
}
}
}
else
{
lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1460_; 
lean_dec_ref(v___x_1385_);
lean_dec(v___x_1380_);
lean_dec(v___x_1378_);
lean_del_object(v___x_1370_);
lean_dec(v_snd_1368_);
lean_dec(v_auxFunName_1354_);
lean_dec_ref(v_indVal_1353_);
v_a_1453_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1455_ = v___x_1396_;
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1396_);
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
v___jp_1386_:
{
lean_object* v___x_1388_; lean_object* v___x_1390_; 
v___x_1388_ = lean_array_push(v_snd_1368_, v_a_1387_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 1, v___x_1388_);
lean_ctor_set(v___x_1370_, 0, v___x_1385_);
v___x_1390_ = v___x_1370_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1385_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v___x_1388_);
v___x_1390_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1391_ = lean_unsigned_to_nat(1u);
v___x_1392_ = lean_nat_add(v_a_1356_, v___x_1391_);
v___x_1393_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6___redArg(v_upperBound_1350_, v_header_1351_, v_xs_1352_, v_indVal_1353_, v_auxFunName_1354_, v_levelInsts_1355_, v___x_1392_, v___x_1390_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_);
return v___x_1393_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4___redArg___boxed(lean_object* v_upperBound_1462_, lean_object* v_header_1463_, lean_object* v_xs_1464_, lean_object* v_indVal_1465_, lean_object* v_auxFunName_1466_, lean_object* v_levelInsts_1467_, lean_object* v_a_1468_, lean_object* v_b_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4___redArg(v_upperBound_1462_, v_header_1463_, v_xs_1464_, v_indVal_1465_, v_auxFunName_1466_, v_levelInsts_1467_, v_a_1468_, v_b_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v_a_1468_);
lean_dec_ref(v_levelInsts_1467_);
lean_dec_ref(v_xs_1464_);
lean_dec_ref(v_header_1463_);
lean_dec(v_upperBound_1462_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg(lean_object* v_upperBound_1481_, lean_object* v___x_1482_, lean_object* v_xs_1483_, lean_object* v_indVal_1484_, lean_object* v_auxFunName_1485_, lean_object* v_levelInsts_1486_, lean_object* v_a_1487_, lean_object* v_b_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
uint8_t v___x_1494_; 
v___x_1494_ = lean_nat_dec_lt(v_a_1487_, v_upperBound_1481_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1495_; 
lean_dec(v_a_1487_);
lean_dec(v_auxFunName_1485_);
lean_dec_ref(v_indVal_1484_);
v___x_1495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1495_, 0, v_b_1488_);
return v___x_1495_;
}
else
{
lean_object* v_fst_1496_; lean_object* v_snd_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1598_; 
v_fst_1496_ = lean_ctor_get(v_b_1488_, 0);
v_snd_1497_ = lean_ctor_get(v_b_1488_, 1);
v_isSharedCheck_1598_ = !lean_is_exclusive(v_b_1488_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1499_ = v_b_1488_;
v_isShared_1500_ = v_isSharedCheck_1598_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_snd_1497_);
lean_inc(v_fst_1496_);
lean_dec(v_b_1488_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1598_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1501_ = l_Lean_instInhabitedExpr;
v___x_1502_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg___closed__1));
v___x_1503_ = l_Lean_Core_mkFreshUserName(v___x_1502_, v___y_1491_, v___y_1492_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v_a_1508_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
lean_inc(v_a_1504_);
lean_dec_ref_known(v___x_1503_, 1);
v___x_1505_ = l_Lean_mkIdent(v_a_1504_);
lean_inc(v___x_1505_);
v___x_1506_ = lean_array_push(v_fst_1496_, v___x_1505_);
v___x_1516_ = lean_nat_add(v___x_1482_, v_a_1487_);
v___x_1517_ = lean_array_get_borrowed(v___x_1501_, v_xs_1483_, v___x_1516_);
lean_dec(v___x_1516_);
lean_inc(v___y_1492_);
lean_inc_ref(v___y_1491_);
lean_inc(v___y_1490_);
lean_inc_ref(v___y_1489_);
lean_inc(v___x_1517_);
v___x_1518_ = lean_infer_type(v___x_1517_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_toConstantVal_1519_; lean_object* v_a_1520_; lean_object* v_name_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1579_; 
v_toConstantVal_1519_ = lean_ctor_get(v_indVal_1484_, 0);
lean_inc_ref(v_toConstantVal_1519_);
v_a_1520_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_a_1520_);
lean_dec_ref_known(v___x_1518_, 1);
v_name_1521_ = lean_ctor_get(v_toConstantVal_1519_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v_toConstantVal_1519_);
if (v_isSharedCheck_1579_ == 0)
{
lean_object* v_unused_1580_; lean_object* v_unused_1581_; 
v_unused_1580_ = lean_ctor_get(v_toConstantVal_1519_, 2);
lean_dec(v_unused_1580_);
v_unused_1581_ = lean_ctor_get(v_toConstantVal_1519_, 1);
lean_dec(v_unused_1581_);
v___x_1523_ = v_toConstantVal_1519_;
v_isShared_1524_ = v_isSharedCheck_1579_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_name_1521_);
lean_dec(v_toConstantVal_1519_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1579_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
uint8_t v___x_1525_; 
v___x_1525_ = l_Lean_Expr_isAppOf(v_a_1520_, v_name_1521_);
lean_dec(v_name_1521_);
lean_dec(v_a_1520_);
if (v___x_1525_ == 0)
{
lean_object* v___x_1526_; 
lean_del_object(v___x_1523_);
lean_inc(v___x_1517_);
v___x_1526_ = l_Lean_Meta_isType(v___x_1517_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; uint8_t v___x_1528_; 
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_a_1527_);
lean_dec_ref_known(v___x_1526_, 1);
v___x_1528_ = lean_unbox(v_a_1527_);
if (v___x_1528_ == 0)
{
lean_object* v_toCold_1529_; lean_object* v_ref_1530_; lean_object* v_quotContext_1531_; lean_object* v_currMacroScope_1532_; uint8_t v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v_toCold_1529_ = lean_ctor_get(v___y_1491_, 0);
v_ref_1530_ = lean_ctor_get(v___y_1491_, 2);
v_quotContext_1531_ = lean_ctor_get(v_toCold_1529_, 8);
v_currMacroScope_1532_ = lean_ctor_get(v_toCold_1529_, 9);
v___x_1533_ = lean_unbox(v_a_1527_);
lean_dec(v_a_1527_);
v___x_1534_ = l_Lean_SourceInfo_fromRef(v_ref_1530_, v___x_1533_);
v___x_1535_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1536_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1);
v___x_1537_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__2));
lean_inc(v_currMacroScope_1532_);
lean_inc(v_quotContext_1531_);
v___x_1538_ = l_Lean_addMacroScope(v_quotContext_1531_, v___x_1537_, v_currMacroScope_1532_);
v___x_1539_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__6));
lean_inc_n(v___x_1534_, 2);
v___x_1540_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1534_);
lean_ctor_set(v___x_1540_, 1, v___x_1536_);
lean_ctor_set(v___x_1540_, 2, v___x_1538_);
lean_ctor_set(v___x_1540_, 3, v___x_1539_);
v___x_1541_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1542_ = l_Lean_Syntax_node1(v___x_1534_, v___x_1541_, v___x_1505_);
v___x_1543_ = l_Lean_Syntax_node2(v___x_1534_, v___x_1535_, v___x_1540_, v___x_1542_);
v_a_1508_ = v___x_1543_;
goto v___jp_1507_;
}
else
{
lean_object* v_toCold_1544_; lean_object* v_ref_1545_; lean_object* v_quotContext_1546_; lean_object* v_currMacroScope_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
lean_dec(v_a_1527_);
v_toCold_1544_ = lean_ctor_get(v___y_1491_, 0);
v_ref_1545_ = lean_ctor_get(v___y_1491_, 2);
v_quotContext_1546_ = lean_ctor_get(v_toCold_1544_, 8);
v_currMacroScope_1547_ = lean_ctor_get(v_toCold_1544_, 9);
v___x_1548_ = l_Lean_SourceInfo_fromRef(v_ref_1545_, v___x_1525_);
v___x_1549_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1550_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8);
v___x_1551_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__9));
lean_inc(v_currMacroScope_1547_);
lean_inc(v_quotContext_1546_);
v___x_1552_ = l_Lean_addMacroScope(v_quotContext_1546_, v___x_1551_, v_currMacroScope_1547_);
v___x_1553_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__12));
lean_inc_n(v___x_1548_, 2);
v___x_1554_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1548_);
lean_ctor_set(v___x_1554_, 1, v___x_1550_);
lean_ctor_set(v___x_1554_, 2, v___x_1552_);
lean_ctor_set(v___x_1554_, 3, v___x_1553_);
v___x_1555_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1556_ = l_Lean_Syntax_node1(v___x_1548_, v___x_1555_, v___x_1505_);
v___x_1557_ = l_Lean_Syntax_node2(v___x_1548_, v___x_1549_, v___x_1554_, v___x_1556_);
v_a_1508_ = v___x_1557_;
goto v___jp_1507_;
}
}
else
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
lean_dec_ref(v___x_1506_);
lean_dec(v___x_1505_);
lean_del_object(v___x_1499_);
lean_dec(v_snd_1497_);
lean_dec(v_a_1487_);
lean_dec(v_auxFunName_1485_);
lean_dec_ref(v_indVal_1484_);
v_a_1558_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1560_ = v___x_1526_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1526_);
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
else
{
lean_object* v_ref_1566_; uint8_t v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1576_; 
v_ref_1566_ = lean_ctor_get(v___y_1491_, 2);
v___x_1567_ = 0;
v___x_1568_ = l_Lean_SourceInfo_fromRef(v_ref_1566_, v___x_1567_);
v___x_1569_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
lean_inc(v_auxFunName_1485_);
v___x_1570_ = l_Lean_mkIdent(v_auxFunName_1485_);
v___x_1571_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1572_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_1573_ = l_Array_append___redArg(v___x_1572_, v_levelInsts_1486_);
v___x_1574_ = lean_array_push(v___x_1573_, v___x_1505_);
lean_inc(v___x_1568_);
if (v_isShared_1524_ == 0)
{
lean_ctor_set_tag(v___x_1523_, 1);
lean_ctor_set(v___x_1523_, 2, v___x_1574_);
lean_ctor_set(v___x_1523_, 1, v___x_1571_);
lean_ctor_set(v___x_1523_, 0, v___x_1568_);
v___x_1576_ = v___x_1523_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1568_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v___x_1571_);
lean_ctor_set(v_reuseFailAlloc_1578_, 2, v___x_1574_);
v___x_1576_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
lean_object* v___x_1577_; 
v___x_1577_ = l_Lean_Syntax_node2(v___x_1568_, v___x_1569_, v___x_1570_, v___x_1576_);
v_a_1508_ = v___x_1577_;
goto v___jp_1507_;
}
}
}
}
else
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_dec_ref(v___x_1506_);
lean_dec(v___x_1505_);
lean_del_object(v___x_1499_);
lean_dec(v_snd_1497_);
lean_dec(v_a_1487_);
lean_dec(v_auxFunName_1485_);
lean_dec_ref(v_indVal_1484_);
v_a_1582_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1518_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1518_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
v___jp_1507_:
{
lean_object* v___x_1509_; lean_object* v___x_1511_; 
v___x_1509_ = lean_array_push(v_snd_1497_, v_a_1508_);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 1, v___x_1509_);
lean_ctor_set(v___x_1499_, 0, v___x_1506_);
v___x_1511_ = v___x_1499_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1506_);
lean_ctor_set(v_reuseFailAlloc_1515_, 1, v___x_1509_);
v___x_1511_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1512_ = lean_unsigned_to_nat(1u);
v___x_1513_ = lean_nat_add(v_a_1487_, v___x_1512_);
lean_dec(v_a_1487_);
v_a_1487_ = v___x_1513_;
v_b_1488_ = v___x_1511_;
goto _start;
}
}
}
else
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
lean_del_object(v___x_1499_);
lean_dec(v_snd_1497_);
lean_dec(v_fst_1496_);
lean_dec(v_a_1487_);
lean_dec(v_auxFunName_1485_);
lean_dec_ref(v_indVal_1484_);
v_a_1590_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1592_ = v___x_1503_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1503_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1590_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg___boxed(lean_object* v_upperBound_1599_, lean_object* v___x_1600_, lean_object* v_xs_1601_, lean_object* v_indVal_1602_, lean_object* v_auxFunName_1603_, lean_object* v_levelInsts_1604_, lean_object* v_a_1605_, lean_object* v_b_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg(v_upperBound_1599_, v___x_1600_, v_xs_1601_, v_indVal_1602_, v_auxFunName_1603_, v_levelInsts_1604_, v_a_1605_, v_b_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec_ref(v_levelInsts_1604_);
lean_dec_ref(v_xs_1601_);
lean_dec(v___x_1600_);
lean_dec(v_upperBound_1599_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3___redArg(lean_object* v_upperBound_1613_, lean_object* v___x_1614_, lean_object* v_xs_1615_, lean_object* v_indVal_1616_, lean_object* v_auxFunName_1617_, lean_object* v_levelInsts_1618_, lean_object* v_a_1619_, lean_object* v_b_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
uint8_t v___x_1628_; 
v___x_1628_ = lean_nat_dec_lt(v_a_1619_, v_upperBound_1613_);
if (v___x_1628_ == 0)
{
lean_object* v___x_1629_; 
lean_dec(v_auxFunName_1617_);
lean_dec_ref(v_indVal_1616_);
v___x_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1629_, 0, v_b_1620_);
return v___x_1629_;
}
else
{
lean_object* v_fst_1630_; lean_object* v_snd_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1732_; 
v_fst_1630_ = lean_ctor_get(v_b_1620_, 0);
v_snd_1631_ = lean_ctor_get(v_b_1620_, 1);
v_isSharedCheck_1732_ = !lean_is_exclusive(v_b_1620_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1633_ = v_b_1620_;
v_isShared_1634_ = v_isSharedCheck_1732_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_snd_1631_);
lean_inc(v_fst_1630_);
lean_dec(v_b_1620_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1732_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1635_ = l_Lean_instInhabitedExpr;
v___x_1636_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg___closed__1));
v___x_1637_ = l_Lean_Core_mkFreshUserName(v___x_1636_, v___y_1625_, v___y_1626_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v_a_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v_a_1642_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_a_1638_);
lean_dec_ref_known(v___x_1637_, 1);
v___x_1639_ = l_Lean_mkIdent(v_a_1638_);
lean_inc(v___x_1639_);
v___x_1640_ = lean_array_push(v_fst_1630_, v___x_1639_);
v___x_1650_ = lean_nat_add(v___x_1614_, v_a_1619_);
v___x_1651_ = lean_array_get_borrowed(v___x_1635_, v_xs_1615_, v___x_1650_);
lean_dec(v___x_1650_);
lean_inc(v___y_1626_);
lean_inc_ref(v___y_1625_);
lean_inc(v___y_1624_);
lean_inc_ref(v___y_1623_);
lean_inc(v___x_1651_);
v___x_1652_ = lean_infer_type(v___x_1651_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_toConstantVal_1653_; lean_object* v_a_1654_; lean_object* v_name_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1713_; 
v_toConstantVal_1653_ = lean_ctor_get(v_indVal_1616_, 0);
lean_inc_ref(v_toConstantVal_1653_);
v_a_1654_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_a_1654_);
lean_dec_ref_known(v___x_1652_, 1);
v_name_1655_ = lean_ctor_get(v_toConstantVal_1653_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v_toConstantVal_1653_);
if (v_isSharedCheck_1713_ == 0)
{
lean_object* v_unused_1714_; lean_object* v_unused_1715_; 
v_unused_1714_ = lean_ctor_get(v_toConstantVal_1653_, 2);
lean_dec(v_unused_1714_);
v_unused_1715_ = lean_ctor_get(v_toConstantVal_1653_, 1);
lean_dec(v_unused_1715_);
v___x_1657_ = v_toConstantVal_1653_;
v_isShared_1658_ = v_isSharedCheck_1713_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_name_1655_);
lean_dec(v_toConstantVal_1653_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1713_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
uint8_t v___x_1659_; 
v___x_1659_ = l_Lean_Expr_isAppOf(v_a_1654_, v_name_1655_);
lean_dec(v_name_1655_);
lean_dec(v_a_1654_);
if (v___x_1659_ == 0)
{
lean_object* v___x_1660_; 
lean_del_object(v___x_1657_);
lean_inc(v___x_1651_);
v___x_1660_ = l_Lean_Meta_isType(v___x_1651_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_a_1661_; uint8_t v___x_1662_; 
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_a_1661_);
lean_dec_ref_known(v___x_1660_, 1);
v___x_1662_ = lean_unbox(v_a_1661_);
if (v___x_1662_ == 0)
{
lean_object* v_toCold_1663_; lean_object* v_ref_1664_; lean_object* v_quotContext_1665_; lean_object* v_currMacroScope_1666_; uint8_t v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v_toCold_1663_ = lean_ctor_get(v___y_1625_, 0);
v_ref_1664_ = lean_ctor_get(v___y_1625_, 2);
v_quotContext_1665_ = lean_ctor_get(v_toCold_1663_, 8);
v_currMacroScope_1666_ = lean_ctor_get(v_toCold_1663_, 9);
v___x_1667_ = lean_unbox(v_a_1661_);
lean_dec(v_a_1661_);
v___x_1668_ = l_Lean_SourceInfo_fromRef(v_ref_1664_, v___x_1667_);
v___x_1669_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1670_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1);
v___x_1671_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__2));
lean_inc(v_currMacroScope_1666_);
lean_inc(v_quotContext_1665_);
v___x_1672_ = l_Lean_addMacroScope(v_quotContext_1665_, v___x_1671_, v_currMacroScope_1666_);
v___x_1673_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__6));
lean_inc_n(v___x_1668_, 2);
v___x_1674_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1668_);
lean_ctor_set(v___x_1674_, 1, v___x_1670_);
lean_ctor_set(v___x_1674_, 2, v___x_1672_);
lean_ctor_set(v___x_1674_, 3, v___x_1673_);
v___x_1675_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1676_ = l_Lean_Syntax_node1(v___x_1668_, v___x_1675_, v___x_1639_);
v___x_1677_ = l_Lean_Syntax_node2(v___x_1668_, v___x_1669_, v___x_1674_, v___x_1676_);
v_a_1642_ = v___x_1677_;
goto v___jp_1641_;
}
else
{
lean_object* v_toCold_1678_; lean_object* v_ref_1679_; lean_object* v_quotContext_1680_; lean_object* v_currMacroScope_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
lean_dec(v_a_1661_);
v_toCold_1678_ = lean_ctor_get(v___y_1625_, 0);
v_ref_1679_ = lean_ctor_get(v___y_1625_, 2);
v_quotContext_1680_ = lean_ctor_get(v_toCold_1678_, 8);
v_currMacroScope_1681_ = lean_ctor_get(v_toCold_1678_, 9);
v___x_1682_ = l_Lean_SourceInfo_fromRef(v_ref_1679_, v___x_1659_);
v___x_1683_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1684_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8);
v___x_1685_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__9));
lean_inc(v_currMacroScope_1681_);
lean_inc(v_quotContext_1680_);
v___x_1686_ = l_Lean_addMacroScope(v_quotContext_1680_, v___x_1685_, v_currMacroScope_1681_);
v___x_1687_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__12));
lean_inc_n(v___x_1682_, 2);
v___x_1688_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1682_);
lean_ctor_set(v___x_1688_, 1, v___x_1684_);
lean_ctor_set(v___x_1688_, 2, v___x_1686_);
lean_ctor_set(v___x_1688_, 3, v___x_1687_);
v___x_1689_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1690_ = l_Lean_Syntax_node1(v___x_1682_, v___x_1689_, v___x_1639_);
v___x_1691_ = l_Lean_Syntax_node2(v___x_1682_, v___x_1683_, v___x_1688_, v___x_1690_);
v_a_1642_ = v___x_1691_;
goto v___jp_1641_;
}
}
else
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1699_; 
lean_dec_ref(v___x_1640_);
lean_dec(v___x_1639_);
lean_del_object(v___x_1633_);
lean_dec(v_snd_1631_);
lean_dec(v_auxFunName_1617_);
lean_dec_ref(v_indVal_1616_);
v_a_1692_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1694_ = v___x_1660_;
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v___x_1660_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1697_; 
if (v_isShared_1695_ == 0)
{
v___x_1697_ = v___x_1694_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_a_1692_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
}
else
{
lean_object* v_ref_1700_; uint8_t v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1710_; 
v_ref_1700_ = lean_ctor_get(v___y_1625_, 2);
v___x_1701_ = 0;
v___x_1702_ = l_Lean_SourceInfo_fromRef(v_ref_1700_, v___x_1701_);
v___x_1703_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
lean_inc(v_auxFunName_1617_);
v___x_1704_ = l_Lean_mkIdent(v_auxFunName_1617_);
v___x_1705_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1706_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_1707_ = l_Array_append___redArg(v___x_1706_, v_levelInsts_1618_);
v___x_1708_ = lean_array_push(v___x_1707_, v___x_1639_);
lean_inc(v___x_1702_);
if (v_isShared_1658_ == 0)
{
lean_ctor_set_tag(v___x_1657_, 1);
lean_ctor_set(v___x_1657_, 2, v___x_1708_);
lean_ctor_set(v___x_1657_, 1, v___x_1705_);
lean_ctor_set(v___x_1657_, 0, v___x_1702_);
v___x_1710_ = v___x_1657_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v___x_1702_);
lean_ctor_set(v_reuseFailAlloc_1712_, 1, v___x_1705_);
lean_ctor_set(v_reuseFailAlloc_1712_, 2, v___x_1708_);
v___x_1710_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
lean_object* v___x_1711_; 
v___x_1711_ = l_Lean_Syntax_node2(v___x_1702_, v___x_1703_, v___x_1704_, v___x_1710_);
v_a_1642_ = v___x_1711_;
goto v___jp_1641_;
}
}
}
}
else
{
lean_object* v_a_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1723_; 
lean_dec_ref(v___x_1640_);
lean_dec(v___x_1639_);
lean_del_object(v___x_1633_);
lean_dec(v_snd_1631_);
lean_dec(v_auxFunName_1617_);
lean_dec_ref(v_indVal_1616_);
v_a_1716_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1718_ = v___x_1652_;
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_a_1716_);
lean_dec(v___x_1652_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1721_; 
if (v_isShared_1719_ == 0)
{
v___x_1721_ = v___x_1718_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_a_1716_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
v___jp_1641_:
{
lean_object* v___x_1643_; lean_object* v___x_1645_; 
v___x_1643_ = lean_array_push(v_snd_1631_, v_a_1642_);
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 1, v___x_1643_);
lean_ctor_set(v___x_1633_, 0, v___x_1640_);
v___x_1645_ = v___x_1633_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1640_);
lean_ctor_set(v_reuseFailAlloc_1649_, 1, v___x_1643_);
v___x_1645_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1646_ = lean_unsigned_to_nat(1u);
v___x_1647_ = lean_nat_add(v_a_1619_, v___x_1646_);
v___x_1648_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg(v_upperBound_1613_, v___x_1614_, v_xs_1615_, v_indVal_1616_, v_auxFunName_1617_, v_levelInsts_1618_, v___x_1647_, v___x_1645_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
return v___x_1648_;
}
}
}
else
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
lean_del_object(v___x_1633_);
lean_dec(v_snd_1631_);
lean_dec(v_fst_1630_);
lean_dec(v_auxFunName_1617_);
lean_dec_ref(v_indVal_1616_);
v_a_1724_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1726_ = v___x_1637_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1637_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3___redArg___boxed(lean_object* v_upperBound_1733_, lean_object* v___x_1734_, lean_object* v_xs_1735_, lean_object* v_indVal_1736_, lean_object* v_auxFunName_1737_, lean_object* v_levelInsts_1738_, lean_object* v_a_1739_, lean_object* v_b_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3___redArg(v_upperBound_1733_, v___x_1734_, v_xs_1735_, v_indVal_1736_, v_auxFunName_1737_, v_levelInsts_1738_, v_a_1739_, v_b_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1745_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v_a_1739_);
lean_dec_ref(v_levelInsts_1738_);
lean_dec_ref(v_xs_1735_);
lean_dec(v___x_1734_);
lean_dec(v_upperBound_1733_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__2(size_t v_sz_1749_, size_t v_i_1750_, lean_object* v_bs_1751_){
_start:
{
uint8_t v___x_1752_; 
v___x_1752_ = lean_usize_dec_lt(v_i_1750_, v_sz_1749_);
if (v___x_1752_ == 0)
{
return v_bs_1751_;
}
else
{
lean_object* v_v_1753_; lean_object* v___x_1754_; lean_object* v_bs_x27_1755_; size_t v___x_1756_; size_t v___x_1757_; lean_object* v___x_1758_; 
v_v_1753_ = lean_array_uget(v_bs_1751_, v_i_1750_);
v___x_1754_ = lean_unsigned_to_nat(0u);
v_bs_x27_1755_ = lean_array_uset(v_bs_1751_, v_i_1750_, v___x_1754_);
v___x_1756_ = ((size_t)1ULL);
v___x_1757_ = lean_usize_add(v_i_1750_, v___x_1756_);
v___x_1758_ = lean_array_uset(v_bs_x27_1755_, v_i_1750_, v_v_1753_);
v_i_1750_ = v___x_1757_;
v_bs_1751_ = v___x_1758_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__2___boxed(lean_object* v_sz_1760_, lean_object* v_i_1761_, lean_object* v_bs_1762_){
_start:
{
size_t v_sz_boxed_1763_; size_t v_i_boxed_1764_; lean_object* v_res_1765_; 
v_sz_boxed_1763_ = lean_unbox_usize(v_sz_1760_);
lean_dec(v_sz_1760_);
v_i_boxed_1764_ = lean_unbox_usize(v_i_1761_);
lean_dec(v_i_1761_);
v_res_1765_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__2(v_sz_boxed_1763_, v_i_boxed_1764_, v_bs_1762_);
return v_res_1765_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1773_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__9));
v___x_1774_ = l_Lean_mkAtom(v___x_1773_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1(lean_object* v_indVal_1776_, lean_object* v___x_1777_, lean_object* v___x_1778_, lean_object* v_numParams_1779_, lean_object* v_header_1780_, lean_object* v_auxFunName_1781_, lean_object* v_levelInsts_1782_, lean_object* v_numFields_1783_, lean_object* v_head_1784_, lean_object* v___f_1785_, lean_object* v_a_1786_, lean_object* v_name_1787_, lean_object* v_xs_1788_, lean_object* v_x_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v_numIndices_1797_; lean_object* v___x_1798_; 
v_numIndices_1797_ = lean_ctor_get(v_indVal_1776_, 2);
lean_inc_ref(v___x_1778_);
lean_inc(v___x_1777_);
v___x_1798_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg(v_numIndices_1797_, v___x_1777_, v___x_1778_, v___y_1794_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_object* v_a_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v_a_1799_ = lean_ctor_get(v___x_1798_, 0);
lean_inc(v_a_1799_);
lean_dec_ref_known(v___x_1798_, 1);
lean_inc_ref(v___x_1778_);
v___x_1800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1778_);
lean_ctor_set(v___x_1800_, 1, v___x_1778_);
lean_inc(v_auxFunName_1781_);
lean_inc_ref(v_indVal_1776_);
v___x_1801_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4___redArg(v_numParams_1779_, v_header_1780_, v_xs_1788_, v_indVal_1776_, v_auxFunName_1781_, v_levelInsts_1782_, v___x_1777_, v___x_1800_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v_a_1802_; lean_object* v_fst_1803_; lean_object* v_snd_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1924_; 
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
lean_inc(v_a_1802_);
lean_dec_ref_known(v___x_1801_, 1);
v_fst_1803_ = lean_ctor_get(v_a_1802_, 0);
v_snd_1804_ = lean_ctor_get(v_a_1802_, 1);
v_isSharedCheck_1924_ = !lean_is_exclusive(v_a_1802_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1806_ = v_a_1802_;
v_isShared_1807_ = v_isSharedCheck_1924_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_snd_1804_);
lean_inc(v_fst_1803_);
lean_dec(v_a_1802_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1924_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1809_; 
if (v_isShared_1807_ == 0)
{
v___x_1809_ = v___x_1806_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_fst_1803_);
lean_ctor_set(v_reuseFailAlloc_1923_, 1, v_snd_1804_);
v___x_1809_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
lean_object* v___x_1810_; 
v___x_1810_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3___redArg(v_numFields_1783_, v_numParams_1779_, v_xs_1788_, v_indVal_1776_, v_auxFunName_1781_, v_levelInsts_1782_, v___x_1777_, v___x_1809_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
lean_dec(v___x_1777_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; lean_object* v_fst_1812_; lean_object* v_snd_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1914_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
lean_inc(v_a_1811_);
lean_dec_ref_known(v___x_1810_, 1);
v_fst_1812_ = lean_ctor_get(v_a_1811_, 0);
v_snd_1813_ = lean_ctor_get(v_a_1811_, 1);
v_isSharedCheck_1914_ = !lean_is_exclusive(v_a_1811_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1815_ = v_a_1811_;
v_isShared_1816_ = v_isSharedCheck_1914_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_snd_1813_);
lean_inc(v_fst_1812_);
lean_dec(v_a_1811_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1914_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v_toCold_1817_; lean_object* v_ref_1818_; uint8_t v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1825_; 
v_toCold_1817_ = lean_ctor_get(v___y_1794_, 0);
v_ref_1818_ = lean_ctor_get(v___y_1794_, 2);
v___x_1819_ = 0;
v___x_1820_ = l_Lean_SourceInfo_fromRef(v_ref_1818_, v___x_1819_);
v___x_1821_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1822_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__3));
v___x_1823_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__4));
lean_inc(v___x_1820_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set_tag(v___x_1815_, 2);
lean_ctor_set(v___x_1815_, 1, v___x_1823_);
lean_ctor_set(v___x_1815_, 0, v___x_1820_);
v___x_1825_ = v___x_1815_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v___x_1820_);
lean_ctor_set(v_reuseFailAlloc_1913_, 1, v___x_1823_);
v___x_1825_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1826_ = l_Lean_mkIdent(v_head_1784_);
lean_inc_n(v___x_1820_, 2);
v___x_1827_ = l_Lean_Syntax_node2(v___x_1820_, v___x_1822_, v___x_1825_, v___x_1826_);
v___x_1828_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1829_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_1830_ = l_Array_append___redArg(v___x_1829_, v_fst_1812_);
lean_dec(v_fst_1812_);
v___x_1831_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1820_);
lean_ctor_set(v___x_1831_, 1, v___x_1828_);
lean_ctor_set(v___x_1831_, 2, v___x_1830_);
v___x_1832_ = l_Lean_Syntax_node2(v___x_1820_, v___x_1821_, v___x_1827_, v___x_1831_);
v___x_1833_ = lean_array_push(v_a_1799_, v___x_1832_);
lean_inc_ref(v___f_1785_);
lean_inc(v___y_1795_);
lean_inc_ref(v___y_1794_);
lean_inc(v___y_1793_);
lean_inc_ref(v___y_1792_);
lean_inc(v___y_1791_);
lean_inc_ref(v___y_1790_);
v___x_1834_ = lean_apply_7(v___f_1785_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, lean_box(0));
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_a_1835_; lean_object* v_quotContext_1836_; lean_object* v_currMacroScope_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___y_1845_; lean_object* v___x_1891_; 
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
lean_inc_n(v_a_1835_, 2);
lean_dec_ref_known(v___x_1834_, 1);
v_quotContext_1836_ = lean_ctor_get(v_toCold_1817_, 8);
v_currMacroScope_1837_ = lean_ctor_get(v_toCold_1817_, 9);
v___x_1838_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__4));
v___x_1839_ = lean_box(0);
v___x_1840_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__2, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__2_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__2);
lean_inc(v_currMacroScope_1837_);
lean_inc(v_quotContext_1836_);
v___x_1841_ = l_Lean_addMacroScope(v_quotContext_1836_, v___x_1838_, v_currMacroScope_1837_);
v___x_1842_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__10));
v___x_1843_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1843_, 0, v_a_1835_);
lean_ctor_set(v___x_1843_, 1, v___x_1840_);
lean_ctor_set(v___x_1843_, 2, v___x_1841_);
lean_ctor_set(v___x_1843_, 3, v___x_1842_);
lean_inc(v_name_1787_);
v___x_1891_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_1839_, v_name_1787_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v___x_1892_; 
v___x_1892_ = l_Lean_quoteNameMk(v_name_1787_);
v___y_1845_ = v___x_1892_;
goto v___jp_1844_;
}
else
{
lean_object* v_val_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
lean_dec(v_name_1787_);
v_val_1893_ = lean_ctor_get(v___x_1891_, 0);
lean_inc(v_val_1893_);
lean_dec_ref_known(v___x_1891_, 1);
v___x_1894_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__16));
v___x_1895_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__17));
v___x_1896_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__18));
v___x_1897_ = lean_string_intercalate(v___x_1896_, v_val_1893_);
v___x_1898_ = lean_string_append(v___x_1895_, v___x_1897_);
lean_dec_ref(v___x_1897_);
v___x_1899_ = lean_box(2);
v___x_1900_ = l_Lean_Syntax_mkNameLit(v___x_1898_, v___x_1899_);
v___x_1901_ = lean_unsigned_to_nat(1u);
v___x_1902_ = lean_mk_empty_array_with_capacity(v___x_1901_);
v___x_1903_ = lean_array_push(v___x_1902_, v___x_1900_);
v___x_1904_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1899_);
lean_ctor_set(v___x_1904_, 1, v___x_1894_);
lean_ctor_set(v___x_1904_, 2, v___x_1903_);
v___y_1845_ = v___x_1904_;
goto v___jp_1844_;
}
v___jp_1844_:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1846_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__12));
v___x_1847_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__13));
lean_inc_n(v_a_1835_, 5);
v___x_1848_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1848_, 0, v_a_1835_);
lean_ctor_set(v___x_1848_, 1, v___x_1847_);
v___x_1849_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__9));
v___x_1850_ = l_Lean_Syntax_SepArray_ofElems(v___x_1849_, v_a_1786_);
v___x_1851_ = l_Array_append___redArg(v___x_1829_, v___x_1850_);
lean_dec_ref(v___x_1850_);
v___x_1852_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1852_, 0, v_a_1835_);
lean_ctor_set(v___x_1852_, 1, v___x_1828_);
lean_ctor_set(v___x_1852_, 2, v___x_1851_);
v___x_1853_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__14));
v___x_1854_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1854_, 0, v_a_1835_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
v___x_1855_ = l_Lean_Syntax_node3(v_a_1835_, v___x_1846_, v___x_1848_, v___x_1852_, v___x_1854_);
v___x_1856_ = l_Lean_Syntax_node2(v_a_1835_, v___x_1828_, v___y_1845_, v___x_1855_);
v___x_1857_ = l_Lean_Syntax_node2(v_a_1835_, v___x_1821_, v___x_1843_, v___x_1856_);
v___x_1858_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm(v___x_1857_, v_snd_1813_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
lean_dec(v_snd_1813_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v_a_1859_; lean_object* v___x_1860_; 
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
lean_inc(v_a_1859_);
lean_dec_ref_known(v___x_1858_, 1);
lean_inc(v___y_1795_);
lean_inc_ref(v___y_1794_);
lean_inc(v___y_1793_);
lean_inc_ref(v___y_1792_);
lean_inc(v___y_1791_);
lean_inc_ref(v___y_1790_);
v___x_1860_ = lean_apply_7(v___f_1785_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, lean_box(0));
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1882_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1863_ = v___x_1860_;
v_isShared_1864_ = v_isSharedCheck_1882_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1860_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1882_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; size_t v_sz_1868_; size_t v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1880_; 
v___x_1865_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__1));
v___x_1866_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__2));
lean_inc_n(v_a_1861_, 4);
v___x_1867_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1867_, 0, v_a_1861_);
lean_ctor_set(v___x_1867_, 1, v___x_1866_);
v_sz_1868_ = lean_array_size(v___x_1833_);
v___x_1869_ = ((size_t)0ULL);
v___x_1870_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__2(v_sz_1868_, v___x_1869_, v___x_1833_);
v___x_1871_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__3);
v___x_1872_ = l_Lean_mkSepArray(v___x_1870_, v___x_1871_);
lean_dec_ref(v___x_1870_);
v___x_1873_ = l_Array_append___redArg(v___x_1829_, v___x_1872_);
lean_dec_ref(v___x_1872_);
v___x_1874_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1874_, 0, v_a_1861_);
lean_ctor_set(v___x_1874_, 1, v___x_1828_);
lean_ctor_set(v___x_1874_, 2, v___x_1873_);
v___x_1875_ = l_Lean_Syntax_node1(v_a_1861_, v___x_1828_, v___x_1874_);
v___x_1876_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__4));
v___x_1877_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1877_, 0, v_a_1861_);
lean_ctor_set(v___x_1877_, 1, v___x_1876_);
v___x_1878_ = l_Lean_Syntax_node4(v_a_1861_, v___x_1865_, v___x_1867_, v___x_1875_, v___x_1877_, v_a_1859_);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 0, v___x_1878_);
v___x_1880_ = v___x_1863_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v___x_1878_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
else
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1890_; 
lean_dec(v_a_1859_);
lean_dec_ref(v___x_1833_);
v_a_1883_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1885_ = v___x_1860_;
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1860_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_a_1883_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
}
else
{
lean_dec_ref(v___x_1833_);
lean_dec_ref(v___f_1785_);
return v___x_1858_;
}
}
}
else
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1912_; 
lean_dec_ref(v___x_1833_);
lean_dec(v_snd_1813_);
lean_dec(v_name_1787_);
lean_dec_ref(v___f_1785_);
v_a_1905_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1907_ = v___x_1834_;
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1834_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1908_ == 0)
{
v___x_1910_ = v___x_1907_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_a_1905_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
}
}
else
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1922_; 
lean_dec(v_a_1799_);
lean_dec(v_name_1787_);
lean_dec_ref(v___f_1785_);
lean_dec(v_head_1784_);
v_a_1915_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1917_ = v___x_1810_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1810_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1918_ == 0)
{
v___x_1920_ = v___x_1917_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1915_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
}
}
}
else
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1932_; 
lean_dec(v_a_1799_);
lean_dec(v_name_1787_);
lean_dec_ref(v___f_1785_);
lean_dec(v_head_1784_);
lean_dec(v_auxFunName_1781_);
lean_dec(v___x_1777_);
lean_dec_ref(v_indVal_1776_);
v_a_1925_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1927_ = v___x_1801_;
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1801_);
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
else
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
lean_dec(v_name_1787_);
lean_dec_ref(v___f_1785_);
lean_dec(v_head_1784_);
lean_dec(v_auxFunName_1781_);
lean_dec_ref(v___x_1778_);
lean_dec(v___x_1777_);
lean_dec_ref(v_indVal_1776_);
v_a_1933_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___x_1798_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1798_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_indVal_1941_ = _args[0];
lean_object* v___x_1942_ = _args[1];
lean_object* v___x_1943_ = _args[2];
lean_object* v_numParams_1944_ = _args[3];
lean_object* v_header_1945_ = _args[4];
lean_object* v_auxFunName_1946_ = _args[5];
lean_object* v_levelInsts_1947_ = _args[6];
lean_object* v_numFields_1948_ = _args[7];
lean_object* v_head_1949_ = _args[8];
lean_object* v___f_1950_ = _args[9];
lean_object* v_a_1951_ = _args[10];
lean_object* v_name_1952_ = _args[11];
lean_object* v_xs_1953_ = _args[12];
lean_object* v_x_1954_ = _args[13];
lean_object* v___y_1955_ = _args[14];
lean_object* v___y_1956_ = _args[15];
lean_object* v___y_1957_ = _args[16];
lean_object* v___y_1958_ = _args[17];
lean_object* v___y_1959_ = _args[18];
lean_object* v___y_1960_ = _args[19];
lean_object* v___y_1961_ = _args[20];
_start:
{
lean_object* v_res_1962_; 
v_res_1962_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1(v_indVal_1941_, v___x_1942_, v___x_1943_, v_numParams_1944_, v_header_1945_, v_auxFunName_1946_, v_levelInsts_1947_, v_numFields_1948_, v_head_1949_, v___f_1950_, v_a_1951_, v_name_1952_, v_xs_1953_, v_x_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec_ref(v_x_1954_);
lean_dec_ref(v_xs_1953_);
lean_dec_ref(v_a_1951_);
lean_dec(v_numFields_1948_);
lean_dec_ref(v_levelInsts_1947_);
lean_dec_ref(v_header_1945_);
lean_dec(v_numParams_1944_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg(lean_object* v_a_1964_, lean_object* v_indVal_1965_, lean_object* v_auxFunName_1966_, lean_object* v_levelInsts_1967_, lean_object* v_header_1968_, lean_object* v_as_x27_1969_, lean_object* v_b_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
if (lean_obj_tag(v_as_x27_1969_) == 0)
{
lean_object* v___x_1978_; 
lean_dec_ref(v_header_1968_);
lean_dec_ref(v_levelInsts_1967_);
lean_dec(v_auxFunName_1966_);
lean_dec_ref(v_indVal_1965_);
lean_dec_ref(v_a_1964_);
v___x_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1978_, 0, v_b_1970_);
return v___x_1978_;
}
else
{
lean_object* v_head_1979_; lean_object* v_tail_1980_; lean_object* v___f_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v_head_1979_ = lean_ctor_get(v_as_x27_1969_, 0);
v_tail_1980_ = lean_ctor_get(v_as_x27_1969_, 1);
v___f_1981_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___closed__0));
v___x_1982_ = lean_unsigned_to_nat(0u);
v___x_1983_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__0));
lean_inc(v_head_1979_);
v___x_1984_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1(v_head_1979_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v_a_1985_; lean_object* v_toConstantVal_1986_; lean_object* v_numParams_1987_; lean_object* v_numFields_1988_; lean_object* v_name_1989_; lean_object* v_type_1990_; lean_object* v___f_1991_; uint8_t v___x_1992_; lean_object* v___x_1993_; 
v_a_1985_ = lean_ctor_get(v___x_1984_, 0);
lean_inc(v_a_1985_);
lean_dec_ref_known(v___x_1984_, 1);
v_toConstantVal_1986_ = lean_ctor_get(v_a_1985_, 0);
lean_inc_ref(v_toConstantVal_1986_);
v_numParams_1987_ = lean_ctor_get(v_a_1985_, 3);
lean_inc(v_numParams_1987_);
v_numFields_1988_ = lean_ctor_get(v_a_1985_, 4);
lean_inc(v_numFields_1988_);
lean_dec(v_a_1985_);
v_name_1989_ = lean_ctor_get(v_toConstantVal_1986_, 0);
lean_inc(v_name_1989_);
v_type_1990_ = lean_ctor_get(v_toConstantVal_1986_, 2);
lean_inc_ref(v_type_1990_);
lean_dec_ref(v_toConstantVal_1986_);
lean_inc_ref(v_a_1964_);
lean_inc(v_head_1979_);
lean_inc_ref(v_levelInsts_1967_);
lean_inc(v_auxFunName_1966_);
lean_inc_ref(v_header_1968_);
lean_inc_ref(v_indVal_1965_);
v___f_1991_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___boxed), 21, 12);
lean_closure_set(v___f_1991_, 0, v_indVal_1965_);
lean_closure_set(v___f_1991_, 1, v___x_1982_);
lean_closure_set(v___f_1991_, 2, v___x_1983_);
lean_closure_set(v___f_1991_, 3, v_numParams_1987_);
lean_closure_set(v___f_1991_, 4, v_header_1968_);
lean_closure_set(v___f_1991_, 5, v_auxFunName_1966_);
lean_closure_set(v___f_1991_, 6, v_levelInsts_1967_);
lean_closure_set(v___f_1991_, 7, v_numFields_1988_);
lean_closure_set(v___f_1991_, 8, v_head_1979_);
lean_closure_set(v___f_1991_, 9, v___f_1981_);
lean_closure_set(v___f_1991_, 10, v_a_1964_);
lean_closure_set(v___f_1991_, 11, v_name_1989_);
v___x_1992_ = 0;
v___x_1993_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg(v_type_1990_, v___f_1991_, v___x_1992_, v___x_1992_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_a_1994_; lean_object* v___x_1995_; 
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
lean_inc(v_a_1994_);
lean_dec_ref_known(v___x_1993_, 1);
v___x_1995_ = lean_array_push(v_b_1970_, v_a_1994_);
v_as_x27_1969_ = v_tail_1980_;
v_b_1970_ = v___x_1995_;
goto _start;
}
else
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2004_; 
lean_dec_ref(v_b_1970_);
lean_dec_ref(v_header_1968_);
lean_dec_ref(v_levelInsts_1967_);
lean_dec(v_auxFunName_1966_);
lean_dec_ref(v_indVal_1965_);
lean_dec_ref(v_a_1964_);
v_a_1997_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1999_ = v___x_1993_;
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___x_1993_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
if (v_isShared_2000_ == 0)
{
v___x_2002_ = v___x_1999_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_a_1997_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
else
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2012_; 
lean_dec_ref(v_b_1970_);
lean_dec_ref(v_header_1968_);
lean_dec_ref(v_levelInsts_1967_);
lean_dec(v_auxFunName_1966_);
lean_dec_ref(v_indVal_1965_);
lean_dec_ref(v_a_1964_);
v_a_2005_ = lean_ctor_get(v___x_1984_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2007_ = v___x_1984_;
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_1984_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2010_; 
if (v_isShared_2008_ == 0)
{
v___x_2010_ = v___x_2007_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_a_2005_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___boxed(lean_object* v_a_2013_, lean_object* v_indVal_2014_, lean_object* v_auxFunName_2015_, lean_object* v_levelInsts_2016_, lean_object* v_header_2017_, lean_object* v_as_x27_2018_, lean_object* v_b_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_){
_start:
{
lean_object* v_res_2027_; 
v_res_2027_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg(v_a_2013_, v_indVal_2014_, v_auxFunName_2015_, v_levelInsts_2016_, v_header_2017_, v_as_x27_2018_, v_b_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
lean_dec(v___y_2021_);
lean_dec_ref(v___y_2020_);
lean_dec(v_as_x27_2018_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__7(size_t v_sz_2028_, size_t v_i_2029_, lean_object* v_bs_2030_){
_start:
{
uint8_t v___x_2031_; 
v___x_2031_ = lean_usize_dec_lt(v_i_2029_, v_sz_2028_);
if (v___x_2031_ == 0)
{
return v_bs_2030_;
}
else
{
lean_object* v_v_2032_; lean_object* v___x_2033_; lean_object* v_bs_x27_2034_; size_t v___x_2035_; size_t v___x_2036_; lean_object* v___x_2037_; 
v_v_2032_ = lean_array_uget(v_bs_2030_, v_i_2029_);
v___x_2033_ = lean_unsigned_to_nat(0u);
v_bs_x27_2034_ = lean_array_uset(v_bs_2030_, v_i_2029_, v___x_2033_);
v___x_2035_ = ((size_t)1ULL);
v___x_2036_ = lean_usize_add(v_i_2029_, v___x_2035_);
v___x_2037_ = lean_array_uset(v_bs_x27_2034_, v_i_2029_, v_v_2032_);
v_i_2029_ = v___x_2036_;
v_bs_2030_ = v___x_2037_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__7___boxed(lean_object* v_sz_2039_, lean_object* v_i_2040_, lean_object* v_bs_2041_){
_start:
{
size_t v_sz_boxed_2042_; size_t v_i_boxed_2043_; lean_object* v_res_2044_; 
v_sz_boxed_2042_ = lean_unbox_usize(v_sz_2039_);
lean_dec(v_sz_2039_);
v_i_boxed_2043_ = lean_unbox_usize(v_i_2040_);
lean_dec(v_i_2040_);
v_res_2044_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__7(v_sz_boxed_2042_, v_i_boxed_2043_, v_bs_2041_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts(lean_object* v_header_2045_, lean_object* v_indVal_2046_, lean_object* v_auxFunName_2047_, lean_object* v_levelInsts_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_){
_start:
{
size_t v_sz_2056_; size_t v___x_2057_; lean_object* v___x_2058_; 
v_sz_2056_ = lean_array_size(v_levelInsts_2048_);
v___x_2057_ = ((size_t)0ULL);
lean_inc_ref(v_levelInsts_2048_);
v___x_2058_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg(v_sz_2056_, v___x_2057_, v_levelInsts_2048_, v_a_2053_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; lean_object* v_ctors_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_a_2059_);
lean_dec_ref_known(v___x_2058_, 1);
v_ctors_2060_ = lean_ctor_get(v_indVal_2046_, 4);
lean_inc(v_ctors_2060_);
v___x_2061_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__0));
v___x_2062_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg(v_a_2059_, v_indVal_2046_, v_auxFunName_2047_, v_levelInsts_2048_, v_header_2045_, v_ctors_2060_, v___x_2061_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_);
lean_dec(v_ctors_2060_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2072_; 
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2065_ = v___x_2062_;
v_isShared_2066_ = v_isSharedCheck_2072_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2062_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2072_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
size_t v_sz_2067_; lean_object* v___x_2068_; lean_object* v___x_2070_; 
v_sz_2067_ = lean_array_size(v_a_2063_);
v___x_2068_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__7(v_sz_2067_, v___x_2057_, v_a_2063_);
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 0, v___x_2068_);
v___x_2070_ = v___x_2065_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v___x_2068_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
else
{
return v___x_2062_;
}
}
else
{
lean_dec_ref(v_levelInsts_2048_);
lean_dec(v_auxFunName_2047_);
lean_dec_ref(v_indVal_2046_);
lean_dec_ref(v_header_2045_);
return v___x_2058_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts___boxed(lean_object* v_header_2073_, lean_object* v_indVal_2074_, lean_object* v_auxFunName_2075_, lean_object* v_levelInsts_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts(v_header_2073_, v_indVal_2074_, v_auxFunName_2075_, v_levelInsts_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
lean_dec(v_a_2082_);
lean_dec_ref(v_a_2081_);
lean_dec(v_a_2080_);
lean_dec_ref(v_a_2079_);
lean_dec(v_a_2078_);
lean_dec_ref(v_a_2077_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0(size_t v_sz_2085_, size_t v_i_2086_, lean_object* v_bs_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
lean_object* v___x_2095_; 
v___x_2095_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg(v_sz_2085_, v_i_2086_, v_bs_2087_, v___y_2092_);
return v___x_2095_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___boxed(lean_object* v_sz_2096_, lean_object* v_i_2097_, lean_object* v_bs_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
size_t v_sz_boxed_2106_; size_t v_i_boxed_2107_; lean_object* v_res_2108_; 
v_sz_boxed_2106_ = lean_unbox_usize(v_sz_2096_);
lean_dec(v_sz_2096_);
v_i_boxed_2107_ = lean_unbox_usize(v_i_2097_);
lean_dec(v_i_2097_);
v_res_2108_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0(v_sz_boxed_2106_, v_i_boxed_2107_, v_bs_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3(lean_object* v_upperBound_2109_, lean_object* v___x_2110_, lean_object* v_xs_2111_, lean_object* v_indVal_2112_, lean_object* v_auxFunName_2113_, lean_object* v_levelInsts_2114_, lean_object* v_inst_2115_, lean_object* v_R_2116_, lean_object* v_a_2117_, lean_object* v_b_2118_, lean_object* v_c_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_){
_start:
{
lean_object* v___x_2127_; 
v___x_2127_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3___redArg(v_upperBound_2109_, v___x_2110_, v_xs_2111_, v_indVal_2112_, v_auxFunName_2113_, v_levelInsts_2114_, v_a_2117_, v_b_2118_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3___boxed(lean_object** _args){
lean_object* v_upperBound_2128_ = _args[0];
lean_object* v___x_2129_ = _args[1];
lean_object* v_xs_2130_ = _args[2];
lean_object* v_indVal_2131_ = _args[3];
lean_object* v_auxFunName_2132_ = _args[4];
lean_object* v_levelInsts_2133_ = _args[5];
lean_object* v_inst_2134_ = _args[6];
lean_object* v_R_2135_ = _args[7];
lean_object* v_a_2136_ = _args[8];
lean_object* v_b_2137_ = _args[9];
lean_object* v_c_2138_ = _args[10];
lean_object* v___y_2139_ = _args[11];
lean_object* v___y_2140_ = _args[12];
lean_object* v___y_2141_ = _args[13];
lean_object* v___y_2142_ = _args[14];
lean_object* v___y_2143_ = _args[15];
lean_object* v___y_2144_ = _args[16];
lean_object* v___y_2145_ = _args[17];
_start:
{
lean_object* v_res_2146_; 
v_res_2146_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3(v_upperBound_2128_, v___x_2129_, v_xs_2130_, v_indVal_2131_, v_auxFunName_2132_, v_levelInsts_2133_, v_inst_2134_, v_R_2135_, v_a_2136_, v_b_2137_, v_c_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
lean_dec(v___y_2142_);
lean_dec_ref(v___y_2141_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
lean_dec(v_a_2136_);
lean_dec_ref(v_levelInsts_2133_);
lean_dec_ref(v_xs_2130_);
lean_dec(v___x_2129_);
lean_dec(v_upperBound_2128_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4(lean_object* v_upperBound_2147_, lean_object* v_header_2148_, lean_object* v_xs_2149_, lean_object* v_indVal_2150_, lean_object* v_auxFunName_2151_, lean_object* v_levelInsts_2152_, lean_object* v_inst_2153_, lean_object* v_R_2154_, lean_object* v_a_2155_, lean_object* v_b_2156_, lean_object* v_c_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
lean_object* v___x_2165_; 
v___x_2165_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4___redArg(v_upperBound_2147_, v_header_2148_, v_xs_2149_, v_indVal_2150_, v_auxFunName_2151_, v_levelInsts_2152_, v_a_2155_, v_b_2156_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_2166_ = _args[0];
lean_object* v_header_2167_ = _args[1];
lean_object* v_xs_2168_ = _args[2];
lean_object* v_indVal_2169_ = _args[3];
lean_object* v_auxFunName_2170_ = _args[4];
lean_object* v_levelInsts_2171_ = _args[5];
lean_object* v_inst_2172_ = _args[6];
lean_object* v_R_2173_ = _args[7];
lean_object* v_a_2174_ = _args[8];
lean_object* v_b_2175_ = _args[9];
lean_object* v_c_2176_ = _args[10];
lean_object* v___y_2177_ = _args[11];
lean_object* v___y_2178_ = _args[12];
lean_object* v___y_2179_ = _args[13];
lean_object* v___y_2180_ = _args[14];
lean_object* v___y_2181_ = _args[15];
lean_object* v___y_2182_ = _args[16];
lean_object* v___y_2183_ = _args[17];
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4(v_upperBound_2166_, v_header_2167_, v_xs_2168_, v_indVal_2169_, v_auxFunName_2170_, v_levelInsts_2171_, v_inst_2172_, v_R_2173_, v_a_2174_, v_b_2175_, v_c_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
lean_dec(v_a_2174_);
lean_dec_ref(v_levelInsts_2171_);
lean_dec_ref(v_xs_2168_);
lean_dec_ref(v_header_2167_);
lean_dec(v_upperBound_2166_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5(lean_object* v_upperBound_2185_, lean_object* v_inst_2186_, lean_object* v_R_2187_, lean_object* v_a_2188_, lean_object* v_b_2189_, lean_object* v_c_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
lean_object* v___x_2198_; 
v___x_2198_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg(v_upperBound_2185_, v_a_2188_, v_b_2189_, v___y_2195_);
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___boxed(lean_object* v_upperBound_2199_, lean_object* v_inst_2200_, lean_object* v_R_2201_, lean_object* v_a_2202_, lean_object* v_b_2203_, lean_object* v_c_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
lean_object* v_res_2212_; 
v_res_2212_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5(v_upperBound_2199_, v_inst_2200_, v_R_2201_, v_a_2202_, v_b_2203_, v_c_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
lean_dec(v___y_2208_);
lean_dec_ref(v___y_2207_);
lean_dec(v___y_2206_);
lean_dec_ref(v___y_2205_);
lean_dec(v_upperBound_2199_);
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6(lean_object* v_a_2213_, lean_object* v_indVal_2214_, lean_object* v_auxFunName_2215_, lean_object* v_levelInsts_2216_, lean_object* v_header_2217_, lean_object* v_as_2218_, lean_object* v_as_x27_2219_, lean_object* v_b_2220_, lean_object* v_a_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
lean_object* v___x_2229_; 
v___x_2229_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg(v_a_2213_, v_indVal_2214_, v_auxFunName_2215_, v_levelInsts_2216_, v_header_2217_, v_as_x27_2219_, v_b_2220_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___boxed(lean_object* v_a_2230_, lean_object* v_indVal_2231_, lean_object* v_auxFunName_2232_, lean_object* v_levelInsts_2233_, lean_object* v_header_2234_, lean_object* v_as_2235_, lean_object* v_as_x27_2236_, lean_object* v_b_2237_, lean_object* v_a_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_){
_start:
{
lean_object* v_res_2246_; 
v_res_2246_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6(v_a_2230_, v_indVal_2231_, v_auxFunName_2232_, v_levelInsts_2233_, v_header_2234_, v_as_2235_, v_as_x27_2236_, v_b_2237_, v_a_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
lean_dec(v___y_2242_);
lean_dec_ref(v___y_2241_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec(v_as_x27_2236_);
lean_dec(v_as_2235_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4(lean_object* v_upperBound_2247_, lean_object* v___x_2248_, lean_object* v_xs_2249_, lean_object* v_indVal_2250_, lean_object* v_auxFunName_2251_, lean_object* v_levelInsts_2252_, lean_object* v_inst_2253_, lean_object* v_R_2254_, lean_object* v_a_2255_, lean_object* v_b_2256_, lean_object* v_c_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
lean_object* v___x_2265_; 
v___x_2265_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg(v_upperBound_2247_, v___x_2248_, v_xs_2249_, v_indVal_2250_, v_auxFunName_2251_, v_levelInsts_2252_, v_a_2255_, v_b_2256_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_2266_ = _args[0];
lean_object* v___x_2267_ = _args[1];
lean_object* v_xs_2268_ = _args[2];
lean_object* v_indVal_2269_ = _args[3];
lean_object* v_auxFunName_2270_ = _args[4];
lean_object* v_levelInsts_2271_ = _args[5];
lean_object* v_inst_2272_ = _args[6];
lean_object* v_R_2273_ = _args[7];
lean_object* v_a_2274_ = _args[8];
lean_object* v_b_2275_ = _args[9];
lean_object* v_c_2276_ = _args[10];
lean_object* v___y_2277_ = _args[11];
lean_object* v___y_2278_ = _args[12];
lean_object* v___y_2279_ = _args[13];
lean_object* v___y_2280_ = _args[14];
lean_object* v___y_2281_ = _args[15];
lean_object* v___y_2282_ = _args[16];
lean_object* v___y_2283_ = _args[17];
_start:
{
lean_object* v_res_2284_; 
v_res_2284_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4(v_upperBound_2266_, v___x_2267_, v_xs_2268_, v_indVal_2269_, v_auxFunName_2270_, v_levelInsts_2271_, v_inst_2272_, v_R_2273_, v_a_2274_, v_b_2275_, v_c_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec_ref(v_levelInsts_2271_);
lean_dec_ref(v_xs_2268_);
lean_dec(v___x_2267_);
lean_dec(v_upperBound_2266_);
return v_res_2284_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6(lean_object* v_upperBound_2285_, lean_object* v_header_2286_, lean_object* v_xs_2287_, lean_object* v_indVal_2288_, lean_object* v_auxFunName_2289_, lean_object* v_levelInsts_2290_, lean_object* v_inst_2291_, lean_object* v_R_2292_, lean_object* v_a_2293_, lean_object* v_b_2294_, lean_object* v_c_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
lean_object* v___x_2303_; 
v___x_2303_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6___redArg(v_upperBound_2285_, v_header_2286_, v_xs_2287_, v_indVal_2288_, v_auxFunName_2289_, v_levelInsts_2290_, v_a_2293_, v_b_2294_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6___boxed(lean_object** _args){
lean_object* v_upperBound_2304_ = _args[0];
lean_object* v_header_2305_ = _args[1];
lean_object* v_xs_2306_ = _args[2];
lean_object* v_indVal_2307_ = _args[3];
lean_object* v_auxFunName_2308_ = _args[4];
lean_object* v_levelInsts_2309_ = _args[5];
lean_object* v_inst_2310_ = _args[6];
lean_object* v_R_2311_ = _args[7];
lean_object* v_a_2312_ = _args[8];
lean_object* v_b_2313_ = _args[9];
lean_object* v_c_2314_ = _args[10];
lean_object* v___y_2315_ = _args[11];
lean_object* v___y_2316_ = _args[12];
lean_object* v___y_2317_ = _args[13];
lean_object* v___y_2318_ = _args[14];
lean_object* v___y_2319_ = _args[15];
lean_object* v___y_2320_ = _args[16];
lean_object* v___y_2321_ = _args[17];
_start:
{
lean_object* v_res_2322_; 
v_res_2322_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6(v_upperBound_2304_, v_header_2305_, v_xs_2306_, v_indVal_2307_, v_auxFunName_2308_, v_levelInsts_2309_, v_inst_2310_, v_R_2311_, v_a_2312_, v_b_2313_, v_c_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec_ref(v_levelInsts_2309_);
lean_dec_ref(v_xs_2306_);
lean_dec_ref(v_header_2305_);
lean_dec(v_upperBound_2304_);
return v_res_2322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody(lean_object* v_header_2336_, lean_object* v_indVal_2337_, lean_object* v_auxFunName_2338_, lean_object* v_levelInsts_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_){
_start:
{
lean_object* v___x_2347_; 
lean_inc_ref(v_indVal_2337_);
lean_inc_ref(v_header_2336_);
v___x_2347_ = l_Lean_Elab_Deriving_mkDiscrs(v_header_2336_, v_indVal_2337_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; lean_object* v___x_2349_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
lean_inc(v_a_2348_);
lean_dec_ref_known(v___x_2347_, 1);
v___x_2349_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts(v_header_2336_, v_indVal_2337_, v_auxFunName_2338_, v_levelInsts_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2380_; 
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2352_ = v___x_2349_;
v_isShared_2353_ = v_isSharedCheck_2380_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2349_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2380_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v_ref_2354_; uint8_t v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; size_t v_sz_2363_; size_t v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2378_; 
v_ref_2354_ = lean_ctor_get(v_a_2344_, 2);
v___x_2355_ = 0;
v___x_2356_ = l_Lean_SourceInfo_fromRef(v_ref_2354_, v___x_2355_);
v___x_2357_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__0));
v___x_2358_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__1));
lean_inc_n(v___x_2356_, 6);
v___x_2359_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2356_);
lean_ctor_set(v___x_2359_, 1, v___x_2357_);
v___x_2360_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_2361_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_2362_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2356_);
lean_ctor_set(v___x_2362_, 1, v___x_2360_);
lean_ctor_set(v___x_2362_, 2, v___x_2361_);
v_sz_2363_ = lean_array_size(v_a_2348_);
v___x_2364_ = ((size_t)0ULL);
v___x_2365_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__2(v_sz_2363_, v___x_2364_, v_a_2348_);
v___x_2366_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__3);
v___x_2367_ = l_Lean_mkSepArray(v___x_2365_, v___x_2366_);
lean_dec_ref(v___x_2365_);
v___x_2368_ = l_Array_append___redArg(v___x_2361_, v___x_2367_);
lean_dec_ref(v___x_2367_);
v___x_2369_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2356_);
lean_ctor_set(v___x_2369_, 1, v___x_2360_);
lean_ctor_set(v___x_2369_, 2, v___x_2368_);
v___x_2370_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__2));
v___x_2371_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2356_);
lean_ctor_set(v___x_2371_, 1, v___x_2370_);
v___x_2372_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__4));
v___x_2373_ = l_Array_append___redArg(v___x_2361_, v_a_2350_);
lean_dec(v_a_2350_);
v___x_2374_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2356_);
lean_ctor_set(v___x_2374_, 1, v___x_2360_);
lean_ctor_set(v___x_2374_, 2, v___x_2373_);
v___x_2375_ = l_Lean_Syntax_node1(v___x_2356_, v___x_2372_, v___x_2374_);
lean_inc_ref(v___x_2362_);
v___x_2376_ = l_Lean_Syntax_node6(v___x_2356_, v___x_2358_, v___x_2359_, v___x_2362_, v___x_2362_, v___x_2369_, v___x_2371_, v___x_2375_);
if (v_isShared_2353_ == 0)
{
lean_ctor_set(v___x_2352_, 0, v___x_2376_);
v___x_2378_ = v___x_2352_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v___x_2376_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
else
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2388_; 
lean_dec(v_a_2348_);
v_a_2381_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___x_2349_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2349_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2386_; 
if (v_isShared_2384_ == 0)
{
v___x_2386_ = v___x_2383_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2381_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
else
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2396_; 
lean_dec_ref(v_levelInsts_2339_);
lean_dec(v_auxFunName_2338_);
lean_dec_ref(v_indVal_2337_);
lean_dec_ref(v_header_2336_);
v_a_2389_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2391_ = v___x_2347_;
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2347_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2394_; 
if (v_isShared_2392_ == 0)
{
v___x_2394_ = v___x_2391_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2389_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___boxed(lean_object* v_header_2397_, lean_object* v_indVal_2398_, lean_object* v_auxFunName_2399_, lean_object* v_levelInsts_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody(v_header_2397_, v_indVal_2398_, v_auxFunName_2399_, v_levelInsts_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_);
lean_dec(v_a_2406_);
lean_dec_ref(v_a_2405_);
lean_dec(v_a_2404_);
lean_dec_ref(v_a_2403_);
lean_dec(v_a_2402_);
lean_dec_ref(v_a_2401_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__0___redArg(lean_object* v_a_2409_, lean_object* v_b_2410_){
_start:
{
lean_object* v_array_2411_; lean_object* v_start_2412_; lean_object* v_stop_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2426_; 
v_array_2411_ = lean_ctor_get(v_a_2409_, 0);
v_start_2412_ = lean_ctor_get(v_a_2409_, 1);
v_stop_2413_ = lean_ctor_get(v_a_2409_, 2);
v_isSharedCheck_2426_ = !lean_is_exclusive(v_a_2409_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2415_ = v_a_2409_;
v_isShared_2416_ = v_isSharedCheck_2426_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_stop_2413_);
lean_inc(v_start_2412_);
lean_inc(v_array_2411_);
lean_dec(v_a_2409_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2426_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
uint8_t v___x_2417_; 
v___x_2417_ = lean_nat_dec_lt(v_start_2412_, v_stop_2413_);
if (v___x_2417_ == 0)
{
lean_del_object(v___x_2415_);
lean_dec(v_stop_2413_);
lean_dec(v_start_2412_);
lean_dec_ref(v_array_2411_);
return v_b_2410_;
}
else
{
lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2421_; 
v___x_2418_ = lean_unsigned_to_nat(1u);
v___x_2419_ = lean_nat_add(v_start_2412_, v___x_2418_);
lean_inc_ref(v_array_2411_);
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 1, v___x_2419_);
v___x_2421_ = v___x_2415_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_array_2411_);
lean_ctor_set(v_reuseFailAlloc_2425_, 1, v___x_2419_);
lean_ctor_set(v_reuseFailAlloc_2425_, 2, v_stop_2413_);
v___x_2421_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2422_ = lean_array_fget(v_array_2411_, v_start_2412_);
lean_dec(v_start_2412_);
lean_dec_ref(v_array_2411_);
v___x_2423_ = lean_array_push(v_b_2410_, v___x_2422_);
v_a_2409_ = v___x_2421_;
v_b_2410_ = v___x_2423_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__12(void){
_start:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2457_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__3));
v___x_2458_ = l_String_toRawSubstring_x27(v___x_2457_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1(lean_object* v_argNames_2534_, lean_object* v_levelInsts_2535_, lean_object* v_as_2536_, size_t v_sz_2537_, size_t v_i_2538_, lean_object* v_b_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_){
_start:
{
uint8_t v___x_2547_; 
v___x_2547_ = lean_usize_dec_lt(v_i_2538_, v_sz_2537_);
if (v___x_2547_ == 0)
{
lean_object* v___x_2548_; 
lean_dec_ref(v_argNames_2534_);
v___x_2548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2548_, 0, v_b_2539_);
return v___x_2548_;
}
else
{
lean_object* v_snd_2549_; lean_object* v_fst_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2723_; 
v_snd_2549_ = lean_ctor_get(v_b_2539_, 1);
v_fst_2550_ = lean_ctor_get(v_b_2539_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v_b_2539_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2552_ = v_b_2539_;
v_isShared_2553_ = v_isSharedCheck_2723_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_snd_2549_);
lean_inc(v_fst_2550_);
lean_dec(v_b_2539_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2723_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v_array_2554_; lean_object* v_start_2555_; lean_object* v_stop_2556_; uint8_t v___x_2557_; 
v_array_2554_ = lean_ctor_get(v_snd_2549_, 0);
v_start_2555_ = lean_ctor_get(v_snd_2549_, 1);
v_stop_2556_ = lean_ctor_get(v_snd_2549_, 2);
v___x_2557_ = lean_nat_dec_lt(v_start_2555_, v_stop_2556_);
if (v___x_2557_ == 0)
{
lean_object* v___x_2559_; 
lean_dec_ref(v_argNames_2534_);
if (v_isShared_2553_ == 0)
{
v___x_2559_ = v___x_2552_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_fst_2550_);
lean_ctor_set(v_reuseFailAlloc_2561_, 1, v_snd_2549_);
v___x_2559_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
lean_object* v___x_2560_; 
v___x_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2559_);
return v___x_2560_;
}
}
else
{
lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2719_; 
lean_inc(v_stop_2556_);
lean_inc(v_start_2555_);
lean_inc_ref(v_array_2554_);
v_isSharedCheck_2719_ = !lean_is_exclusive(v_snd_2549_);
if (v_isSharedCheck_2719_ == 0)
{
lean_object* v_unused_2720_; lean_object* v_unused_2721_; lean_object* v_unused_2722_; 
v_unused_2720_ = lean_ctor_get(v_snd_2549_, 2);
lean_dec(v_unused_2720_);
v_unused_2721_ = lean_ctor_get(v_snd_2549_, 1);
lean_dec(v_unused_2721_);
v_unused_2722_ = lean_ctor_get(v_snd_2549_, 0);
lean_dec(v_unused_2722_);
v___x_2563_ = v_snd_2549_;
v_isShared_2564_ = v_isSharedCheck_2719_;
goto v_resetjp_2562_;
}
else
{
lean_dec(v_snd_2549_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2719_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v_a_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2570_; 
v_a_2565_ = lean_array_uget_borrowed(v_as_2536_, v_i_2538_);
v___x_2566_ = lean_array_fget(v_array_2554_, v_start_2555_);
v___x_2567_ = lean_unsigned_to_nat(1u);
v___x_2568_ = lean_nat_add(v_start_2555_, v___x_2567_);
lean_dec(v_start_2555_);
if (v_isShared_2564_ == 0)
{
lean_ctor_set(v___x_2563_, 1, v___x_2568_);
v___x_2570_ = v___x_2563_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_array_2554_);
lean_ctor_set(v_reuseFailAlloc_2718_, 1, v___x_2568_);
lean_ctor_set(v_reuseFailAlloc_2718_, 2, v_stop_2556_);
v___x_2570_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
lean_object* v___x_2571_; 
lean_inc(v_a_2565_);
v___x_2571_ = l_Lean_Elab_Deriving_mkInductArgNames(v_a_2565_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v_a_2572_; lean_object* v_numParams_2573_; lean_object* v_lower_2575_; lean_object* v_upper_2576_; lean_object* v___x_2707_; lean_object* v___x_2708_; uint8_t v___x_2709_; 
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
lean_inc(v_a_2572_);
lean_dec_ref_known(v___x_2571_, 1);
v_numParams_2573_ = lean_ctor_get(v_a_2565_, 1);
v___x_2707_ = lean_unsigned_to_nat(0u);
v___x_2708_ = lean_array_get_size(v_a_2572_);
v___x_2709_ = lean_nat_dec_le(v_numParams_2573_, v___x_2707_);
if (v___x_2709_ == 0)
{
lean_inc(v_numParams_2573_);
v_lower_2575_ = v_numParams_2573_;
v_upper_2576_ = v___x_2708_;
goto v___jp_2574_;
}
else
{
v_lower_2575_ = v___x_2707_;
v_upper_2576_ = v___x_2708_;
goto v___jp_2574_;
}
v___jp_2574_:
{
lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___x_2577_ = l_Array_toSubarray___redArg(v_a_2572_, v_lower_2575_, v_upper_2576_);
lean_inc_ref(v___x_2577_);
v___x_2578_ = l_Subarray_copy___redArg(v___x_2577_);
v___x_2579_ = l_Lean_Elab_Deriving_mkImplicitBinders(v___x_2578_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_);
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v_a_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v_a_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
lean_inc(v_a_2580_);
lean_dec_ref_known(v___x_2579_, 1);
v___x_2581_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2573_);
lean_inc_ref(v_argNames_2534_);
v___x_2582_ = l_Array_toSubarray___redArg(v_argNames_2534_, v___x_2581_, v_numParams_2573_);
v___x_2583_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__0));
v___x_2584_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__0___redArg(v___x_2582_, v___x_2583_);
v___x_2585_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__0___redArg(v___x_2577_, v___x_2583_);
v_a_2586_ = l_Array_append___redArg(v___x_2584_, v___x_2585_);
lean_dec_ref(v___x_2585_);
v___x_2587_ = lean_array_get_size(v_a_2586_);
v___x_2588_ = l_Array_toSubarray___redArg(v_a_2586_, v___x_2581_, v___x_2587_);
v___x_2589_ = l_Subarray_copy___redArg(v___x_2588_);
lean_inc(v_a_2565_);
v___x_2590_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v_a_2565_, v___x_2589_, v___y_2544_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v_a_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; 
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
lean_inc(v_a_2591_);
lean_dec_ref_known(v___x_2590_, 1);
v___x_2592_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__2));
v___x_2593_ = l_Lean_Core_mkFreshUserName(v___x_2592_, v___y_2544_, v___y_2545_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; lean_object* v___x_2595_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_a_2594_);
lean_dec_ref_known(v___x_2593_, 1);
lean_inc_ref(v_argNames_2534_);
lean_inc(v_a_2565_);
v___x_2595_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr(v_a_2565_, v_argNames_2534_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_toCold_2596_; lean_object* v_a_2597_; lean_object* v_ref_2598_; lean_object* v_quotContext_2599_; lean_object* v_currMacroScope_2600_; uint8_t v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2670_; 
v_toCold_2596_ = lean_ctor_get(v___y_2544_, 0);
v_a_2597_ = lean_ctor_get(v___x_2595_, 0);
lean_inc(v_a_2597_);
lean_dec_ref_known(v___x_2595_, 1);
v_ref_2598_ = lean_ctor_get(v___y_2544_, 2);
v_quotContext_2599_ = lean_ctor_get(v_toCold_2596_, 8);
v_currMacroScope_2600_ = lean_ctor_get(v_toCold_2596_, 9);
v___x_2601_ = 0;
v___x_2602_ = l_Lean_SourceInfo_fromRef(v_ref_2598_, v___x_2601_);
v___x_2603_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__4));
v___x_2604_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__6));
v___x_2605_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__8));
v___x_2606_ = l_Lean_mkIdent(v_a_2594_);
lean_inc_n(v___x_2602_, 30);
v___x_2607_ = l_Lean_Syntax_node1(v___x_2602_, v___x_2605_, v___x_2606_);
v___x_2608_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_2609_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_2610_ = l_Array_append___redArg(v___x_2609_, v_a_2580_);
lean_dec(v_a_2580_);
v___x_2611_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2602_);
lean_ctor_set(v___x_2611_, 1, v___x_2608_);
lean_ctor_set(v___x_2611_, 2, v___x_2610_);
v___x_2612_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__10));
v___x_2613_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__11));
v___x_2614_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2602_);
lean_ctor_set(v___x_2614_, 1, v___x_2613_);
v___x_2615_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_2616_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__12);
v___x_2617_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__13));
lean_inc_n(v_currMacroScope_2600_, 3);
lean_inc_n(v_quotContext_2599_, 3);
v___x_2618_ = l_Lean_addMacroScope(v_quotContext_2599_, v___x_2617_, v_currMacroScope_2600_);
v___x_2619_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__26));
v___x_2620_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2602_);
lean_ctor_set(v___x_2620_, 1, v___x_2616_);
lean_ctor_set(v___x_2620_, 2, v___x_2618_);
lean_ctor_set(v___x_2620_, 3, v___x_2619_);
v___x_2621_ = l_Lean_Syntax_node1(v___x_2602_, v___x_2608_, v_a_2591_);
v___x_2622_ = l_Lean_Syntax_node2(v___x_2602_, v___x_2615_, v___x_2620_, v___x_2621_);
v___x_2623_ = l_Lean_Syntax_node2(v___x_2602_, v___x_2612_, v___x_2614_, v___x_2622_);
v___x_2624_ = l_Lean_Syntax_node1(v___x_2602_, v___x_2608_, v___x_2623_);
v___x_2625_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__27));
v___x_2626_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2602_);
lean_ctor_set(v___x_2626_, 1, v___x_2625_);
v___x_2627_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__29));
v___x_2628_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__30));
v___x_2629_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2602_);
lean_ctor_set(v___x_2629_, 1, v___x_2628_);
v___x_2630_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2602_);
lean_ctor_set(v___x_2630_, 1, v___x_2608_);
lean_ctor_set(v___x_2630_, 2, v___x_2609_);
v___x_2631_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__32));
v___x_2632_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__34));
v___x_2633_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__36));
v___x_2634_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1);
v___x_2635_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__2));
v___x_2636_ = l_Lean_addMacroScope(v_quotContext_2599_, v___x_2635_, v_currMacroScope_2600_);
v___x_2637_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__6));
v___x_2638_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2638_, 0, v___x_2602_);
lean_ctor_set(v___x_2638_, 1, v___x_2634_);
lean_ctor_set(v___x_2638_, 2, v___x_2636_);
lean_ctor_set(v___x_2638_, 3, v___x_2637_);
lean_inc_ref_n(v___x_2630_, 10);
v___x_2639_ = l_Lean_Syntax_node2(v___x_2602_, v___x_2633_, v___x_2638_, v___x_2630_);
v___x_2640_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__38));
v___x_2641_ = l_Lean_mkIdent(v___x_2566_);
v___x_2642_ = l_Array_append___redArg(v___x_2609_, v_levelInsts_2535_);
v___x_2643_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2643_, 0, v___x_2602_);
lean_ctor_set(v___x_2643_, 1, v___x_2608_);
lean_ctor_set(v___x_2643_, 2, v___x_2642_);
v___x_2644_ = l_Lean_Syntax_node2(v___x_2602_, v___x_2615_, v___x_2641_, v___x_2643_);
lean_inc_ref_n(v___x_2626_, 2);
v___x_2645_ = l_Lean_Syntax_node3(v___x_2602_, v___x_2640_, v___x_2626_, v___x_2630_, v___x_2644_);
v___x_2646_ = l_Lean_Syntax_node3(v___x_2602_, v___x_2608_, v___x_2630_, v___x_2630_, v___x_2645_);
v___x_2647_ = l_Lean_Syntax_node2(v___x_2602_, v___x_2632_, v___x_2639_, v___x_2646_);
v___x_2648_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__9));
v___x_2649_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2602_);
lean_ctor_set(v___x_2649_, 1, v___x_2648_);
v___x_2650_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8);
v___x_2651_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__9));
v___x_2652_ = l_Lean_addMacroScope(v_quotContext_2599_, v___x_2651_, v_currMacroScope_2600_);
v___x_2653_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__12));
v___x_2654_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2602_);
lean_ctor_set(v___x_2654_, 1, v___x_2650_);
lean_ctor_set(v___x_2654_, 2, v___x_2652_);
lean_ctor_set(v___x_2654_, 3, v___x_2653_);
v___x_2655_ = l_Lean_Syntax_node2(v___x_2602_, v___x_2633_, v___x_2654_, v___x_2630_);
v___x_2656_ = l_Lean_Syntax_node3(v___x_2602_, v___x_2640_, v___x_2626_, v___x_2630_, v_a_2597_);
v___x_2657_ = l_Lean_Syntax_node3(v___x_2602_, v___x_2608_, v___x_2630_, v___x_2630_, v___x_2656_);
v___x_2658_ = l_Lean_Syntax_node2(v___x_2602_, v___x_2632_, v___x_2655_, v___x_2657_);
v___x_2659_ = l_Lean_Syntax_node3(v___x_2602_, v___x_2608_, v___x_2647_, v___x_2649_, v___x_2658_);
v___x_2660_ = l_Lean_Syntax_node1(v___x_2602_, v___x_2631_, v___x_2659_);
v___x_2661_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__40));
v___x_2662_ = l_Lean_Syntax_node1(v___x_2602_, v___x_2661_, v___x_2630_);
v___x_2663_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__10));
v___x_2664_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2664_, 0, v___x_2602_);
lean_ctor_set(v___x_2664_, 1, v___x_2663_);
v___x_2665_ = l_Lean_Syntax_node6(v___x_2602_, v___x_2627_, v___x_2629_, v___x_2630_, v___x_2660_, v___x_2662_, v___x_2630_, v___x_2664_);
v___x_2666_ = l_Lean_Syntax_node5(v___x_2602_, v___x_2604_, v___x_2607_, v___x_2611_, v___x_2624_, v___x_2626_, v___x_2665_);
v___x_2667_ = l_Lean_Syntax_node1(v___x_2602_, v___x_2603_, v___x_2666_);
v___x_2668_ = lean_array_push(v_fst_2550_, v___x_2667_);
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 1, v___x_2570_);
lean_ctor_set(v___x_2552_, 0, v___x_2668_);
v___x_2670_ = v___x_2552_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v___x_2668_);
lean_ctor_set(v_reuseFailAlloc_2674_, 1, v___x_2570_);
v___x_2670_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
size_t v___x_2671_; size_t v___x_2672_; 
v___x_2671_ = ((size_t)1ULL);
v___x_2672_ = lean_usize_add(v_i_2538_, v___x_2671_);
v_i_2538_ = v___x_2672_;
v_b_2539_ = v___x_2670_;
goto _start;
}
}
else
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
lean_dec(v_a_2594_);
lean_dec(v_a_2591_);
lean_dec(v_a_2580_);
lean_dec_ref(v___x_2570_);
lean_dec(v___x_2566_);
lean_del_object(v___x_2552_);
lean_dec(v_fst_2550_);
lean_dec_ref(v_argNames_2534_);
v_a_2675_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v___x_2595_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2595_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2675_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
}
else
{
lean_object* v_a_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2690_; 
lean_dec(v_a_2591_);
lean_dec(v_a_2580_);
lean_dec_ref(v___x_2570_);
lean_dec(v___x_2566_);
lean_del_object(v___x_2552_);
lean_dec(v_fst_2550_);
lean_dec_ref(v_argNames_2534_);
v_a_2683_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2685_ = v___x_2593_;
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_a_2683_);
lean_dec(v___x_2593_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v___x_2688_; 
if (v_isShared_2686_ == 0)
{
v___x_2688_ = v___x_2685_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v_a_2683_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
}
}
else
{
lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2698_; 
lean_dec(v_a_2580_);
lean_dec_ref(v___x_2570_);
lean_dec(v___x_2566_);
lean_del_object(v___x_2552_);
lean_dec(v_fst_2550_);
lean_dec_ref(v_argNames_2534_);
v_a_2691_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2693_ = v___x_2590_;
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_dec(v___x_2590_);
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
lean_dec_ref(v___x_2577_);
lean_dec_ref(v___x_2570_);
lean_dec(v___x_2566_);
lean_del_object(v___x_2552_);
lean_dec(v_fst_2550_);
lean_dec_ref(v_argNames_2534_);
v_a_2699_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2701_ = v___x_2579_;
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_a_2699_);
lean_dec(v___x_2579_);
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
else
{
lean_object* v_a_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2717_; 
lean_dec_ref(v___x_2570_);
lean_dec(v___x_2566_);
lean_del_object(v___x_2552_);
lean_dec(v_fst_2550_);
lean_dec_ref(v_argNames_2534_);
v_a_2710_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2712_ = v___x_2571_;
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_a_2710_);
lean_dec(v___x_2571_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2715_; 
if (v_isShared_2713_ == 0)
{
v___x_2715_ = v___x_2712_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_a_2710_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___boxed(lean_object* v_argNames_2724_, lean_object* v_levelInsts_2725_, lean_object* v_as_2726_, lean_object* v_sz_2727_, lean_object* v_i_2728_, lean_object* v_b_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
size_t v_sz_boxed_2737_; size_t v_i_boxed_2738_; lean_object* v_res_2739_; 
v_sz_boxed_2737_ = lean_unbox_usize(v_sz_2727_);
lean_dec(v_sz_2727_);
v_i_boxed_2738_ = lean_unbox_usize(v_i_2728_);
lean_dec(v_i_2728_);
v_res_2739_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1(v_argNames_2724_, v_levelInsts_2725_, v_as_2726_, v_sz_boxed_2737_, v_i_boxed_2738_, v_b_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec_ref(v_as_2726_);
lean_dec_ref(v_levelInsts_2725_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls(lean_object* v_ctx_2740_, lean_object* v_argNames_2741_, lean_object* v_levelInsts_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_){
_start:
{
lean_object* v_typeInfos_2750_; lean_object* v_auxFunNames_2751_; lean_object* v___x_2752_; lean_object* v_letDecls_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; size_t v_sz_2757_; size_t v___x_2758_; lean_object* v___x_2759_; 
v_typeInfos_2750_ = lean_ctor_get(v_ctx_2740_, 1);
lean_inc_ref(v_typeInfos_2750_);
v_auxFunNames_2751_ = lean_ctor_get(v_ctx_2740_, 2);
lean_inc_ref(v_auxFunNames_2751_);
lean_dec_ref(v_ctx_2740_);
v___x_2752_ = lean_unsigned_to_nat(0u);
v_letDecls_2753_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__0));
v___x_2754_ = lean_array_get_size(v_auxFunNames_2751_);
v___x_2755_ = l_Array_toSubarray___redArg(v_auxFunNames_2751_, v___x_2752_, v___x_2754_);
v___x_2756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2756_, 0, v_letDecls_2753_);
lean_ctor_set(v___x_2756_, 1, v___x_2755_);
v_sz_2757_ = lean_array_size(v_typeInfos_2750_);
v___x_2758_ = ((size_t)0ULL);
v___x_2759_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1(v_argNames_2741_, v_levelInsts_2742_, v_typeInfos_2750_, v_sz_2757_, v___x_2758_, v___x_2756_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_);
lean_dec_ref(v_typeInfos_2750_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2768_; 
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2762_ = v___x_2759_;
v_isShared_2763_ = v_isSharedCheck_2768_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2759_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2768_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v_fst_2764_; lean_object* v___x_2766_; 
v_fst_2764_ = lean_ctor_get(v_a_2760_, 0);
lean_inc(v_fst_2764_);
lean_dec(v_a_2760_);
if (v_isShared_2763_ == 0)
{
lean_ctor_set(v___x_2762_, 0, v_fst_2764_);
v___x_2766_ = v___x_2762_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_fst_2764_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
else
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2776_; 
v_a_2769_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2771_ = v___x_2759_;
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v___x_2759_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2774_; 
if (v_isShared_2772_ == 0)
{
v___x_2774_ = v___x_2771_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_a_2769_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls___boxed(lean_object* v_ctx_2777_, lean_object* v_argNames_2778_, lean_object* v_levelInsts_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_){
_start:
{
lean_object* v_res_2787_; 
v_res_2787_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls(v_ctx_2777_, v_argNames_2778_, v_levelInsts_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_);
lean_dec(v_a_2785_);
lean_dec_ref(v_a_2784_);
lean_dec(v_a_2783_);
lean_dec_ref(v_a_2782_);
lean_dec(v_a_2781_);
lean_dec_ref(v_a_2780_);
lean_dec_ref(v_levelInsts_2779_);
return v_res_2787_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__0(lean_object* v_inst_2788_, lean_object* v_R_2789_, lean_object* v_a_2790_, lean_object* v_b_2791_){
_start:
{
lean_object* v___x_2792_; 
v___x_2792_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__0___redArg(v_a_2790_, v_b_2791_);
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__2(size_t v_sz_2793_, size_t v_i_2794_, lean_object* v_bs_2795_){
_start:
{
uint8_t v___x_2796_; 
v___x_2796_ = lean_usize_dec_lt(v_i_2794_, v_sz_2793_);
if (v___x_2796_ == 0)
{
return v_bs_2795_;
}
else
{
lean_object* v_v_2797_; lean_object* v___x_2798_; lean_object* v_bs_x27_2799_; size_t v___x_2800_; size_t v___x_2801_; lean_object* v___x_2802_; 
v_v_2797_ = lean_array_uget(v_bs_2795_, v_i_2794_);
v___x_2798_ = lean_unsigned_to_nat(0u);
v_bs_x27_2799_ = lean_array_uset(v_bs_2795_, v_i_2794_, v___x_2798_);
v___x_2800_ = ((size_t)1ULL);
v___x_2801_ = lean_usize_add(v_i_2794_, v___x_2800_);
v___x_2802_ = lean_array_uset(v_bs_x27_2799_, v_i_2794_, v_v_2797_);
v_i_2794_ = v___x_2801_;
v_bs_2795_ = v___x_2802_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__2___boxed(lean_object* v_sz_2804_, lean_object* v_i_2805_, lean_object* v_bs_2806_){
_start:
{
size_t v_sz_boxed_2807_; size_t v_i_boxed_2808_; lean_object* v_res_2809_; 
v_sz_boxed_2807_ = lean_unbox_usize(v_sz_2804_);
lean_dec(v_sz_2804_);
v_i_boxed_2808_ = lean_unbox_usize(v_i_2805_);
lean_dec(v_i_2805_);
v_res_2809_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__2(v_sz_boxed_2807_, v_i_boxed_2808_, v_bs_2806_);
return v_res_2809_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2820_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__4));
v___x_2821_ = l_String_toRawSubstring_x27(v___x_2820_);
return v___x_2821_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg(size_t v_sz_2842_, size_t v_i_2843_, lean_object* v_bs_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_){
_start:
{
uint8_t v___x_2848_; 
v___x_2848_ = lean_usize_dec_lt(v_i_2843_, v_sz_2842_);
if (v___x_2848_ == 0)
{
lean_object* v___x_2849_; 
v___x_2849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2849_, 0, v_bs_2844_);
return v___x_2849_;
}
else
{
lean_object* v_v_2850_; lean_object* v___x_2851_; lean_object* v_bs_x27_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; 
v_v_2850_ = lean_array_uget(v_bs_2844_, v_i_2843_);
v___x_2851_ = lean_unsigned_to_nat(0u);
v_bs_x27_2852_ = lean_array_uset(v_bs_2844_, v_i_2843_, v___x_2851_);
v___x_2853_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__1));
v___x_2854_ = l_Lean_Core_mkFreshUserName(v___x_2853_, v___y_2845_, v___y_2846_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_toCold_2855_; lean_object* v_a_2856_; lean_object* v_ref_2857_; lean_object* v_quotContext_2858_; lean_object* v_currMacroScope_2859_; lean_object* v___x_2860_; uint8_t v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; size_t v___x_2890_; size_t v___x_2891_; lean_object* v___x_2892_; 
v_toCold_2855_ = lean_ctor_get(v___y_2845_, 0);
v_a_2856_ = lean_ctor_get(v___x_2854_, 0);
lean_inc(v_a_2856_);
lean_dec_ref_known(v___x_2854_, 1);
v_ref_2857_ = lean_ctor_get(v___y_2845_, 2);
v_quotContext_2858_ = lean_ctor_get(v_toCold_2855_, 8);
v_currMacroScope_2859_ = lean_ctor_get(v_toCold_2855_, 9);
v___x_2860_ = l_Lean_mkIdent(v_a_2856_);
v___x_2861_ = 0;
v___x_2862_ = l_Lean_SourceInfo_fromRef(v_ref_2857_, v___x_2861_);
v___x_2863_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__3));
v___x_2864_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__4));
lean_inc_n(v___x_2862_, 11);
v___x_2865_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2862_);
lean_ctor_set(v___x_2865_, 1, v___x_2864_);
v___x_2866_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
lean_inc(v___x_2860_);
v___x_2867_ = l_Lean_Syntax_node1(v___x_2862_, v___x_2866_, v___x_2860_);
v___x_2868_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__11));
v___x_2869_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2862_);
lean_ctor_set(v___x_2869_, 1, v___x_2868_);
v___x_2870_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__6));
v___x_2871_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__5);
v___x_2872_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__6));
lean_inc(v_currMacroScope_2859_);
lean_inc(v_quotContext_2858_);
v___x_2873_ = l_Lean_addMacroScope(v_quotContext_2858_, v___x_2872_, v_currMacroScope_2859_);
v___x_2874_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__12));
v___x_2875_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2862_);
lean_ctor_set(v___x_2875_, 1, v___x_2871_);
lean_ctor_set(v___x_2875_, 2, v___x_2873_);
lean_ctor_set(v___x_2875_, 3, v___x_2874_);
v___x_2876_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__7));
v___x_2877_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2862_);
lean_ctor_set(v___x_2877_, 1, v___x_2876_);
v___x_2878_ = l_Lean_mkIdent(v_v_2850_);
v___x_2879_ = l_Lean_Syntax_node1(v___x_2862_, v___x_2866_, v___x_2878_);
v___x_2880_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__10));
v___x_2881_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2862_);
lean_ctor_set(v___x_2881_, 1, v___x_2880_);
v___x_2882_ = l_Lean_Syntax_node4(v___x_2862_, v___x_2870_, v___x_2875_, v___x_2877_, v___x_2879_, v___x_2881_);
v___x_2883_ = l_Lean_Syntax_node2(v___x_2862_, v___x_2866_, v___x_2869_, v___x_2882_);
v___x_2884_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_2885_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2862_);
lean_ctor_set(v___x_2885_, 1, v___x_2866_);
lean_ctor_set(v___x_2885_, 2, v___x_2884_);
v___x_2886_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__13));
v___x_2887_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2862_);
lean_ctor_set(v___x_2887_, 1, v___x_2886_);
v___x_2888_ = l_Lean_Syntax_node5(v___x_2862_, v___x_2863_, v___x_2865_, v___x_2867_, v___x_2883_, v___x_2885_, v___x_2887_);
v___x_2889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2860_);
lean_ctor_set(v___x_2889_, 1, v___x_2888_);
v___x_2890_ = ((size_t)1ULL);
v___x_2891_ = lean_usize_add(v_i_2843_, v___x_2890_);
v___x_2892_ = lean_array_uset(v_bs_x27_2852_, v_i_2843_, v___x_2889_);
v_i_2843_ = v___x_2891_;
v_bs_2844_ = v___x_2892_;
goto _start;
}
else
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2901_; 
lean_dec_ref(v_bs_x27_2852_);
lean_dec(v_v_2850_);
v_a_2894_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2896_ = v___x_2854_;
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___x_2854_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2899_; 
if (v_isShared_2897_ == 0)
{
v___x_2899_ = v___x_2896_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2894_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___boxed(lean_object* v_sz_2902_, lean_object* v_i_2903_, lean_object* v_bs_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_){
_start:
{
size_t v_sz_boxed_2908_; size_t v_i_boxed_2909_; lean_object* v_res_2910_; 
v_sz_boxed_2908_ = lean_unbox_usize(v_sz_2902_);
lean_dec(v_sz_2902_);
v_i_boxed_2909_ = lean_unbox_usize(v_i_2903_);
lean_dec(v_i_2903_);
v_res_2910_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg(v_sz_boxed_2908_, v_i_boxed_2909_, v_bs_2904_, v___y_2905_, v___y_2906_);
lean_dec(v___y_2906_);
lean_dec_ref(v___y_2905_);
return v_res_2910_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__1(size_t v_sz_2911_, size_t v_i_2912_, lean_object* v_bs_2913_){
_start:
{
uint8_t v___x_2914_; 
v___x_2914_ = lean_usize_dec_lt(v_i_2912_, v_sz_2911_);
if (v___x_2914_ == 0)
{
return v_bs_2913_;
}
else
{
lean_object* v_v_2915_; lean_object* v___x_2916_; lean_object* v_bs_x27_2917_; size_t v___x_2918_; size_t v___x_2919_; lean_object* v___x_2920_; 
v_v_2915_ = lean_array_uget(v_bs_2913_, v_i_2912_);
v___x_2916_ = lean_unsigned_to_nat(0u);
v_bs_x27_2917_ = lean_array_uset(v_bs_2913_, v_i_2912_, v___x_2916_);
v___x_2918_ = ((size_t)1ULL);
v___x_2919_ = lean_usize_add(v_i_2912_, v___x_2918_);
v___x_2920_ = lean_array_uset(v_bs_x27_2917_, v_i_2912_, v_v_2915_);
v_i_2912_ = v___x_2919_;
v_bs_2913_ = v___x_2920_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__1___boxed(lean_object* v_sz_2922_, lean_object* v_i_2923_, lean_object* v_bs_2924_){
_start:
{
size_t v_sz_boxed_2925_; size_t v_i_boxed_2926_; lean_object* v_res_2927_; 
v_sz_boxed_2925_ = lean_unbox_usize(v_sz_2922_);
lean_dec(v_sz_2922_);
v_i_boxed_2926_ = lean_unbox_usize(v_i_2923_);
lean_dec(v_i_2923_);
v_res_2927_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__1(v_sz_boxed_2925_, v_i_boxed_2926_, v_bs_2924_);
return v_res_2927_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__7(void){
_start:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2935_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__7));
v___x_2936_ = l_String_toRawSubstring_x27(v___x_2935_);
return v___x_2936_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20(void){
_start:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2961_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__19));
v___x_2962_ = l_Lean_stringToMessageData(v___x_2961_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction(lean_object* v_ctx_2963_, lean_object* v_i_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_){
_start:
{
lean_object* v_typeInfos_2972_; lean_object* v_auxFunNames_2973_; uint8_t v_usePartial_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v_auxFunName_2977_; lean_object* v_indVal_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v_typeInfos_2972_ = lean_ctor_get(v_ctx_2963_, 1);
v_auxFunNames_2973_ = lean_ctor_get(v_ctx_2963_, 2);
v_usePartial_2974_ = lean_ctor_get_uint8(v_ctx_2963_, sizeof(void*)*3);
v___x_2975_ = lean_box(0);
v___x_2976_ = l_Lean_instInhabitedInductiveVal_default;
v_auxFunName_2977_ = lean_array_get(v___x_2975_, v_auxFunNames_2973_, v_i_2964_);
v_indVal_2978_ = lean_array_get(v___x_2976_, v_typeInfos_2972_, v_i_2964_);
v___x_2979_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0));
v___x_2980_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__14));
v___x_2981_ = lean_unsigned_to_nat(1u);
lean_inc(v_indVal_2978_);
v___x_2982_ = l_Lean_Elab_Deriving_mkHeader(v___x_2980_, v___x_2981_, v_indVal_2978_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_toConstantVal_2983_; lean_object* v_a_2984_; lean_object* v_levelParams_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_3224_; 
v_toConstantVal_2983_ = lean_ctor_get(v_indVal_2978_, 0);
lean_inc_ref(v_toConstantVal_2983_);
v_a_2984_ = lean_ctor_get(v___x_2982_, 0);
lean_inc(v_a_2984_);
lean_dec_ref_known(v___x_2982_, 1);
v_levelParams_2985_ = lean_ctor_get(v_toConstantVal_2983_, 1);
v_isSharedCheck_3224_ = !lean_is_exclusive(v_toConstantVal_2983_);
if (v_isSharedCheck_3224_ == 0)
{
lean_object* v_unused_3225_; lean_object* v_unused_3226_; 
v_unused_3225_ = lean_ctor_get(v_toConstantVal_2983_, 2);
lean_dec(v_unused_3225_);
v_unused_3226_ = lean_ctor_get(v_toConstantVal_2983_, 0);
lean_dec(v_unused_3226_);
v___x_2987_ = v_toConstantVal_2983_;
v_isShared_2988_ = v_isSharedCheck_3224_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_levelParams_2985_);
lean_dec(v_toConstantVal_2983_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_3224_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v___x_2989_; size_t v_sz_2990_; size_t v___x_2991_; lean_object* v___x_2992_; 
v___x_2989_ = lean_array_mk(v_levelParams_2985_);
v_sz_2990_ = lean_array_size(v___x_2989_);
v___x_2991_ = ((size_t)0ULL);
v___x_2992_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg(v_sz_2990_, v___x_2991_, v___x_2989_, v_a_2969_, v_a_2970_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_object* v_a_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3215_; 
v_a_2993_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_2995_ = v___x_2992_;
v_isShared_2996_ = v_isSharedCheck_3215_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_a_2993_);
lean_dec(v___x_2992_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3215_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2997_; lean_object* v_fst_2998_; lean_object* v_snd_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3214_; 
v___x_2997_ = l_Array_unzip___redArg(v_a_2993_);
lean_dec(v_a_2993_);
v_fst_2998_ = lean_ctor_get(v___x_2997_, 0);
v_snd_2999_ = lean_ctor_get(v___x_2997_, 1);
v_isSharedCheck_3214_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3001_ = v___x_2997_;
v_isShared_3002_ = v_isSharedCheck_3214_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_snd_2999_);
lean_inc(v_fst_2998_);
lean_dec(v___x_2997_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3214_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v_a_3009_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v_body_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; size_t v_sz_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; 
v_sz_3196_ = lean_array_size(v_fst_2998_);
v___x_3197_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__2(v_sz_3196_, v___x_2991_, v_fst_2998_);
lean_inc_ref(v___x_3197_);
lean_inc(v_auxFunName_2977_);
lean_inc(v_indVal_2978_);
lean_inc(v_a_2984_);
v___x_3198_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody(v_a_2984_, v_indVal_2978_, v_auxFunName_2977_, v___x_3197_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_);
if (lean_obj_tag(v___x_3198_) == 0)
{
if (v_usePartial_2974_ == 0)
{
lean_object* v_a_3199_; 
lean_dec_ref(v___x_3197_);
lean_dec_ref(v_ctx_2963_);
v_a_3199_ = lean_ctor_get(v___x_3198_, 0);
lean_inc(v_a_3199_);
lean_dec_ref_known(v___x_3198_, 1);
v_body_3144_ = v_a_3199_;
v___y_3145_ = v_a_2965_;
v___y_3146_ = v_a_2966_;
v___y_3147_ = v_a_2967_;
v___y_3148_ = v_a_2968_;
v___y_3149_ = v_a_2969_;
v___y_3150_ = v_a_2970_;
goto v___jp_3143_;
}
else
{
lean_object* v_a_3200_; lean_object* v_argNames_3201_; lean_object* v___x_3202_; 
v_a_3200_ = lean_ctor_get(v___x_3198_, 0);
lean_inc(v_a_3200_);
lean_dec_ref_known(v___x_3198_, 1);
v_argNames_3201_ = lean_ctor_get(v_a_2984_, 1);
lean_inc_ref(v_argNames_3201_);
v___x_3202_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls(v_ctx_2963_, v_argNames_3201_, v___x_3197_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_);
lean_dec_ref(v___x_3197_);
if (lean_obj_tag(v___x_3202_) == 0)
{
lean_object* v_a_3203_; lean_object* v___x_3204_; 
v_a_3203_ = lean_ctor_get(v___x_3202_, 0);
lean_inc(v_a_3203_);
lean_dec_ref_known(v___x_3202_, 1);
v___x_3204_ = l_Lean_Elab_Deriving_mkLet(v_a_3203_, v_a_3200_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_);
lean_dec(v_a_3203_);
if (lean_obj_tag(v___x_3204_) == 0)
{
lean_object* v_a_3205_; 
v_a_3205_ = lean_ctor_get(v___x_3204_, 0);
lean_inc(v_a_3205_);
lean_dec_ref_known(v___x_3204_, 1);
v_body_3144_ = v_a_3205_;
v___y_3145_ = v_a_2965_;
v___y_3146_ = v_a_2966_;
v___y_3147_ = v_a_2967_;
v___y_3148_ = v_a_2968_;
v___y_3149_ = v_a_2969_;
v___y_3150_ = v_a_2970_;
goto v___jp_3143_;
}
else
{
lean_del_object(v___x_3001_);
lean_dec(v_snd_2999_);
lean_del_object(v___x_2995_);
lean_del_object(v___x_2987_);
lean_dec(v_a_2984_);
lean_dec(v_indVal_2978_);
lean_dec(v_auxFunName_2977_);
return v___x_3204_;
}
}
else
{
lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3213_; 
lean_dec(v_a_3200_);
lean_del_object(v___x_3001_);
lean_dec(v_snd_2999_);
lean_del_object(v___x_2995_);
lean_del_object(v___x_2987_);
lean_dec(v_a_2984_);
lean_dec(v_indVal_2978_);
lean_dec(v_auxFunName_2977_);
v_a_3206_ = lean_ctor_get(v___x_3202_, 0);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_3202_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3208_ = v___x_3202_;
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_3202_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3211_; 
if (v_isShared_3209_ == 0)
{
v___x_3211_ = v___x_3208_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v_a_3206_);
v___x_3211_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
return v___x_3211_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3197_);
lean_del_object(v___x_3001_);
lean_dec(v_snd_2999_);
lean_del_object(v___x_2995_);
lean_del_object(v___x_2987_);
lean_dec(v_a_2984_);
lean_dec(v_indVal_2978_);
lean_dec(v_auxFunName_2977_);
lean_dec_ref(v_ctx_2963_);
return v___x_3198_;
}
v___jp_3003_:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; size_t v_sz_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3010_ = lean_array_pop(v___y_3006_);
v___x_3011_ = l_Array_append___redArg(v___x_3010_, v_snd_2999_);
lean_dec(v_snd_2999_);
v___x_3012_ = lean_mk_empty_array_with_capacity(v___x_2981_);
v___x_3013_ = lean_array_push(v___x_3012_, v_a_3009_);
v_sz_3014_ = lean_array_size(v___x_3013_);
v___x_3015_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__1(v_sz_3014_, v___x_2991_, v___x_3013_);
v___x_3016_ = l_Array_append___redArg(v___x_3011_, v___x_3015_);
lean_dec_ref(v___x_3015_);
if (v_usePartial_2974_ == 0)
{
lean_object* v_toCold_3017_; lean_object* v_ref_3018_; lean_object* v_quotContext_3019_; lean_object* v_currMacroScope_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3030_; 
v_toCold_3017_ = lean_ctor_get(v___y_3005_, 0);
v_ref_3018_ = lean_ctor_get(v___y_3005_, 2);
v_quotContext_3019_ = lean_ctor_get(v_toCold_3017_, 8);
v_currMacroScope_3020_ = lean_ctor_get(v_toCold_3017_, 9);
v___x_3021_ = l_Lean_SourceInfo_fromRef(v_ref_3018_, v_usePartial_2974_);
v___x_3022_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__0));
v___x_3023_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__1));
lean_inc_ref_n(v___y_3004_, 2);
v___x_3024_ = l_Lean_Name_mkStr4(v___x_2979_, v___y_3004_, v___x_3022_, v___x_3023_);
v___x_3025_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__2));
v___x_3026_ = l_Lean_Name_mkStr4(v___x_2979_, v___y_3004_, v___x_3022_, v___x_3025_);
v___x_3027_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_3028_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
lean_inc(v___x_3021_);
if (v_isShared_2988_ == 0)
{
lean_ctor_set_tag(v___x_2987_, 1);
lean_ctor_set(v___x_2987_, 2, v___x_3028_);
lean_ctor_set(v___x_2987_, 1, v___x_3027_);
lean_ctor_set(v___x_2987_, 0, v___x_3021_);
v___x_3030_ = v___x_2987_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v___x_3021_);
lean_ctor_set(v_reuseFailAlloc_3072_, 1, v___x_3027_);
lean_ctor_set(v_reuseFailAlloc_3072_, 2, v___x_3028_);
v___x_3030_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3036_; 
lean_inc_ref_n(v___x_3030_, 7);
lean_inc_n(v___x_3021_, 2);
v___x_3031_ = l_Lean_Syntax_node7(v___x_3021_, v___x_3026_, v___x_3030_, v___x_3030_, v___x_3030_, v___x_3030_, v___x_3030_, v___x_3030_, v___x_3030_);
v___x_3032_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__3));
lean_inc_ref(v___y_3004_);
v___x_3033_ = l_Lean_Name_mkStr4(v___x_2979_, v___y_3004_, v___x_3022_, v___x_3032_);
v___x_3034_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__4));
if (v_isShared_3002_ == 0)
{
lean_ctor_set_tag(v___x_3001_, 2);
lean_ctor_set(v___x_3001_, 1, v___x_3034_);
lean_ctor_set(v___x_3001_, 0, v___x_3021_);
v___x_3036_ = v___x_3001_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v___x_3021_);
lean_ctor_set(v_reuseFailAlloc_3071_, 1, v___x_3034_);
v___x_3036_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3069_; 
v___x_3037_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__5));
lean_inc_ref_n(v___y_3004_, 5);
v___x_3038_ = l_Lean_Name_mkStr4(v___x_2979_, v___y_3004_, v___x_3022_, v___x_3037_);
v___x_3039_ = l_Lean_mkIdent(v_auxFunName_2977_);
lean_inc_ref_n(v___x_3030_, 4);
lean_inc_n(v___x_3021_, 11);
v___x_3040_ = l_Lean_Syntax_node2(v___x_3021_, v___x_3038_, v___x_3039_, v___x_3030_);
v___x_3041_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__6));
v___x_3042_ = l_Lean_Name_mkStr4(v___x_2979_, v___y_3004_, v___x_3022_, v___x_3041_);
v___x_3043_ = l_Array_append___redArg(v___x_3028_, v___x_3016_);
lean_dec_ref(v___x_3016_);
v___x_3044_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3021_);
lean_ctor_set(v___x_3044_, 1, v___x_3027_);
lean_ctor_set(v___x_3044_, 2, v___x_3043_);
v___x_3045_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__9));
lean_inc_ref(v___y_3007_);
v___x_3046_ = l_Lean_Name_mkStr4(v___x_2979_, v___y_3004_, v___y_3007_, v___x_3045_);
v___x_3047_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__11));
v___x_3048_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3021_);
lean_ctor_set(v___x_3048_, 1, v___x_3047_);
v___x_3049_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__7, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__7_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__7);
v___x_3050_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__8));
lean_inc(v_currMacroScope_3020_);
lean_inc(v_quotContext_3019_);
v___x_3051_ = l_Lean_addMacroScope(v_quotContext_3019_, v___x_3050_, v_currMacroScope_3020_);
v___x_3052_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__14));
v___x_3053_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3021_);
lean_ctor_set(v___x_3053_, 1, v___x_3049_);
lean_ctor_set(v___x_3053_, 2, v___x_3051_);
lean_ctor_set(v___x_3053_, 3, v___x_3052_);
v___x_3054_ = l_Lean_Syntax_node2(v___x_3021_, v___x_3046_, v___x_3048_, v___x_3053_);
v___x_3055_ = l_Lean_Syntax_node1(v___x_3021_, v___x_3027_, v___x_3054_);
v___x_3056_ = l_Lean_Syntax_node2(v___x_3021_, v___x_3042_, v___x_3044_, v___x_3055_);
v___x_3057_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__15));
v___x_3058_ = l_Lean_Name_mkStr4(v___x_2979_, v___y_3004_, v___x_3022_, v___x_3057_);
v___x_3059_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__27));
v___x_3060_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3060_, 0, v___x_3021_);
lean_ctor_set(v___x_3060_, 1, v___x_3059_);
v___x_3061_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__16));
v___x_3062_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__17));
v___x_3063_ = l_Lean_Name_mkStr4(v___x_2979_, v___y_3004_, v___x_3061_, v___x_3062_);
v___x_3064_ = l_Lean_Syntax_node2(v___x_3021_, v___x_3063_, v___x_3030_, v___x_3030_);
v___x_3065_ = l_Lean_Syntax_node4(v___x_3021_, v___x_3058_, v___x_3060_, v___y_3008_, v___x_3064_, v___x_3030_);
v___x_3066_ = l_Lean_Syntax_node5(v___x_3021_, v___x_3033_, v___x_3036_, v___x_3040_, v___x_3056_, v___x_3065_, v___x_3030_);
v___x_3067_ = l_Lean_Syntax_node2(v___x_3021_, v___x_3024_, v___x_3031_, v___x_3066_);
if (v_isShared_2996_ == 0)
{
lean_ctor_set(v___x_2995_, 0, v___x_3067_);
v___x_3069_ = v___x_2995_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v___x_3067_);
v___x_3069_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
return v___x_3069_;
}
}
}
}
else
{
lean_object* v_toCold_3073_; lean_object* v_ref_3074_; lean_object* v_quotContext_3075_; lean_object* v_currMacroScope_3076_; uint8_t v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3087_; 
v_toCold_3073_ = lean_ctor_get(v___y_3005_, 0);
v_ref_3074_ = lean_ctor_get(v___y_3005_, 2);
v_quotContext_3075_ = lean_ctor_get(v_toCold_3073_, 8);
v_currMacroScope_3076_ = lean_ctor_get(v_toCold_3073_, 9);
v___x_3077_ = 0;
v___x_3078_ = l_Lean_SourceInfo_fromRef(v_ref_3074_, v___x_3077_);
v___x_3079_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__0));
v___x_3080_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__1));
lean_inc_ref_n(v___y_3004_, 2);
v___x_3081_ = l_Lean_Name_mkStr4(v___x_2979_, v___y_3004_, v___x_3079_, v___x_3080_);
v___x_3082_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__2));
v___x_3083_ = l_Lean_Name_mkStr4(v___x_2979_, v___y_3004_, v___x_3079_, v___x_3082_);
v___x_3084_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_3085_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
lean_inc(v___x_3078_);
if (v_isShared_2988_ == 0)
{
lean_ctor_set_tag(v___x_2987_, 1);
lean_ctor_set(v___x_2987_, 2, v___x_3085_);
lean_ctor_set(v___x_2987_, 1, v___x_3084_);
lean_ctor_set(v___x_2987_, 0, v___x_3078_);
v___x_3087_ = v___x_2987_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v___x_3078_);
lean_ctor_set(v_reuseFailAlloc_3134_, 1, v___x_3084_);
lean_ctor_set(v_reuseFailAlloc_3134_, 2, v___x_3085_);
v___x_3087_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3091_; 
v___x_3088_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__18));
lean_inc_ref(v___y_3004_);
v___x_3089_ = l_Lean_Name_mkStr4(v___x_2979_, v___y_3004_, v___x_3079_, v___x_3088_);
lean_inc(v___x_3078_);
if (v_isShared_3002_ == 0)
{
lean_ctor_set_tag(v___x_3001_, 2);
lean_ctor_set(v___x_3001_, 1, v___x_3088_);
lean_ctor_set(v___x_3001_, 0, v___x_3078_);
v___x_3091_ = v___x_3001_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v___x_3078_);
lean_ctor_set(v_reuseFailAlloc_3133_, 1, v___x_3088_);
v___x_3091_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3131_; 
lean_inc_n(v___x_3078_, 15);
v___x_3092_ = l_Lean_Syntax_node1(v___x_3078_, v___x_3089_, v___x_3091_);
v___x_3093_ = l_Lean_Syntax_node1(v___x_3078_, v___x_3084_, v___x_3092_);
lean_inc_ref_n(v___x_3087_, 10);
v___x_3094_ = l_Lean_Syntax_node7(v___x_3078_, v___x_3083_, v___x_3087_, v___x_3087_, v___x_3087_, v___x_3087_, v___x_3087_, v___x_3087_, v___x_3093_);
v___x_3095_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__3));
lean_inc_ref_n(v___y_3004_, 6);
v___x_3096_ = l_Lean_Name_mkStr4(v___x_2979_, v___y_3004_, v___x_3079_, v___x_3095_);
v___x_3097_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__4));
v___x_3098_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3078_);
lean_ctor_set(v___x_3098_, 1, v___x_3097_);
v___x_3099_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__5));
v___x_3100_ = l_Lean_Name_mkStr4(v___x_2979_, v___y_3004_, v___x_3079_, v___x_3099_);
v___x_3101_ = l_Lean_mkIdent(v_auxFunName_2977_);
v___x_3102_ = l_Lean_Syntax_node2(v___x_3078_, v___x_3100_, v___x_3101_, v___x_3087_);
v___x_3103_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__6));
v___x_3104_ = l_Lean_Name_mkStr4(v___x_2979_, v___y_3004_, v___x_3079_, v___x_3103_);
v___x_3105_ = l_Array_append___redArg(v___x_3085_, v___x_3016_);
lean_dec_ref(v___x_3016_);
v___x_3106_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3078_);
lean_ctor_set(v___x_3106_, 1, v___x_3084_);
lean_ctor_set(v___x_3106_, 2, v___x_3105_);
v___x_3107_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__9));
lean_inc_ref(v___y_3007_);
v___x_3108_ = l_Lean_Name_mkStr4(v___x_2979_, v___y_3004_, v___y_3007_, v___x_3107_);
v___x_3109_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__11));
v___x_3110_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3110_, 0, v___x_3078_);
lean_ctor_set(v___x_3110_, 1, v___x_3109_);
v___x_3111_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__7, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__7_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__7);
v___x_3112_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__8));
lean_inc(v_currMacroScope_3076_);
lean_inc(v_quotContext_3075_);
v___x_3113_ = l_Lean_addMacroScope(v_quotContext_3075_, v___x_3112_, v_currMacroScope_3076_);
v___x_3114_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__14));
v___x_3115_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3078_);
lean_ctor_set(v___x_3115_, 1, v___x_3111_);
lean_ctor_set(v___x_3115_, 2, v___x_3113_);
lean_ctor_set(v___x_3115_, 3, v___x_3114_);
v___x_3116_ = l_Lean_Syntax_node2(v___x_3078_, v___x_3108_, v___x_3110_, v___x_3115_);
v___x_3117_ = l_Lean_Syntax_node1(v___x_3078_, v___x_3084_, v___x_3116_);
v___x_3118_ = l_Lean_Syntax_node2(v___x_3078_, v___x_3104_, v___x_3106_, v___x_3117_);
v___x_3119_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__15));
v___x_3120_ = l_Lean_Name_mkStr4(v___x_2979_, v___y_3004_, v___x_3079_, v___x_3119_);
v___x_3121_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__27));
v___x_3122_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3122_, 0, v___x_3078_);
lean_ctor_set(v___x_3122_, 1, v___x_3121_);
v___x_3123_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__16));
v___x_3124_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__17));
v___x_3125_ = l_Lean_Name_mkStr4(v___x_2979_, v___y_3004_, v___x_3123_, v___x_3124_);
v___x_3126_ = l_Lean_Syntax_node2(v___x_3078_, v___x_3125_, v___x_3087_, v___x_3087_);
v___x_3127_ = l_Lean_Syntax_node4(v___x_3078_, v___x_3120_, v___x_3122_, v___y_3008_, v___x_3126_, v___x_3087_);
v___x_3128_ = l_Lean_Syntax_node5(v___x_3078_, v___x_3096_, v___x_3098_, v___x_3102_, v___x_3118_, v___x_3127_, v___x_3087_);
v___x_3129_ = l_Lean_Syntax_node2(v___x_3078_, v___x_3081_, v___x_3094_, v___x_3128_);
if (v_isShared_2996_ == 0)
{
lean_ctor_set(v___x_2995_, 0, v___x_3129_);
v___x_3131_ = v___x_2995_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v___x_3129_);
v___x_3131_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
return v___x_3131_;
}
}
}
}
}
v___jp_3135_:
{
if (lean_obj_tag(v___y_3141_) == 0)
{
lean_object* v_a_3142_; 
v_a_3142_ = lean_ctor_get(v___y_3141_, 0);
lean_inc(v_a_3142_);
lean_dec_ref_known(v___y_3141_, 1);
v___y_3004_ = v___y_3136_;
v___y_3005_ = v___y_3137_;
v___y_3006_ = v___y_3138_;
v___y_3007_ = v___y_3139_;
v___y_3008_ = v___y_3140_;
v_a_3009_ = v_a_3142_;
goto v___jp_3003_;
}
else
{
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3138_);
lean_del_object(v___x_3001_);
lean_dec(v_snd_2999_);
lean_del_object(v___x_2995_);
lean_del_object(v___x_2987_);
lean_dec(v_auxFunName_2977_);
return v___y_3141_;
}
}
v___jp_3143_:
{
lean_object* v_binders_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; uint8_t v___x_3159_; 
v_binders_3151_ = lean_ctor_get(v_a_2984_, 0);
lean_inc_ref(v_binders_3151_);
lean_dec(v_a_2984_);
v___x_3152_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__1));
v___x_3153_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__2));
v___x_3154_ = lean_box(0);
v___x_3155_ = lean_array_get_size(v_binders_3151_);
v___x_3156_ = lean_nat_sub(v___x_3155_, v___x_2981_);
v___x_3157_ = lean_array_get_borrowed(v___x_3154_, v_binders_3151_, v___x_3156_);
lean_dec(v___x_3156_);
v___x_3158_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__3));
lean_inc(v___x_3157_);
v___x_3159_ = l_Lean_Syntax_isOfKind(v___x_3157_, v___x_3158_);
if (v___x_3159_ == 0)
{
lean_object* v___x_3160_; lean_object* v___x_3161_; 
lean_dec(v_indVal_2978_);
v___x_3160_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20);
v___x_3161_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v___x_3160_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
v___y_3136_ = v___x_3152_;
v___y_3137_ = v___y_3149_;
v___y_3138_ = v_binders_3151_;
v___y_3139_ = v___x_3153_;
v___y_3140_ = v_body_3144_;
v___y_3141_ = v___x_3161_;
goto v___jp_3135_;
}
else
{
lean_object* v___x_3162_; uint8_t v___x_3163_; 
v___x_3162_ = l_Lean_Syntax_getArg(v___x_3157_, v___x_2981_);
lean_inc(v___x_3162_);
v___x_3163_ = l_Lean_Syntax_matchesNull(v___x_3162_, v___x_2981_);
if (v___x_3163_ == 0)
{
lean_object* v___x_3164_; lean_object* v___x_3165_; 
lean_dec(v___x_3162_);
lean_dec(v_indVal_2978_);
v___x_3164_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20);
v___x_3165_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v___x_3164_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
v___y_3136_ = v___x_3152_;
v___y_3137_ = v___y_3149_;
v___y_3138_ = v_binders_3151_;
v___y_3139_ = v___x_3153_;
v___y_3140_ = v_body_3144_;
v___y_3141_ = v___x_3165_;
goto v___jp_3135_;
}
else
{
lean_object* v___x_3166_; lean_object* v___x_3167_; uint8_t v___x_3168_; 
v___x_3166_ = lean_unsigned_to_nat(2u);
v___x_3167_ = l_Lean_Syntax_getArg(v___x_3157_, v___x_3166_);
lean_inc(v___x_3167_);
v___x_3168_ = l_Lean_Syntax_matchesNull(v___x_3167_, v___x_3166_);
if (v___x_3168_ == 0)
{
lean_object* v___x_3169_; lean_object* v___x_3170_; 
lean_dec(v___x_3167_);
lean_dec(v___x_3162_);
lean_dec(v_indVal_2978_);
v___x_3169_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20);
v___x_3170_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v___x_3169_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
v___y_3136_ = v___x_3152_;
v___y_3137_ = v___y_3149_;
v___y_3138_ = v_binders_3151_;
v___y_3139_ = v___x_3153_;
v___y_3140_ = v_body_3144_;
v___y_3141_ = v___x_3170_;
goto v___jp_3135_;
}
else
{
lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; uint8_t v___x_3174_; 
v___x_3171_ = lean_unsigned_to_nat(0u);
v___x_3172_ = lean_unsigned_to_nat(3u);
v___x_3173_ = l_Lean_Syntax_getArg(v___x_3157_, v___x_3172_);
v___x_3174_ = l_Lean_Syntax_matchesNull(v___x_3173_, v___x_3171_);
if (v___x_3174_ == 0)
{
lean_object* v___x_3175_; lean_object* v___x_3176_; 
lean_dec(v___x_3167_);
lean_dec(v___x_3162_);
lean_dec(v_indVal_2978_);
v___x_3175_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20);
v___x_3176_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v___x_3175_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
v___y_3136_ = v___x_3152_;
v___y_3137_ = v___y_3149_;
v___y_3138_ = v_binders_3151_;
v___y_3139_ = v___x_3153_;
v___y_3140_ = v_body_3144_;
v___y_3141_ = v___x_3176_;
goto v___jp_3135_;
}
else
{
lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3177_ = l_Lean_Syntax_getArg(v___x_3162_, v___x_3171_);
lean_dec(v___x_3162_);
v___x_3178_ = l_Lean_Syntax_getArg(v___x_3167_, v___x_2981_);
lean_dec(v___x_3167_);
v___x_3179_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType(v_indVal_2978_, v___x_3178_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
if (lean_obj_tag(v___x_3179_) == 0)
{
lean_object* v_a_3180_; lean_object* v_ref_3181_; uint8_t v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; 
v_a_3180_ = lean_ctor_get(v___x_3179_, 0);
lean_inc(v_a_3180_);
lean_dec_ref_known(v___x_3179_, 1);
v_ref_3181_ = lean_ctor_get(v___y_3149_, 2);
v___x_3182_ = 0;
v___x_3183_ = l_Lean_SourceInfo_fromRef(v_ref_3181_, v___x_3182_);
v___x_3184_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__4));
lean_inc_n(v___x_3183_, 6);
v___x_3185_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3183_);
lean_ctor_set(v___x_3185_, 1, v___x_3184_);
v___x_3186_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_3187_ = l_Lean_Syntax_node1(v___x_3183_, v___x_3186_, v___x_3177_);
v___x_3188_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__11));
v___x_3189_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3189_, 0, v___x_3183_);
lean_ctor_set(v___x_3189_, 1, v___x_3188_);
v___x_3190_ = l_Lean_Syntax_node2(v___x_3183_, v___x_3186_, v___x_3189_, v_a_3180_);
v___x_3191_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_3192_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3183_);
lean_ctor_set(v___x_3192_, 1, v___x_3186_);
lean_ctor_set(v___x_3192_, 2, v___x_3191_);
v___x_3193_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__13));
v___x_3194_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3183_);
lean_ctor_set(v___x_3194_, 1, v___x_3193_);
v___x_3195_ = l_Lean_Syntax_node5(v___x_3183_, v___x_3158_, v___x_3185_, v___x_3187_, v___x_3190_, v___x_3192_, v___x_3194_);
v___y_3004_ = v___x_3152_;
v___y_3005_ = v___y_3149_;
v___y_3006_ = v_binders_3151_;
v___y_3007_ = v___x_3153_;
v___y_3008_ = v_body_3144_;
v_a_3009_ = v___x_3195_;
goto v___jp_3003_;
}
else
{
lean_dec(v___x_3177_);
v___y_3136_ = v___x_3152_;
v___y_3137_ = v___y_3149_;
v___y_3138_ = v_binders_3151_;
v___y_3139_ = v___x_3153_;
v___y_3140_ = v_body_3144_;
v___y_3141_ = v___x_3179_;
goto v___jp_3135_;
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
lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3223_; 
lean_del_object(v___x_2987_);
lean_dec(v_a_2984_);
lean_dec(v_indVal_2978_);
lean_dec(v_auxFunName_2977_);
lean_dec_ref(v_ctx_2963_);
v_a_3216_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3218_ = v___x_2992_;
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___x_2992_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3221_; 
if (v_isShared_3219_ == 0)
{
v___x_3221_ = v___x_3218_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3216_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
}
}
}
else
{
lean_object* v_a_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3234_; 
lean_dec(v_indVal_2978_);
lean_dec(v_auxFunName_2977_);
lean_dec_ref(v_ctx_2963_);
v_a_3227_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3229_ = v___x_2982_;
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_a_3227_);
lean_dec(v___x_2982_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___x_3232_; 
if (v_isShared_3230_ == 0)
{
v___x_3232_ = v___x_3229_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_a_3227_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___boxed(lean_object* v_ctx_3235_, lean_object* v_i_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_){
_start:
{
lean_object* v_res_3244_; 
v_res_3244_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction(v_ctx_3235_, v_i_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_);
lean_dec(v_a_3242_);
lean_dec_ref(v_a_3241_);
lean_dec(v_a_3240_);
lean_dec_ref(v_a_3239_);
lean_dec(v_a_3238_);
lean_dec_ref(v_a_3237_);
lean_dec(v_i_3236_);
return v_res_3244_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0(size_t v_sz_3245_, size_t v_i_3246_, lean_object* v_bs_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_){
_start:
{
lean_object* v___x_3255_; 
v___x_3255_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg(v_sz_3245_, v_i_3246_, v_bs_3247_, v___y_3252_, v___y_3253_);
return v___x_3255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___boxed(lean_object* v_sz_3256_, lean_object* v_i_3257_, lean_object* v_bs_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_){
_start:
{
size_t v_sz_boxed_3266_; size_t v_i_boxed_3267_; lean_object* v_res_3268_; 
v_sz_boxed_3266_ = lean_unbox_usize(v_sz_3256_);
lean_dec(v_sz_3256_);
v_i_boxed_3267_ = lean_unbox_usize(v_i_3257_);
lean_dec(v_i_3257_);
v_res_3268_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0(v_sz_boxed_3266_, v_i_boxed_3267_, v_bs_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_);
lean_dec(v___y_3264_);
lean_dec_ref(v___y_3263_);
lean_dec(v___y_3262_);
lean_dec_ref(v___y_3261_);
lean_dec(v___y_3260_);
lean_dec_ref(v___y_3259_);
return v_res_3268_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0___redArg(lean_object* v_upperBound_3269_, lean_object* v_ctx_3270_, lean_object* v_a_3271_, lean_object* v_b_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_){
_start:
{
uint8_t v___x_3280_; 
v___x_3280_ = lean_nat_dec_lt(v_a_3271_, v_upperBound_3269_);
if (v___x_3280_ == 0)
{
lean_object* v___x_3281_; 
lean_dec(v_a_3271_);
lean_dec_ref(v_ctx_3270_);
v___x_3281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3281_, 0, v_b_3272_);
return v___x_3281_;
}
else
{
lean_object* v___x_3282_; 
lean_inc_ref(v_ctx_3270_);
v___x_3282_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction(v_ctx_3270_, v_a_3271_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_);
if (lean_obj_tag(v___x_3282_) == 0)
{
lean_object* v_a_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v_a_3283_ = lean_ctor_get(v___x_3282_, 0);
lean_inc(v_a_3283_);
lean_dec_ref_known(v___x_3282_, 1);
v___x_3284_ = lean_array_push(v_b_3272_, v_a_3283_);
v___x_3285_ = lean_unsigned_to_nat(1u);
v___x_3286_ = lean_nat_add(v_a_3271_, v___x_3285_);
lean_dec(v_a_3271_);
v_a_3271_ = v___x_3286_;
v_b_3272_ = v___x_3284_;
goto _start;
}
else
{
lean_object* v_a_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3295_; 
lean_dec_ref(v_b_3272_);
lean_dec(v_a_3271_);
lean_dec_ref(v_ctx_3270_);
v_a_3288_ = lean_ctor_get(v___x_3282_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3282_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3290_ = v___x_3282_;
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_a_3288_);
lean_dec(v___x_3282_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v___x_3293_; 
if (v_isShared_3291_ == 0)
{
v___x_3293_ = v___x_3290_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_a_3288_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0___redArg___boxed(lean_object* v_upperBound_3296_, lean_object* v_ctx_3297_, lean_object* v_a_3298_, lean_object* v_b_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_){
_start:
{
lean_object* v_res_3307_; 
v_res_3307_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0___redArg(v_upperBound_3296_, v_ctx_3297_, v_a_3298_, v_b_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_);
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec_ref(v___y_3300_);
lean_dec(v_upperBound_3296_);
return v_res_3307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions(lean_object* v_ctx_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_){
_start:
{
lean_object* v_typeInfos_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v_auxDefs_3326_; lean_object* v___x_3327_; 
v_typeInfos_3323_ = lean_ctor_get(v_ctx_3315_, 1);
v___x_3324_ = lean_array_get_size(v_typeInfos_3323_);
v___x_3325_ = lean_unsigned_to_nat(0u);
v_auxDefs_3326_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__0));
v___x_3327_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0___redArg(v___x_3324_, v_ctx_3315_, v___x_3325_, v_auxDefs_3326_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_);
if (lean_obj_tag(v___x_3327_) == 0)
{
lean_object* v_a_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3348_; 
v_a_3328_ = lean_ctor_get(v___x_3327_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3327_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3330_ = v___x_3327_;
v_isShared_3331_ = v_isSharedCheck_3348_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_a_3328_);
lean_dec(v___x_3327_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3348_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v_ref_3332_; uint8_t v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3346_; 
v_ref_3332_ = lean_ctor_get(v_a_3320_, 2);
v___x_3333_ = 0;
v___x_3334_ = l_Lean_SourceInfo_fromRef(v_ref_3332_, v___x_3333_);
v___x_3335_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions___closed__0));
v___x_3336_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions___closed__1));
lean_inc_n(v___x_3334_, 3);
v___x_3337_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3334_);
lean_ctor_set(v___x_3337_, 1, v___x_3335_);
v___x_3338_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_3339_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_3340_ = l_Array_append___redArg(v___x_3339_, v_a_3328_);
lean_dec(v_a_3328_);
v___x_3341_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3334_);
lean_ctor_set(v___x_3341_, 1, v___x_3338_);
lean_ctor_set(v___x_3341_, 2, v___x_3340_);
v___x_3342_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions___closed__2));
v___x_3343_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3343_, 0, v___x_3334_);
lean_ctor_set(v___x_3343_, 1, v___x_3342_);
v___x_3344_ = l_Lean_Syntax_node3(v___x_3334_, v___x_3336_, v___x_3337_, v___x_3341_, v___x_3343_);
if (v_isShared_3331_ == 0)
{
lean_ctor_set(v___x_3330_, 0, v___x_3344_);
v___x_3346_ = v___x_3330_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v___x_3344_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
}
else
{
lean_object* v_a_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3356_; 
v_a_3349_ = lean_ctor_get(v___x_3327_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3327_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3351_ = v___x_3327_;
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_a_3349_);
lean_dec(v___x_3327_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v___x_3354_; 
if (v_isShared_3352_ == 0)
{
v___x_3354_ = v___x_3351_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_a_3349_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions___boxed(lean_object* v_ctx_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_){
_start:
{
lean_object* v_res_3365_; 
v_res_3365_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions(v_ctx_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_);
lean_dec(v_a_3363_);
lean_dec_ref(v_a_3362_);
lean_dec(v_a_3361_);
lean_dec_ref(v_a_3360_);
lean_dec(v_a_3359_);
lean_dec_ref(v_a_3358_);
return v_res_3365_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0(lean_object* v_upperBound_3366_, lean_object* v_ctx_3367_, lean_object* v_inst_3368_, lean_object* v_R_3369_, lean_object* v_a_3370_, lean_object* v_b_3371_, lean_object* v_c_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_){
_start:
{
lean_object* v___x_3380_; 
v___x_3380_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0___redArg(v_upperBound_3366_, v_ctx_3367_, v_a_3370_, v_b_3371_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_);
return v___x_3380_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0___boxed(lean_object* v_upperBound_3381_, lean_object* v_ctx_3382_, lean_object* v_inst_3383_, lean_object* v_R_3384_, lean_object* v_a_3385_, lean_object* v_b_3386_, lean_object* v_c_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_){
_start:
{
lean_object* v_res_3395_; 
v_res_3395_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0(v_upperBound_3381_, v_ctx_3382_, v_inst_3383_, v_R_3384_, v_a_3385_, v_b_3386_, v_c_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_);
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
lean_dec(v___y_3391_);
lean_dec_ref(v___y_3390_);
lean_dec(v___y_3389_);
lean_dec_ref(v___y_3388_);
lean_dec(v_upperBound_3381_);
return v_res_3395_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0_spec__0(lean_object* v_a_3396_, lean_object* v_as_3397_, size_t v_i_3398_, size_t v_stop_3399_){
_start:
{
uint8_t v___x_3400_; 
v___x_3400_ = lean_usize_dec_eq(v_i_3398_, v_stop_3399_);
if (v___x_3400_ == 0)
{
lean_object* v___x_3401_; uint8_t v___x_3402_; 
v___x_3401_ = lean_array_uget_borrowed(v_as_3397_, v_i_3398_);
v___x_3402_ = lean_name_eq(v_a_3396_, v___x_3401_);
if (v___x_3402_ == 0)
{
size_t v___x_3403_; size_t v___x_3404_; 
v___x_3403_ = ((size_t)1ULL);
v___x_3404_ = lean_usize_add(v_i_3398_, v___x_3403_);
v_i_3398_ = v___x_3404_;
goto _start;
}
else
{
return v___x_3402_;
}
}
else
{
uint8_t v___x_3406_; 
v___x_3406_ = 0;
return v___x_3406_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0_spec__0___boxed(lean_object* v_a_3407_, lean_object* v_as_3408_, lean_object* v_i_3409_, lean_object* v_stop_3410_){
_start:
{
size_t v_i_boxed_3411_; size_t v_stop_boxed_3412_; uint8_t v_res_3413_; lean_object* v_r_3414_; 
v_i_boxed_3411_ = lean_unbox_usize(v_i_3409_);
lean_dec(v_i_3409_);
v_stop_boxed_3412_ = lean_unbox_usize(v_stop_3410_);
lean_dec(v_stop_3410_);
v_res_3413_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0_spec__0(v_a_3407_, v_as_3408_, v_i_boxed_3411_, v_stop_boxed_3412_);
lean_dec_ref(v_as_3408_);
lean_dec(v_a_3407_);
v_r_3414_ = lean_box(v_res_3413_);
return v_r_3414_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0(lean_object* v_as_3415_, lean_object* v_a_3416_){
_start:
{
lean_object* v___x_3417_; lean_object* v___x_3418_; uint8_t v___x_3419_; 
v___x_3417_ = lean_unsigned_to_nat(0u);
v___x_3418_ = lean_array_get_size(v_as_3415_);
v___x_3419_ = lean_nat_dec_lt(v___x_3417_, v___x_3418_);
if (v___x_3419_ == 0)
{
return v___x_3419_;
}
else
{
if (v___x_3419_ == 0)
{
return v___x_3419_;
}
else
{
size_t v___x_3420_; size_t v___x_3421_; uint8_t v___x_3422_; 
v___x_3420_ = ((size_t)0ULL);
v___x_3421_ = lean_usize_of_nat(v___x_3418_);
v___x_3422_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0_spec__0(v_a_3416_, v_as_3415_, v___x_3420_, v___x_3421_);
return v___x_3422_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0___boxed(lean_object* v_as_3423_, lean_object* v_a_3424_){
_start:
{
uint8_t v_res_3425_; lean_object* v_r_3426_; 
v_res_3425_ = l_Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0(v_as_3423_, v_a_3424_);
lean_dec(v_a_3424_);
lean_dec_ref(v_as_3423_);
v_r_3426_ = lean_box(v_res_3425_);
return v_r_3426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg(size_t v_sz_3433_, size_t v_i_3434_, lean_object* v_bs_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_){
_start:
{
uint8_t v___x_3439_; 
v___x_3439_ = lean_usize_dec_lt(v_i_3434_, v_sz_3433_);
if (v___x_3439_ == 0)
{
lean_object* v___x_3440_; 
v___x_3440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3440_, 0, v_bs_3435_);
return v___x_3440_;
}
else
{
lean_object* v_v_3441_; lean_object* v___x_3442_; lean_object* v_bs_x27_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; 
v_v_3441_ = lean_array_uget(v_bs_3435_, v_i_3434_);
v___x_3442_ = lean_unsigned_to_nat(0u);
v_bs_x27_3443_ = lean_array_uset(v_bs_3435_, v_i_3434_, v___x_3442_);
v___x_3444_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__1));
v___x_3445_ = l_Lean_Core_mkFreshUserName(v___x_3444_, v___y_3436_, v___y_3437_);
if (lean_obj_tag(v___x_3445_) == 0)
{
lean_object* v_toCold_3446_; lean_object* v_a_3447_; lean_object* v_ref_3448_; lean_object* v_quotContext_3449_; lean_object* v_currMacroScope_3450_; lean_object* v___x_3451_; uint8_t v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; size_t v___x_3478_; size_t v___x_3479_; lean_object* v___x_3480_; 
v_toCold_3446_ = lean_ctor_get(v___y_3436_, 0);
v_a_3447_ = lean_ctor_get(v___x_3445_, 0);
lean_inc(v_a_3447_);
lean_dec_ref_known(v___x_3445_, 1);
v_ref_3448_ = lean_ctor_get(v___y_3436_, 2);
v_quotContext_3449_ = lean_ctor_get(v_toCold_3446_, 8);
v_currMacroScope_3450_ = lean_ctor_get(v_toCold_3446_, 9);
v___x_3451_ = l_Lean_mkIdent(v_a_3447_);
v___x_3452_ = 0;
v___x_3453_ = l_Lean_SourceInfo_fromRef(v_ref_3448_, v___x_3452_);
v___x_3454_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg___closed__1));
v___x_3455_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__13));
lean_inc_n(v___x_3453_, 9);
v___x_3456_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3456_, 0, v___x_3453_);
lean_ctor_set(v___x_3456_, 1, v___x_3455_);
v___x_3457_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_3458_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__11));
v___x_3459_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3459_, 0, v___x_3453_);
lean_ctor_set(v___x_3459_, 1, v___x_3458_);
lean_inc(v___x_3451_);
v___x_3460_ = l_Lean_Syntax_node2(v___x_3453_, v___x_3457_, v___x_3451_, v___x_3459_);
v___x_3461_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__6));
v___x_3462_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__5);
v___x_3463_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__6));
lean_inc(v_currMacroScope_3450_);
lean_inc(v_quotContext_3449_);
v___x_3464_ = l_Lean_addMacroScope(v_quotContext_3449_, v___x_3463_, v_currMacroScope_3450_);
v___x_3465_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__12));
v___x_3466_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3453_);
lean_ctor_set(v___x_3466_, 1, v___x_3462_);
lean_ctor_set(v___x_3466_, 2, v___x_3464_);
lean_ctor_set(v___x_3466_, 3, v___x_3465_);
v___x_3467_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__7));
v___x_3468_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3453_);
lean_ctor_set(v___x_3468_, 1, v___x_3467_);
v___x_3469_ = l_Lean_mkIdent(v_v_3441_);
v___x_3470_ = l_Lean_Syntax_node1(v___x_3453_, v___x_3457_, v___x_3469_);
v___x_3471_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__10));
v___x_3472_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3472_, 0, v___x_3453_);
lean_ctor_set(v___x_3472_, 1, v___x_3471_);
v___x_3473_ = l_Lean_Syntax_node4(v___x_3453_, v___x_3461_, v___x_3466_, v___x_3468_, v___x_3470_, v___x_3472_);
v___x_3474_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__14));
v___x_3475_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3453_);
lean_ctor_set(v___x_3475_, 1, v___x_3474_);
v___x_3476_ = l_Lean_Syntax_node4(v___x_3453_, v___x_3454_, v___x_3456_, v___x_3460_, v___x_3473_, v___x_3475_);
v___x_3477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3477_, 0, v___x_3451_);
lean_ctor_set(v___x_3477_, 1, v___x_3476_);
v___x_3478_ = ((size_t)1ULL);
v___x_3479_ = lean_usize_add(v_i_3434_, v___x_3478_);
v___x_3480_ = lean_array_uset(v_bs_x27_3443_, v_i_3434_, v___x_3477_);
v_i_3434_ = v___x_3479_;
v_bs_3435_ = v___x_3480_;
goto _start;
}
else
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3489_; 
lean_dec_ref(v_bs_x27_3443_);
lean_dec(v_v_3441_);
v_a_3482_ = lean_ctor_get(v___x_3445_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3445_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3484_ = v___x_3445_;
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3445_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3487_; 
if (v_isShared_3485_ == 0)
{
v___x_3487_ = v___x_3484_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v_a_3482_);
v___x_3487_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
return v___x_3487_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg___boxed(lean_object* v_sz_3490_, lean_object* v_i_3491_, lean_object* v_bs_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_){
_start:
{
size_t v_sz_boxed_3496_; size_t v_i_boxed_3497_; lean_object* v_res_3498_; 
v_sz_boxed_3496_ = lean_unbox_usize(v_sz_3490_);
lean_dec(v_sz_3490_);
v_i_boxed_3497_ = lean_unbox_usize(v_i_3491_);
lean_dec(v_i_3491_);
v_res_3498_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg(v_sz_boxed_3496_, v_i_boxed_3497_, v_bs_3492_, v___y_3493_, v___y_3494_);
lean_dec(v___y_3494_);
lean_dec_ref(v___y_3493_);
return v_res_3498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__2(size_t v_sz_3499_, size_t v_i_3500_, lean_object* v_bs_3501_){
_start:
{
uint8_t v___x_3502_; 
v___x_3502_ = lean_usize_dec_lt(v_i_3500_, v_sz_3499_);
if (v___x_3502_ == 0)
{
return v_bs_3501_;
}
else
{
lean_object* v_v_3503_; lean_object* v___x_3504_; lean_object* v_bs_x27_3505_; size_t v___x_3506_; size_t v___x_3507_; lean_object* v___x_3508_; 
v_v_3503_ = lean_array_uget(v_bs_3501_, v_i_3500_);
v___x_3504_ = lean_unsigned_to_nat(0u);
v_bs_x27_3505_ = lean_array_uset(v_bs_3501_, v_i_3500_, v___x_3504_);
v___x_3506_ = ((size_t)1ULL);
v___x_3507_ = lean_usize_add(v_i_3500_, v___x_3506_);
v___x_3508_ = lean_array_uset(v_bs_x27_3505_, v_i_3500_, v_v_3503_);
v_i_3500_ = v___x_3507_;
v_bs_3501_ = v___x_3508_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__2___boxed(lean_object* v_sz_3510_, lean_object* v_i_3511_, lean_object* v_bs_3512_){
_start:
{
size_t v_sz_boxed_3513_; size_t v_i_boxed_3514_; lean_object* v_res_3515_; 
v_sz_boxed_3513_ = lean_unbox_usize(v_sz_3510_);
lean_dec(v_sz_3510_);
v_i_boxed_3514_ = lean_unbox_usize(v_i_3511_);
lean_dec(v_i_3511_);
v_res_3515_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__2(v_sz_boxed_3513_, v_i_boxed_3514_, v_bs_3512_);
return v_res_3515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3(lean_object* v_typeNames_3556_, lean_object* v_as_3557_, size_t v_sz_3558_, size_t v_i_3559_, lean_object* v_b_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_){
_start:
{
lean_object* v_a_3569_; uint8_t v___x_3573_; 
v___x_3573_ = lean_usize_dec_lt(v_i_3559_, v_sz_3558_);
if (v___x_3573_ == 0)
{
lean_object* v___x_3574_; 
v___x_3574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3574_, 0, v_b_3560_);
return v___x_3574_;
}
else
{
lean_object* v_snd_3575_; lean_object* v_fst_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3788_; 
v_snd_3575_ = lean_ctor_get(v_b_3560_, 1);
v_fst_3576_ = lean_ctor_get(v_b_3560_, 0);
v_isSharedCheck_3788_ = !lean_is_exclusive(v_b_3560_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3578_ = v_b_3560_;
v_isShared_3579_ = v_isSharedCheck_3788_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_snd_3575_);
lean_inc(v_fst_3576_);
lean_dec(v_b_3560_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3788_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v_array_3580_; lean_object* v_start_3581_; lean_object* v_stop_3582_; uint8_t v___x_3583_; 
v_array_3580_ = lean_ctor_get(v_snd_3575_, 0);
v_start_3581_ = lean_ctor_get(v_snd_3575_, 1);
v_stop_3582_ = lean_ctor_get(v_snd_3575_, 2);
v___x_3583_ = lean_nat_dec_lt(v_start_3581_, v_stop_3582_);
if (v___x_3583_ == 0)
{
lean_object* v___x_3585_; 
if (v_isShared_3579_ == 0)
{
v___x_3585_ = v___x_3578_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v_fst_3576_);
lean_ctor_set(v_reuseFailAlloc_3587_, 1, v_snd_3575_);
v___x_3585_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
lean_object* v___x_3586_; 
v___x_3586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3586_, 0, v___x_3585_);
return v___x_3586_;
}
}
else
{
lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3784_; 
lean_inc(v_stop_3582_);
lean_inc(v_start_3581_);
lean_inc_ref(v_array_3580_);
v_isSharedCheck_3784_ = !lean_is_exclusive(v_snd_3575_);
if (v_isSharedCheck_3784_ == 0)
{
lean_object* v_unused_3785_; lean_object* v_unused_3786_; lean_object* v_unused_3787_; 
v_unused_3785_ = lean_ctor_get(v_snd_3575_, 2);
lean_dec(v_unused_3785_);
v_unused_3786_ = lean_ctor_get(v_snd_3575_, 1);
lean_dec(v_unused_3786_);
v_unused_3787_ = lean_ctor_get(v_snd_3575_, 0);
lean_dec(v_unused_3787_);
v___x_3589_ = v_snd_3575_;
v_isShared_3590_ = v_isSharedCheck_3784_;
goto v_resetjp_3588_;
}
else
{
lean_dec(v_snd_3575_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3784_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v_a_3591_; lean_object* v_toConstantVal_3592_; lean_object* v_name_3593_; lean_object* v_levelParams_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3782_; 
v_a_3591_ = lean_array_uget_borrowed(v_as_3557_, v_i_3559_);
v_toConstantVal_3592_ = lean_ctor_get(v_a_3591_, 0);
lean_inc_ref(v_toConstantVal_3592_);
v_name_3593_ = lean_ctor_get(v_toConstantVal_3592_, 0);
v_levelParams_3594_ = lean_ctor_get(v_toConstantVal_3592_, 1);
v_isSharedCheck_3782_ = !lean_is_exclusive(v_toConstantVal_3592_);
if (v_isSharedCheck_3782_ == 0)
{
lean_object* v_unused_3783_; 
v_unused_3783_ = lean_ctor_get(v_toConstantVal_3592_, 2);
lean_dec(v_unused_3783_);
v___x_3596_ = v_toConstantVal_3592_;
v_isShared_3597_ = v_isSharedCheck_3782_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_levelParams_3594_);
lean_inc(v_name_3593_);
lean_dec(v_toConstantVal_3592_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3782_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3602_; 
v___x_3598_ = lean_array_fget(v_array_3580_, v_start_3581_);
v___x_3599_ = lean_unsigned_to_nat(1u);
v___x_3600_ = lean_nat_add(v_start_3581_, v___x_3599_);
lean_dec(v_start_3581_);
if (v_isShared_3590_ == 0)
{
lean_ctor_set(v___x_3589_, 1, v___x_3600_);
v___x_3602_ = v___x_3589_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_array_3580_);
lean_ctor_set(v_reuseFailAlloc_3781_, 1, v___x_3600_);
lean_ctor_set(v_reuseFailAlloc_3781_, 2, v_stop_3582_);
v___x_3602_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
uint8_t v___x_3603_; 
v___x_3603_ = l_Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0(v_typeNames_3556_, v_name_3593_);
if (v___x_3603_ == 0)
{
lean_object* v___x_3605_; 
lean_dec(v___x_3598_);
lean_del_object(v___x_3596_);
lean_dec(v_levelParams_3594_);
lean_dec(v_name_3593_);
if (v_isShared_3579_ == 0)
{
lean_ctor_set(v___x_3578_, 1, v___x_3602_);
v___x_3605_ = v___x_3578_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v_fst_3576_);
lean_ctor_set(v_reuseFailAlloc_3606_, 1, v___x_3602_);
v___x_3605_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
v_a_3569_ = v___x_3605_;
goto v___jp_3568_;
}
}
else
{
lean_object* v___x_3607_; 
lean_del_object(v___x_3578_);
lean_inc(v_a_3591_);
v___x_3607_ = l_Lean_Elab_Deriving_mkInductArgNames(v_a_3591_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_);
if (lean_obj_tag(v___x_3607_) == 0)
{
lean_object* v_a_3608_; lean_object* v___x_3609_; 
v_a_3608_ = lean_ctor_get(v___x_3607_, 0);
lean_inc_n(v_a_3608_, 2);
lean_dec_ref_known(v___x_3607_, 1);
v___x_3609_ = l_Lean_Elab_Deriving_mkImplicitBinders(v_a_3608_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_);
if (lean_obj_tag(v___x_3609_) == 0)
{
lean_object* v_a_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; 
v_a_3610_ = lean_ctor_get(v___x_3609_, 0);
lean_inc(v_a_3610_);
lean_dec_ref_known(v___x_3609_, 1);
v___x_3611_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__14));
lean_inc(v_a_3608_);
lean_inc(v_a_3591_);
v___x_3612_ = l_Lean_Elab_Deriving_mkInstImplicitBinders(v___x_3611_, v_a_3591_, v_a_3608_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_);
if (lean_obj_tag(v___x_3612_) == 0)
{
lean_object* v_a_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; size_t v_sz_3616_; size_t v___x_3617_; lean_object* v___x_3618_; 
v_a_3613_ = lean_ctor_get(v___x_3612_, 0);
lean_inc(v_a_3613_);
lean_dec_ref_known(v___x_3612_, 1);
v___x_3614_ = l_Array_append___redArg(v_a_3610_, v_a_3613_);
lean_dec(v_a_3613_);
v___x_3615_ = lean_array_mk(v_levelParams_3594_);
v_sz_3616_ = lean_array_size(v___x_3615_);
v___x_3617_ = ((size_t)0ULL);
v___x_3618_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg(v_sz_3616_, v___x_3617_, v___x_3615_, v___y_3565_, v___y_3566_);
if (lean_obj_tag(v___x_3618_) == 0)
{
lean_object* v_a_3619_; lean_object* v___x_3620_; lean_object* v_fst_3621_; lean_object* v_snd_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3748_; 
v_a_3619_ = lean_ctor_get(v___x_3618_, 0);
lean_inc(v_a_3619_);
lean_dec_ref_known(v___x_3618_, 1);
v___x_3620_ = l_Array_unzip___redArg(v_a_3619_);
lean_dec(v_a_3619_);
v_fst_3621_ = lean_ctor_get(v___x_3620_, 0);
v_snd_3622_ = lean_ctor_get(v___x_3620_, 1);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3620_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3624_ = v___x_3620_;
v_isShared_3625_ = v_isSharedCheck_3748_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_snd_3622_);
lean_inc(v_fst_3621_);
lean_dec(v___x_3620_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3748_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v___x_3626_; lean_object* v___x_3627_; 
v___x_3626_ = l_Array_append___redArg(v___x_3614_, v_snd_3622_);
lean_dec(v_snd_3622_);
lean_inc(v_a_3608_);
lean_inc(v_a_3591_);
v___x_3627_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v_a_3591_, v_a_3608_, v___y_3565_);
if (lean_obj_tag(v___x_3627_) == 0)
{
lean_object* v_a_3628_; lean_object* v___x_3629_; 
v_a_3628_ = lean_ctor_get(v___x_3627_, 0);
lean_inc(v_a_3628_);
lean_dec_ref_known(v___x_3627_, 1);
lean_inc(v_a_3591_);
v___x_3629_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType(v_a_3591_, v_a_3628_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_);
if (lean_obj_tag(v___x_3629_) == 0)
{
lean_object* v_a_3630_; lean_object* v___x_3631_; 
v_a_3630_ = lean_ctor_get(v___x_3629_, 0);
lean_inc(v_a_3630_);
lean_dec_ref_known(v___x_3629_, 1);
lean_inc(v_a_3591_);
v___x_3631_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr(v_a_3591_, v_a_3608_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_);
if (lean_obj_tag(v___x_3631_) == 0)
{
lean_object* v_a_3632_; lean_object* v___x_3633_; 
v_a_3632_ = lean_ctor_get(v___x_3631_, 0);
lean_inc(v_a_3632_);
lean_dec_ref_known(v___x_3631_, 1);
v___x_3633_ = l_Lean_Elab_Deriving_mkInstName(v___x_3611_, v_name_3593_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_);
if (lean_obj_tag(v___x_3633_) == 0)
{
lean_object* v_toCold_3634_; lean_object* v_a_3635_; lean_object* v_ref_3636_; lean_object* v_quotContext_3637_; lean_object* v_currMacroScope_3638_; uint8_t v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3646_; 
v_toCold_3634_ = lean_ctor_get(v___y_3565_, 0);
v_a_3635_ = lean_ctor_get(v___x_3633_, 0);
lean_inc(v_a_3635_);
lean_dec_ref_known(v___x_3633_, 1);
v_ref_3636_ = lean_ctor_get(v___y_3565_, 2);
v_quotContext_3637_ = lean_ctor_get(v_toCold_3634_, 8);
v_currMacroScope_3638_ = lean_ctor_get(v_toCold_3634_, 9);
v___x_3639_ = 0;
v___x_3640_ = l_Lean_SourceInfo_fromRef(v_ref_3636_, v___x_3639_);
v___x_3641_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__0));
v___x_3642_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__1));
v___x_3643_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_3644_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
lean_inc(v___x_3640_);
if (v_isShared_3597_ == 0)
{
lean_ctor_set_tag(v___x_3596_, 1);
lean_ctor_set(v___x_3596_, 2, v___x_3644_);
lean_ctor_set(v___x_3596_, 1, v___x_3643_);
lean_ctor_set(v___x_3596_, 0, v___x_3640_);
v___x_3646_ = v___x_3596_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v___x_3640_);
lean_ctor_set(v_reuseFailAlloc_3715_, 1, v___x_3643_);
lean_ctor_set(v_reuseFailAlloc_3715_, 2, v___x_3644_);
v___x_3646_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; size_t v_sz_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3713_; 
lean_inc_ref_n(v___x_3646_, 19);
lean_inc_n(v___x_3640_, 30);
v___x_3647_ = l_Lean_Syntax_node7(v___x_3640_, v___x_3642_, v___x_3646_, v___x_3646_, v___x_3646_, v___x_3646_, v___x_3646_, v___x_3646_, v___x_3646_);
v___x_3648_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__2));
v___x_3649_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__3));
v___x_3650_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__5));
v___x_3651_ = l_Lean_Syntax_node1(v___x_3640_, v___x_3650_, v___x_3646_);
v___x_3652_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3652_, 0, v___x_3640_);
lean_ctor_set(v___x_3652_, 1, v___x_3648_);
v___x_3653_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__6));
v___x_3654_ = l_Lean_mkIdent(v_a_3635_);
v___x_3655_ = l_Lean_Syntax_node2(v___x_3640_, v___x_3653_, v___x_3654_, v___x_3646_);
v___x_3656_ = l_Lean_Syntax_node1(v___x_3640_, v___x_3643_, v___x_3655_);
v___x_3657_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__8));
v___x_3658_ = l_Array_append___redArg(v___x_3644_, v___x_3626_);
lean_dec_ref(v___x_3626_);
v___x_3659_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3659_, 0, v___x_3640_);
lean_ctor_set(v___x_3659_, 1, v___x_3643_);
lean_ctor_set(v___x_3659_, 2, v___x_3658_);
v___x_3660_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__10));
v___x_3661_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__11));
v___x_3662_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3640_);
lean_ctor_set(v___x_3662_, 1, v___x_3661_);
v___x_3663_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_3664_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__12);
v___x_3665_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__13));
lean_inc_n(v_currMacroScope_3638_, 3);
lean_inc_n(v_quotContext_3637_, 3);
v___x_3666_ = l_Lean_addMacroScope(v_quotContext_3637_, v___x_3665_, v_currMacroScope_3638_);
v___x_3667_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__26));
v___x_3668_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3668_, 0, v___x_3640_);
lean_ctor_set(v___x_3668_, 1, v___x_3664_);
lean_ctor_set(v___x_3668_, 2, v___x_3666_);
lean_ctor_set(v___x_3668_, 3, v___x_3667_);
v___x_3669_ = l_Lean_Syntax_node1(v___x_3640_, v___x_3643_, v_a_3630_);
v___x_3670_ = l_Lean_Syntax_node2(v___x_3640_, v___x_3663_, v___x_3668_, v___x_3669_);
v___x_3671_ = l_Lean_Syntax_node2(v___x_3640_, v___x_3660_, v___x_3662_, v___x_3670_);
v___x_3672_ = l_Lean_Syntax_node2(v___x_3640_, v___x_3657_, v___x_3659_, v___x_3671_);
v___x_3673_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__10));
v___x_3674_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__11));
v___x_3675_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3675_, 0, v___x_3640_);
lean_ctor_set(v___x_3675_, 1, v___x_3674_);
v___x_3676_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__32));
v___x_3677_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__34));
v___x_3678_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__36));
v___x_3679_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1);
v___x_3680_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__2));
v___x_3681_ = l_Lean_addMacroScope(v_quotContext_3637_, v___x_3680_, v_currMacroScope_3638_);
v___x_3682_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__6));
v___x_3683_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3683_, 0, v___x_3640_);
lean_ctor_set(v___x_3683_, 1, v___x_3679_);
lean_ctor_set(v___x_3683_, 2, v___x_3681_);
lean_ctor_set(v___x_3683_, 3, v___x_3682_);
v___x_3684_ = l_Lean_Syntax_node2(v___x_3640_, v___x_3678_, v___x_3683_, v___x_3646_);
v___x_3685_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__38));
v___x_3686_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__27));
v___x_3687_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3687_, 0, v___x_3640_);
lean_ctor_set(v___x_3687_, 1, v___x_3686_);
v___x_3688_ = l_Lean_mkIdent(v___x_3598_);
v_sz_3689_ = lean_array_size(v_fst_3621_);
v___x_3690_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__2(v_sz_3689_, v___x_3617_, v_fst_3621_);
v___x_3691_ = l_Array_append___redArg(v___x_3644_, v___x_3690_);
lean_dec_ref(v___x_3690_);
v___x_3692_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3640_);
lean_ctor_set(v___x_3692_, 1, v___x_3643_);
lean_ctor_set(v___x_3692_, 2, v___x_3691_);
v___x_3693_ = l_Lean_Syntax_node2(v___x_3640_, v___x_3663_, v___x_3688_, v___x_3692_);
lean_inc_ref(v___x_3687_);
v___x_3694_ = l_Lean_Syntax_node3(v___x_3640_, v___x_3685_, v___x_3687_, v___x_3646_, v___x_3693_);
v___x_3695_ = l_Lean_Syntax_node3(v___x_3640_, v___x_3643_, v___x_3646_, v___x_3646_, v___x_3694_);
v___x_3696_ = l_Lean_Syntax_node2(v___x_3640_, v___x_3677_, v___x_3684_, v___x_3695_);
v___x_3697_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8);
v___x_3698_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__9));
v___x_3699_ = l_Lean_addMacroScope(v_quotContext_3637_, v___x_3698_, v_currMacroScope_3638_);
v___x_3700_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__12));
v___x_3701_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3701_, 0, v___x_3640_);
lean_ctor_set(v___x_3701_, 1, v___x_3697_);
lean_ctor_set(v___x_3701_, 2, v___x_3699_);
lean_ctor_set(v___x_3701_, 3, v___x_3700_);
v___x_3702_ = l_Lean_Syntax_node2(v___x_3640_, v___x_3678_, v___x_3701_, v___x_3646_);
v___x_3703_ = l_Lean_Syntax_node3(v___x_3640_, v___x_3685_, v___x_3687_, v___x_3646_, v_a_3632_);
v___x_3704_ = l_Lean_Syntax_node3(v___x_3640_, v___x_3643_, v___x_3646_, v___x_3646_, v___x_3703_);
v___x_3705_ = l_Lean_Syntax_node2(v___x_3640_, v___x_3677_, v___x_3702_, v___x_3704_);
v___x_3706_ = l_Lean_Syntax_node3(v___x_3640_, v___x_3643_, v___x_3696_, v___x_3646_, v___x_3705_);
v___x_3707_ = l_Lean_Syntax_node1(v___x_3640_, v___x_3676_, v___x_3706_);
v___x_3708_ = l_Lean_Syntax_node3(v___x_3640_, v___x_3673_, v___x_3675_, v___x_3707_, v___x_3646_);
v___x_3709_ = l_Lean_Syntax_node6(v___x_3640_, v___x_3649_, v___x_3651_, v___x_3652_, v___x_3646_, v___x_3656_, v___x_3672_, v___x_3708_);
v___x_3710_ = l_Lean_Syntax_node2(v___x_3640_, v___x_3641_, v___x_3647_, v___x_3709_);
v___x_3711_ = lean_array_push(v_fst_3576_, v___x_3710_);
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 1, v___x_3602_);
lean_ctor_set(v___x_3624_, 0, v___x_3711_);
v___x_3713_ = v___x_3624_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v___x_3711_);
lean_ctor_set(v_reuseFailAlloc_3714_, 1, v___x_3602_);
v___x_3713_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
v_a_3569_ = v___x_3713_;
goto v___jp_3568_;
}
}
}
else
{
lean_object* v_a_3716_; lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3723_; 
lean_dec(v_a_3632_);
lean_dec(v_a_3630_);
lean_dec_ref(v___x_3626_);
lean_del_object(v___x_3624_);
lean_dec(v_fst_3621_);
lean_dec_ref(v___x_3602_);
lean_dec(v___x_3598_);
lean_del_object(v___x_3596_);
lean_dec(v_fst_3576_);
v_a_3716_ = lean_ctor_get(v___x_3633_, 0);
v_isSharedCheck_3723_ = !lean_is_exclusive(v___x_3633_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3718_ = v___x_3633_;
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
else
{
lean_inc(v_a_3716_);
lean_dec(v___x_3633_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
lean_object* v___x_3721_; 
if (v_isShared_3719_ == 0)
{
v___x_3721_ = v___x_3718_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v_a_3716_);
v___x_3721_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
return v___x_3721_;
}
}
}
}
else
{
lean_object* v_a_3724_; lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3731_; 
lean_dec(v_a_3630_);
lean_dec_ref(v___x_3626_);
lean_del_object(v___x_3624_);
lean_dec(v_fst_3621_);
lean_dec_ref(v___x_3602_);
lean_dec(v___x_3598_);
lean_del_object(v___x_3596_);
lean_dec(v_name_3593_);
lean_dec(v_fst_3576_);
v_a_3724_ = lean_ctor_get(v___x_3631_, 0);
v_isSharedCheck_3731_ = !lean_is_exclusive(v___x_3631_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3726_ = v___x_3631_;
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
else
{
lean_inc(v_a_3724_);
lean_dec(v___x_3631_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
lean_object* v___x_3729_; 
if (v_isShared_3727_ == 0)
{
v___x_3729_ = v___x_3726_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v_a_3724_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
return v___x_3729_;
}
}
}
}
else
{
lean_object* v_a_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3739_; 
lean_dec_ref(v___x_3626_);
lean_del_object(v___x_3624_);
lean_dec(v_fst_3621_);
lean_dec(v_a_3608_);
lean_dec_ref(v___x_3602_);
lean_dec(v___x_3598_);
lean_del_object(v___x_3596_);
lean_dec(v_name_3593_);
lean_dec(v_fst_3576_);
v_a_3732_ = lean_ctor_get(v___x_3629_, 0);
v_isSharedCheck_3739_ = !lean_is_exclusive(v___x_3629_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3734_ = v___x_3629_;
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_a_3732_);
lean_dec(v___x_3629_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3737_; 
if (v_isShared_3735_ == 0)
{
v___x_3737_ = v___x_3734_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_a_3732_);
v___x_3737_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
return v___x_3737_;
}
}
}
}
else
{
lean_object* v_a_3740_; lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3747_; 
lean_dec_ref(v___x_3626_);
lean_del_object(v___x_3624_);
lean_dec(v_fst_3621_);
lean_dec(v_a_3608_);
lean_dec_ref(v___x_3602_);
lean_dec(v___x_3598_);
lean_del_object(v___x_3596_);
lean_dec(v_name_3593_);
lean_dec(v_fst_3576_);
v_a_3740_ = lean_ctor_get(v___x_3627_, 0);
v_isSharedCheck_3747_ = !lean_is_exclusive(v___x_3627_);
if (v_isSharedCheck_3747_ == 0)
{
v___x_3742_ = v___x_3627_;
v_isShared_3743_ = v_isSharedCheck_3747_;
goto v_resetjp_3741_;
}
else
{
lean_inc(v_a_3740_);
lean_dec(v___x_3627_);
v___x_3742_ = lean_box(0);
v_isShared_3743_ = v_isSharedCheck_3747_;
goto v_resetjp_3741_;
}
v_resetjp_3741_:
{
lean_object* v___x_3745_; 
if (v_isShared_3743_ == 0)
{
v___x_3745_ = v___x_3742_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_a_3740_);
v___x_3745_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
return v___x_3745_;
}
}
}
}
}
else
{
lean_object* v_a_3749_; lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3756_; 
lean_dec_ref(v___x_3614_);
lean_dec(v_a_3608_);
lean_dec_ref(v___x_3602_);
lean_dec(v___x_3598_);
lean_del_object(v___x_3596_);
lean_dec(v_name_3593_);
lean_dec(v_fst_3576_);
v_a_3749_ = lean_ctor_get(v___x_3618_, 0);
v_isSharedCheck_3756_ = !lean_is_exclusive(v___x_3618_);
if (v_isSharedCheck_3756_ == 0)
{
v___x_3751_ = v___x_3618_;
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
else
{
lean_inc(v_a_3749_);
lean_dec(v___x_3618_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v___x_3754_; 
if (v_isShared_3752_ == 0)
{
v___x_3754_ = v___x_3751_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v_a_3749_);
v___x_3754_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
return v___x_3754_;
}
}
}
}
else
{
lean_object* v_a_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3764_; 
lean_dec(v_a_3610_);
lean_dec(v_a_3608_);
lean_dec_ref(v___x_3602_);
lean_dec(v___x_3598_);
lean_del_object(v___x_3596_);
lean_dec(v_levelParams_3594_);
lean_dec(v_name_3593_);
lean_dec(v_fst_3576_);
v_a_3757_ = lean_ctor_get(v___x_3612_, 0);
v_isSharedCheck_3764_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3759_ = v___x_3612_;
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_a_3757_);
lean_dec(v___x_3612_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v___x_3762_; 
if (v_isShared_3760_ == 0)
{
v___x_3762_ = v___x_3759_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v_a_3757_);
v___x_3762_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
return v___x_3762_;
}
}
}
}
else
{
lean_object* v_a_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3772_; 
lean_dec(v_a_3608_);
lean_dec_ref(v___x_3602_);
lean_dec(v___x_3598_);
lean_del_object(v___x_3596_);
lean_dec(v_levelParams_3594_);
lean_dec(v_name_3593_);
lean_dec(v_fst_3576_);
v_a_3765_ = lean_ctor_get(v___x_3609_, 0);
v_isSharedCheck_3772_ = !lean_is_exclusive(v___x_3609_);
if (v_isSharedCheck_3772_ == 0)
{
v___x_3767_ = v___x_3609_;
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_a_3765_);
lean_dec(v___x_3609_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v___x_3770_; 
if (v_isShared_3768_ == 0)
{
v___x_3770_ = v___x_3767_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v_a_3765_);
v___x_3770_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
return v___x_3770_;
}
}
}
}
else
{
lean_object* v_a_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3780_; 
lean_dec_ref(v___x_3602_);
lean_dec(v___x_3598_);
lean_del_object(v___x_3596_);
lean_dec(v_levelParams_3594_);
lean_dec(v_name_3593_);
lean_dec(v_fst_3576_);
v_a_3773_ = lean_ctor_get(v___x_3607_, 0);
v_isSharedCheck_3780_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3780_ == 0)
{
v___x_3775_ = v___x_3607_;
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
else
{
lean_inc(v_a_3773_);
lean_dec(v___x_3607_);
v___x_3775_ = lean_box(0);
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
v_resetjp_3774_:
{
lean_object* v___x_3778_; 
if (v_isShared_3776_ == 0)
{
v___x_3778_ = v___x_3775_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v_a_3773_);
v___x_3778_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
return v___x_3778_;
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
v___jp_3568_:
{
size_t v___x_3570_; size_t v___x_3571_; 
v___x_3570_ = ((size_t)1ULL);
v___x_3571_ = lean_usize_add(v_i_3559_, v___x_3570_);
v_i_3559_ = v___x_3571_;
v_b_3560_ = v_a_3569_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___boxed(lean_object* v_typeNames_3789_, lean_object* v_as_3790_, lean_object* v_sz_3791_, lean_object* v_i_3792_, lean_object* v_b_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_){
_start:
{
size_t v_sz_boxed_3801_; size_t v_i_boxed_3802_; lean_object* v_res_3803_; 
v_sz_boxed_3801_ = lean_unbox_usize(v_sz_3791_);
lean_dec(v_sz_3791_);
v_i_boxed_3802_ = lean_unbox_usize(v_i_3792_);
lean_dec(v_i_3792_);
v_res_3803_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3(v_typeNames_3789_, v_as_3790_, v_sz_boxed_3801_, v_i_boxed_3802_, v_b_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_);
lean_dec(v___y_3799_);
lean_dec_ref(v___y_3798_);
lean_dec(v___y_3797_);
lean_dec_ref(v___y_3796_);
lean_dec(v___y_3795_);
lean_dec_ref(v___y_3794_);
lean_dec_ref(v_as_3790_);
lean_dec_ref(v_typeNames_3789_);
return v_res_3803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds(lean_object* v_ctx_3804_, lean_object* v_typeNames_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_){
_start:
{
lean_object* v_typeInfos_3813_; lean_object* v_auxFunNames_3814_; lean_object* v___x_3815_; lean_object* v_instances_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; size_t v_sz_3820_; size_t v___x_3821_; lean_object* v___x_3822_; 
v_typeInfos_3813_ = lean_ctor_get(v_ctx_3804_, 1);
lean_inc_ref(v_typeInfos_3813_);
v_auxFunNames_3814_ = lean_ctor_get(v_ctx_3804_, 2);
lean_inc_ref(v_auxFunNames_3814_);
lean_dec_ref(v_ctx_3804_);
v___x_3815_ = lean_unsigned_to_nat(0u);
v_instances_3816_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__0));
v___x_3817_ = lean_array_get_size(v_auxFunNames_3814_);
v___x_3818_ = l_Array_toSubarray___redArg(v_auxFunNames_3814_, v___x_3815_, v___x_3817_);
v___x_3819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3819_, 0, v_instances_3816_);
lean_ctor_set(v___x_3819_, 1, v___x_3818_);
v_sz_3820_ = lean_array_size(v_typeInfos_3813_);
v___x_3821_ = ((size_t)0ULL);
v___x_3822_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3(v_typeNames_3805_, v_typeInfos_3813_, v_sz_3820_, v___x_3821_, v___x_3819_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_);
lean_dec_ref(v_typeInfos_3813_);
if (lean_obj_tag(v___x_3822_) == 0)
{
lean_object* v_a_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3831_; 
v_a_3823_ = lean_ctor_get(v___x_3822_, 0);
v_isSharedCheck_3831_ = !lean_is_exclusive(v___x_3822_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3825_ = v___x_3822_;
v_isShared_3826_ = v_isSharedCheck_3831_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_a_3823_);
lean_dec(v___x_3822_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3831_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v_fst_3827_; lean_object* v___x_3829_; 
v_fst_3827_ = lean_ctor_get(v_a_3823_, 0);
lean_inc(v_fst_3827_);
lean_dec(v_a_3823_);
if (v_isShared_3826_ == 0)
{
lean_ctor_set(v___x_3825_, 0, v_fst_3827_);
v___x_3829_ = v___x_3825_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_fst_3827_);
v___x_3829_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
return v___x_3829_;
}
}
}
else
{
lean_object* v_a_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3839_; 
v_a_3832_ = lean_ctor_get(v___x_3822_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3822_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3834_ = v___x_3822_;
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_a_3832_);
lean_dec(v___x_3822_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v___x_3837_; 
if (v_isShared_3835_ == 0)
{
v___x_3837_ = v___x_3834_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_a_3832_);
v___x_3837_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
return v___x_3837_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds___boxed(lean_object* v_ctx_3840_, lean_object* v_typeNames_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_){
_start:
{
lean_object* v_res_3849_; 
v_res_3849_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds(v_ctx_3840_, v_typeNames_3841_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_);
lean_dec(v_a_3847_);
lean_dec_ref(v_a_3846_);
lean_dec(v_a_3845_);
lean_dec_ref(v_a_3844_);
lean_dec(v_a_3843_);
lean_dec_ref(v_a_3842_);
lean_dec_ref(v_typeNames_3841_);
return v_res_3849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1(size_t v_sz_3850_, size_t v_i_3851_, lean_object* v_bs_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_){
_start:
{
lean_object* v___x_3860_; 
v___x_3860_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg(v_sz_3850_, v_i_3851_, v_bs_3852_, v___y_3857_, v___y_3858_);
return v___x_3860_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___boxed(lean_object* v_sz_3861_, lean_object* v_i_3862_, lean_object* v_bs_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_){
_start:
{
size_t v_sz_boxed_3871_; size_t v_i_boxed_3872_; lean_object* v_res_3873_; 
v_sz_boxed_3871_ = lean_unbox_usize(v_sz_3861_);
lean_dec(v_sz_3861_);
v_i_boxed_3872_ = lean_unbox_usize(v_i_3862_);
lean_dec(v_i_3862_);
v_res_3873_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1(v_sz_boxed_3871_, v_i_boxed_3872_, v_bs_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_);
lean_dec(v___y_3869_);
lean_dec_ref(v___y_3868_);
lean_dec(v___y_3867_);
lean_dec_ref(v___y_3866_);
lean_dec(v___y_3865_);
lean_dec_ref(v___y_3864_);
return v_res_3873_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__0(lean_object* v_a_3874_, lean_object* v_a_3875_){
_start:
{
if (lean_obj_tag(v_a_3874_) == 0)
{
lean_object* v___x_3876_; 
v___x_3876_ = l_List_reverse___redArg(v_a_3875_);
return v___x_3876_;
}
else
{
lean_object* v_head_3877_; lean_object* v_tail_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3887_; 
v_head_3877_ = lean_ctor_get(v_a_3874_, 0);
v_tail_3878_ = lean_ctor_get(v_a_3874_, 1);
v_isSharedCheck_3887_ = !lean_is_exclusive(v_a_3874_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3880_ = v_a_3874_;
v_isShared_3881_ = v_isSharedCheck_3887_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_tail_3878_);
lean_inc(v_head_3877_);
lean_dec(v_a_3874_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3887_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3882_; lean_object* v___x_3884_; 
v___x_3882_ = l_Lean_MessageData_ofSyntax(v_head_3877_);
if (v_isShared_3881_ == 0)
{
lean_ctor_set(v___x_3880_, 1, v_a_3875_);
lean_ctor_set(v___x_3880_, 0, v___x_3882_);
v___x_3884_ = v___x_3880_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v___x_3882_);
lean_ctor_set(v_reuseFailAlloc_3886_, 1, v_a_3875_);
v___x_3884_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
v_a_3874_ = v_tail_3878_;
v_a_3875_ = v___x_3884_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3888_; double v___x_3889_; 
v___x_3888_ = lean_unsigned_to_nat(0u);
v___x_3889_ = lean_float_of_nat(v___x_3888_);
return v___x_3889_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg(lean_object* v_cls_3893_, lean_object* v_msg_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_){
_start:
{
lean_object* v_ref_3900_; lean_object* v___x_3901_; lean_object* v_a_3902_; lean_object* v___x_3904_; uint8_t v_isShared_3905_; uint8_t v_isSharedCheck_3947_; 
v_ref_3900_ = lean_ctor_get(v___y_3897_, 2);
v___x_3901_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__0(v_msg_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
v_a_3902_ = lean_ctor_get(v___x_3901_, 0);
v_isSharedCheck_3947_ = !lean_is_exclusive(v___x_3901_);
if (v_isSharedCheck_3947_ == 0)
{
v___x_3904_ = v___x_3901_;
v_isShared_3905_ = v_isSharedCheck_3947_;
goto v_resetjp_3903_;
}
else
{
lean_inc(v_a_3902_);
lean_dec(v___x_3901_);
v___x_3904_ = lean_box(0);
v_isShared_3905_ = v_isSharedCheck_3947_;
goto v_resetjp_3903_;
}
v_resetjp_3903_:
{
lean_object* v___x_3906_; lean_object* v_traceState_3907_; lean_object* v_env_3908_; lean_object* v_nextMacroScope_3909_; lean_object* v_ngen_3910_; lean_object* v_auxDeclNGen_3911_; lean_object* v_cache_3912_; lean_object* v_recordedDeps_3913_; lean_object* v_messages_3914_; lean_object* v_infoState_3915_; lean_object* v_snapshotTasks_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3946_; 
v___x_3906_ = lean_st_ref_take(v___y_3898_);
v_traceState_3907_ = lean_ctor_get(v___x_3906_, 4);
v_env_3908_ = lean_ctor_get(v___x_3906_, 0);
v_nextMacroScope_3909_ = lean_ctor_get(v___x_3906_, 1);
v_ngen_3910_ = lean_ctor_get(v___x_3906_, 2);
v_auxDeclNGen_3911_ = lean_ctor_get(v___x_3906_, 3);
v_cache_3912_ = lean_ctor_get(v___x_3906_, 5);
v_recordedDeps_3913_ = lean_ctor_get(v___x_3906_, 6);
v_messages_3914_ = lean_ctor_get(v___x_3906_, 7);
v_infoState_3915_ = lean_ctor_get(v___x_3906_, 8);
v_snapshotTasks_3916_ = lean_ctor_get(v___x_3906_, 9);
v_isSharedCheck_3946_ = !lean_is_exclusive(v___x_3906_);
if (v_isSharedCheck_3946_ == 0)
{
v___x_3918_ = v___x_3906_;
v_isShared_3919_ = v_isSharedCheck_3946_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_snapshotTasks_3916_);
lean_inc(v_infoState_3915_);
lean_inc(v_messages_3914_);
lean_inc(v_recordedDeps_3913_);
lean_inc(v_cache_3912_);
lean_inc(v_traceState_3907_);
lean_inc(v_auxDeclNGen_3911_);
lean_inc(v_ngen_3910_);
lean_inc(v_nextMacroScope_3909_);
lean_inc(v_env_3908_);
lean_dec(v___x_3906_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3946_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
uint64_t v_tid_3920_; lean_object* v_traces_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3945_; 
v_tid_3920_ = lean_ctor_get_uint64(v_traceState_3907_, sizeof(void*)*1);
v_traces_3921_ = lean_ctor_get(v_traceState_3907_, 0);
v_isSharedCheck_3945_ = !lean_is_exclusive(v_traceState_3907_);
if (v_isSharedCheck_3945_ == 0)
{
v___x_3923_ = v_traceState_3907_;
v_isShared_3924_ = v_isSharedCheck_3945_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_traces_3921_);
lean_dec(v_traceState_3907_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3945_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
lean_object* v___x_3925_; lean_object* v___x_3926_; double v___x_3927_; uint8_t v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3936_; 
v___x_3925_ = lean_box(0);
v___x_3926_ = lean_box(0);
v___x_3927_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg___closed__0);
v___x_3928_ = 0;
v___x_3929_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg___closed__1));
v___x_3930_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3930_, 0, v_cls_3893_);
lean_ctor_set(v___x_3930_, 1, v___x_3926_);
lean_ctor_set(v___x_3930_, 2, v___x_3929_);
lean_ctor_set_float(v___x_3930_, sizeof(void*)*3, v___x_3927_);
lean_ctor_set_float(v___x_3930_, sizeof(void*)*3 + 8, v___x_3927_);
lean_ctor_set_uint8(v___x_3930_, sizeof(void*)*3 + 16, v___x_3928_);
v___x_3931_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg___closed__2));
v___x_3932_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3932_, 0, v___x_3930_);
lean_ctor_set(v___x_3932_, 1, v_a_3902_);
lean_ctor_set(v___x_3932_, 2, v___x_3931_);
lean_inc(v_ref_3900_);
v___x_3933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3933_, 0, v_ref_3900_);
lean_ctor_set(v___x_3933_, 1, v___x_3932_);
v___x_3934_ = l_Lean_PersistentArray_push___redArg(v_traces_3921_, v___x_3933_);
if (v_isShared_3924_ == 0)
{
lean_ctor_set(v___x_3923_, 0, v___x_3934_);
v___x_3936_ = v___x_3923_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3944_, 0, v___x_3934_);
lean_ctor_set_uint64(v_reuseFailAlloc_3944_, sizeof(void*)*1, v_tid_3920_);
v___x_3936_ = v_reuseFailAlloc_3944_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
lean_object* v___x_3938_; 
if (v_isShared_3919_ == 0)
{
lean_ctor_set(v___x_3918_, 4, v___x_3936_);
v___x_3938_ = v___x_3918_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_env_3908_);
lean_ctor_set(v_reuseFailAlloc_3943_, 1, v_nextMacroScope_3909_);
lean_ctor_set(v_reuseFailAlloc_3943_, 2, v_ngen_3910_);
lean_ctor_set(v_reuseFailAlloc_3943_, 3, v_auxDeclNGen_3911_);
lean_ctor_set(v_reuseFailAlloc_3943_, 4, v___x_3936_);
lean_ctor_set(v_reuseFailAlloc_3943_, 5, v_cache_3912_);
lean_ctor_set(v_reuseFailAlloc_3943_, 6, v_recordedDeps_3913_);
lean_ctor_set(v_reuseFailAlloc_3943_, 7, v_messages_3914_);
lean_ctor_set(v_reuseFailAlloc_3943_, 8, v_infoState_3915_);
lean_ctor_set(v_reuseFailAlloc_3943_, 9, v_snapshotTasks_3916_);
v___x_3938_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
lean_object* v___x_3939_; lean_object* v___x_3941_; 
v___x_3939_ = lean_st_ref_put(v___y_3898_, v___x_3938_);
if (v_isShared_3905_ == 0)
{
lean_ctor_set(v___x_3904_, 0, v___x_3925_);
v___x_3941_ = v___x_3904_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v___x_3925_);
v___x_3941_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
return v___x_3941_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg___boxed(lean_object* v_cls_3948_, lean_object* v_msg_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_){
_start:
{
lean_object* v_res_3955_; 
v_res_3955_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg(v_cls_3948_, v_msg_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_);
lean_dec(v___y_3953_);
lean_dec_ref(v___y_3952_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
return v_res_3955_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__3(void){
_start:
{
lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
v___x_3963_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__0));
v___x_3964_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__2));
v___x_3965_ = l_Lean_Name_append(v___x_3964_, v___x_3963_);
return v___x_3965_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__5(void){
_start:
{
lean_object* v___x_3967_; lean_object* v___x_3968_; 
v___x_3967_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__4));
v___x_3968_ = l_Lean_stringToMessageData(v___x_3967_);
return v___x_3968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds(lean_object* v_declNames_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_, lean_object* v_a_3974_, lean_object* v_a_3975_){
_start:
{
lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; uint8_t v___x_3982_; lean_object* v___x_3983_; 
v___x_3977_ = lean_box(0);
v___x_3978_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__14));
v___x_3979_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__0));
v___x_3980_ = lean_unsigned_to_nat(0u);
v___x_3981_ = lean_array_get_borrowed(v___x_3977_, v_declNames_3969_, v___x_3980_);
v___x_3982_ = 1;
lean_inc(v___x_3981_);
v___x_3983_ = l_Lean_Elab_Deriving_mkContext(v___x_3978_, v___x_3979_, v___x_3981_, v___x_3982_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_, v_a_3974_, v_a_3975_);
if (lean_obj_tag(v___x_3983_) == 0)
{
lean_object* v_a_3984_; lean_object* v___x_3985_; 
v_a_3984_ = lean_ctor_get(v___x_3983_, 0);
lean_inc_n(v_a_3984_, 2);
lean_dec_ref_known(v___x_3983_, 1);
v___x_3985_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions(v_a_3984_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_, v_a_3974_, v_a_3975_);
if (lean_obj_tag(v___x_3985_) == 0)
{
lean_object* v_a_3986_; lean_object* v___x_3987_; 
v_a_3986_ = lean_ctor_get(v___x_3985_, 0);
lean_inc(v_a_3986_);
lean_dec_ref_known(v___x_3985_, 1);
v___x_3987_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds(v_a_3984_, v_declNames_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_, v_a_3974_, v_a_3975_);
if (lean_obj_tag(v___x_3987_) == 0)
{
lean_object* v_toCold_3988_; lean_object* v_options_3989_; lean_object* v_a_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_4032_; 
v_toCold_3988_ = lean_ctor_get(v_a_3974_, 0);
v_options_3989_ = lean_ctor_get(v_toCold_3988_, 2);
v_a_3990_ = lean_ctor_get(v___x_3987_, 0);
v_isSharedCheck_4032_ = !lean_is_exclusive(v___x_3987_);
if (v_isSharedCheck_4032_ == 0)
{
v___x_3992_ = v___x_3987_;
v_isShared_3993_ = v_isSharedCheck_4032_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_a_3990_);
lean_dec(v___x_3987_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_4032_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v_inheritedTraceOptions_3994_; uint8_t v_hasTrace_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; 
v_inheritedTraceOptions_3994_ = lean_ctor_get(v_toCold_3988_, 11);
v_hasTrace_3995_ = lean_ctor_get_uint8(v_options_3989_, sizeof(void*)*1);
v___x_3996_ = lean_unsigned_to_nat(1u);
v___x_3997_ = lean_mk_empty_array_with_capacity(v___x_3996_);
v___x_3998_ = lean_array_push(v___x_3997_, v_a_3986_);
v___x_3999_ = l_Array_append___redArg(v___x_3998_, v_a_3990_);
lean_dec(v_a_3990_);
if (v_hasTrace_3995_ == 0)
{
lean_object* v___x_4001_; 
if (v_isShared_3993_ == 0)
{
lean_ctor_set(v___x_3992_, 0, v___x_3999_);
v___x_4001_ = v___x_3992_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v___x_3999_);
v___x_4001_ = v_reuseFailAlloc_4002_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
return v___x_4001_;
}
}
else
{
lean_object* v___x_4003_; lean_object* v___x_4004_; uint8_t v___x_4005_; 
v___x_4003_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__0));
v___x_4004_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__3, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__3_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__3);
v___x_4005_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3994_, v_options_3989_, v___x_4004_);
if (v___x_4005_ == 0)
{
lean_object* v___x_4007_; 
if (v_isShared_3993_ == 0)
{
lean_ctor_set(v___x_3992_, 0, v___x_3999_);
v___x_4007_ = v___x_3992_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v___x_3999_);
v___x_4007_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
return v___x_4007_;
}
}
else
{
lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; 
lean_del_object(v___x_3992_);
v___x_4009_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__5, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__5_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__5);
lean_inc_ref(v___x_3999_);
v___x_4010_ = lean_array_to_list(v___x_3999_);
v___x_4011_ = lean_box(0);
v___x_4012_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__0(v___x_4010_, v___x_4011_);
v___x_4013_ = l_Lean_MessageData_ofList(v___x_4012_);
v___x_4014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4014_, 0, v___x_4009_);
lean_ctor_set(v___x_4014_, 1, v___x_4013_);
v___x_4015_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg(v___x_4003_, v___x_4014_, v_a_3972_, v_a_3973_, v_a_3974_, v_a_3975_);
if (lean_obj_tag(v___x_4015_) == 0)
{
lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4022_; 
v_isSharedCheck_4022_ = !lean_is_exclusive(v___x_4015_);
if (v_isSharedCheck_4022_ == 0)
{
lean_object* v_unused_4023_; 
v_unused_4023_ = lean_ctor_get(v___x_4015_, 0);
lean_dec(v_unused_4023_);
v___x_4017_ = v___x_4015_;
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
else
{
lean_dec(v___x_4015_);
v___x_4017_ = lean_box(0);
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
v_resetjp_4016_:
{
lean_object* v___x_4020_; 
if (v_isShared_4018_ == 0)
{
lean_ctor_set(v___x_4017_, 0, v___x_3999_);
v___x_4020_ = v___x_4017_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v___x_3999_);
v___x_4020_ = v_reuseFailAlloc_4021_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
return v___x_4020_;
}
}
}
else
{
lean_object* v_a_4024_; lean_object* v___x_4026_; uint8_t v_isShared_4027_; uint8_t v_isSharedCheck_4031_; 
lean_dec_ref(v___x_3999_);
v_a_4024_ = lean_ctor_get(v___x_4015_, 0);
v_isSharedCheck_4031_ = !lean_is_exclusive(v___x_4015_);
if (v_isSharedCheck_4031_ == 0)
{
v___x_4026_ = v___x_4015_;
v_isShared_4027_ = v_isSharedCheck_4031_;
goto v_resetjp_4025_;
}
else
{
lean_inc(v_a_4024_);
lean_dec(v___x_4015_);
v___x_4026_ = lean_box(0);
v_isShared_4027_ = v_isSharedCheck_4031_;
goto v_resetjp_4025_;
}
v_resetjp_4025_:
{
lean_object* v___x_4029_; 
if (v_isShared_4027_ == 0)
{
v___x_4029_ = v___x_4026_;
goto v_reusejp_4028_;
}
else
{
lean_object* v_reuseFailAlloc_4030_; 
v_reuseFailAlloc_4030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4030_, 0, v_a_4024_);
v___x_4029_ = v_reuseFailAlloc_4030_;
goto v_reusejp_4028_;
}
v_reusejp_4028_:
{
return v___x_4029_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4040_; 
lean_dec(v_a_3986_);
v_a_4033_ = lean_ctor_get(v___x_3987_, 0);
v_isSharedCheck_4040_ = !lean_is_exclusive(v___x_3987_);
if (v_isSharedCheck_4040_ == 0)
{
v___x_4035_ = v___x_3987_;
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_a_4033_);
lean_dec(v___x_3987_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
lean_object* v___x_4038_; 
if (v_isShared_4036_ == 0)
{
v___x_4038_ = v___x_4035_;
goto v_reusejp_4037_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v_a_4033_);
v___x_4038_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4037_;
}
v_reusejp_4037_:
{
return v___x_4038_;
}
}
}
}
else
{
lean_object* v_a_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4048_; 
lean_dec(v_a_3984_);
v_a_4041_ = lean_ctor_get(v___x_3985_, 0);
v_isSharedCheck_4048_ = !lean_is_exclusive(v___x_3985_);
if (v_isSharedCheck_4048_ == 0)
{
v___x_4043_ = v___x_3985_;
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_a_4041_);
lean_dec(v___x_3985_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v___x_4046_; 
if (v_isShared_4044_ == 0)
{
v___x_4046_ = v___x_4043_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v_a_4041_);
v___x_4046_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
return v___x_4046_;
}
}
}
}
else
{
lean_object* v_a_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4056_; 
v_a_4049_ = lean_ctor_get(v___x_3983_, 0);
v_isSharedCheck_4056_ = !lean_is_exclusive(v___x_3983_);
if (v_isSharedCheck_4056_ == 0)
{
v___x_4051_ = v___x_3983_;
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_a_4049_);
lean_dec(v___x_3983_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
lean_object* v___x_4054_; 
if (v_isShared_4052_ == 0)
{
v___x_4054_ = v___x_4051_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_a_4049_);
v___x_4054_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
return v___x_4054_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___boxed(lean_object* v_declNames_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_){
_start:
{
lean_object* v_res_4065_; 
v_res_4065_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds(v_declNames_4057_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_);
lean_dec(v_a_4063_);
lean_dec_ref(v_a_4062_);
lean_dec(v_a_4061_);
lean_dec_ref(v_a_4060_);
lean_dec(v_a_4059_);
lean_dec_ref(v_a_4058_);
lean_dec_ref(v_declNames_4057_);
return v_res_4065_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1(lean_object* v_cls_4066_, lean_object* v_msg_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_){
_start:
{
lean_object* v___x_4075_; 
v___x_4075_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg(v_cls_4066_, v_msg_4067_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_);
return v___x_4075_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___boxed(lean_object* v_cls_4076_, lean_object* v_msg_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_){
_start:
{
lean_object* v_res_4085_; 
v_res_4085_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1(v_cls_4076_, v_msg_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_);
lean_dec(v___y_4083_);
lean_dec_ref(v___y_4082_);
lean_dec(v___y_4081_);
lean_dec_ref(v___y_4080_);
lean_dec(v___y_4079_);
lean_dec_ref(v___y_4078_);
return v_res_4085_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0___redArg(lean_object* v_declName_4086_, lean_object* v___y_4087_){
_start:
{
lean_object* v___x_4089_; lean_object* v_env_4090_; uint8_t v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; 
v___x_4089_ = lean_st_ref_get(v___y_4087_);
v_env_4090_ = lean_ctor_get(v___x_4089_, 0);
lean_inc_ref(v_env_4090_);
lean_dec(v___x_4089_);
v___x_4091_ = l_Lean_isInductiveCore(v_env_4090_, v_declName_4086_);
v___x_4092_ = lean_box(v___x_4091_);
v___x_4093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4093_, 0, v___x_4092_);
return v___x_4093_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0___redArg___boxed(lean_object* v_declName_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_){
_start:
{
lean_object* v_res_4097_; 
v_res_4097_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0___redArg(v_declName_4094_, v___y_4095_);
lean_dec(v___y_4095_);
return v_res_4097_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0(lean_object* v_declName_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_){
_start:
{
lean_object* v___x_4102_; 
v___x_4102_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0___redArg(v_declName_4098_, v___y_4100_);
return v___x_4102_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0___boxed(lean_object* v_declName_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_){
_start:
{
lean_object* v_res_4107_; 
v_res_4107_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0(v_declName_4103_, v___y_4104_, v___y_4105_);
lean_dec(v___y_4105_);
lean_dec_ref(v___y_4104_);
return v_res_4107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__0(uint8_t v_____do__lift_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_){
_start:
{
if (v_____do__lift_4108_ == 0)
{
uint8_t v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; 
v___x_4112_ = 1;
v___x_4113_ = lean_box(v___x_4112_);
v___x_4114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4114_, 0, v___x_4113_);
return v___x_4114_;
}
else
{
uint8_t v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; 
v___x_4115_ = 0;
v___x_4116_ = lean_box(v___x_4115_);
v___x_4117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4117_, 0, v___x_4116_);
return v___x_4117_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__0___boxed(lean_object* v_____do__lift_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_){
_start:
{
uint8_t v_____do__lift_1525__boxed_4122_; lean_object* v_res_4123_; 
v_____do__lift_1525__boxed_4122_ = lean_unbox(v_____do__lift_4118_);
v_res_4123_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__0(v_____do__lift_1525__boxed_4122_, v___y_4119_, v___y_4120_);
lean_dec(v___y_4120_);
lean_dec_ref(v___y_4119_);
return v_res_4123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1_spec__1(lean_object* v_o_4124_, lean_object* v_k_4125_, uint8_t v_v_4126_){
_start:
{
lean_object* v_map_4127_; uint8_t v_hasTrace_4128_; lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4142_; 
v_map_4127_ = lean_ctor_get(v_o_4124_, 0);
v_hasTrace_4128_ = lean_ctor_get_uint8(v_o_4124_, sizeof(void*)*1);
v_isSharedCheck_4142_ = !lean_is_exclusive(v_o_4124_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4130_ = v_o_4124_;
v_isShared_4131_ = v_isSharedCheck_4142_;
goto v_resetjp_4129_;
}
else
{
lean_inc(v_map_4127_);
lean_dec(v_o_4124_);
v___x_4130_ = lean_box(0);
v_isShared_4131_ = v_isSharedCheck_4142_;
goto v_resetjp_4129_;
}
v_resetjp_4129_:
{
lean_object* v___x_4132_; lean_object* v___x_4133_; 
v___x_4132_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4132_, 0, v_v_4126_);
lean_inc(v_k_4125_);
v___x_4133_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4125_, v___x_4132_, v_map_4127_);
if (v_hasTrace_4128_ == 0)
{
lean_object* v___x_4134_; uint8_t v___x_4135_; lean_object* v___x_4137_; 
v___x_4134_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__2));
v___x_4135_ = l_Lean_Name_isPrefixOf(v___x_4134_, v_k_4125_);
lean_dec(v_k_4125_);
if (v_isShared_4131_ == 0)
{
lean_ctor_set(v___x_4130_, 0, v___x_4133_);
v___x_4137_ = v___x_4130_;
goto v_reusejp_4136_;
}
else
{
lean_object* v_reuseFailAlloc_4138_; 
v_reuseFailAlloc_4138_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4138_, 0, v___x_4133_);
v___x_4137_ = v_reuseFailAlloc_4138_;
goto v_reusejp_4136_;
}
v_reusejp_4136_:
{
lean_ctor_set_uint8(v___x_4137_, sizeof(void*)*1, v___x_4135_);
return v___x_4137_;
}
}
else
{
lean_object* v___x_4140_; 
lean_dec(v_k_4125_);
if (v_isShared_4131_ == 0)
{
lean_ctor_set(v___x_4130_, 0, v___x_4133_);
v___x_4140_ = v___x_4130_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v___x_4133_);
lean_ctor_set_uint8(v_reuseFailAlloc_4141_, sizeof(void*)*1, v_hasTrace_4128_);
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
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1_spec__1___boxed(lean_object* v_o_4143_, lean_object* v_k_4144_, lean_object* v_v_4145_){
_start:
{
uint8_t v_v_boxed_4146_; lean_object* v_res_4147_; 
v_v_boxed_4146_ = lean_unbox(v_v_4145_);
v_res_4147_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1_spec__1(v_o_4143_, v_k_4144_, v_v_boxed_4146_);
return v_res_4147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1(lean_object* v_opts_4148_, lean_object* v_opt_4149_, uint8_t v_val_4150_){
_start:
{
lean_object* v_name_4151_; lean_object* v___x_4152_; 
v_name_4151_ = lean_ctor_get(v_opt_4149_, 0);
lean_inc(v_name_4151_);
lean_dec_ref(v_opt_4149_);
v___x_4152_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1_spec__1(v_opts_4148_, v_name_4151_, v_val_4150_);
return v___x_4152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1___boxed(lean_object* v_opts_4153_, lean_object* v_opt_4154_, lean_object* v_val_4155_){
_start:
{
uint8_t v_val_boxed_4156_; lean_object* v_res_4157_; 
v_val_boxed_4156_ = lean_unbox(v_val_4155_);
v_res_4157_ = l_Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1(v_opts_4153_, v_opt_4154_, v_val_boxed_4156_);
return v_res_4157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__1(uint8_t v_a_4158_, lean_object* v_scope_4159_){
_start:
{
lean_object* v_header_4160_; lean_object* v_opts_4161_; lean_object* v_currNamespace_4162_; lean_object* v_openDecls_4163_; lean_object* v_levelNames_4164_; lean_object* v_varDecls_4165_; lean_object* v_varUIds_4166_; lean_object* v_includedVars_4167_; lean_object* v_omittedVars_4168_; uint8_t v_isNoncomputable_4169_; uint8_t v_isPublic_4170_; uint8_t v_isMeta_4171_; lean_object* v_attrs_4172_; lean_object* v___x_4174_; uint8_t v_isShared_4175_; uint8_t v_isSharedCheck_4181_; 
v_header_4160_ = lean_ctor_get(v_scope_4159_, 0);
v_opts_4161_ = lean_ctor_get(v_scope_4159_, 1);
v_currNamespace_4162_ = lean_ctor_get(v_scope_4159_, 2);
v_openDecls_4163_ = lean_ctor_get(v_scope_4159_, 3);
v_levelNames_4164_ = lean_ctor_get(v_scope_4159_, 4);
v_varDecls_4165_ = lean_ctor_get(v_scope_4159_, 5);
v_varUIds_4166_ = lean_ctor_get(v_scope_4159_, 6);
v_includedVars_4167_ = lean_ctor_get(v_scope_4159_, 7);
v_omittedVars_4168_ = lean_ctor_get(v_scope_4159_, 8);
v_isNoncomputable_4169_ = lean_ctor_get_uint8(v_scope_4159_, sizeof(void*)*10);
v_isPublic_4170_ = lean_ctor_get_uint8(v_scope_4159_, sizeof(void*)*10 + 1);
v_isMeta_4171_ = lean_ctor_get_uint8(v_scope_4159_, sizeof(void*)*10 + 2);
v_attrs_4172_ = lean_ctor_get(v_scope_4159_, 9);
v_isSharedCheck_4181_ = !lean_is_exclusive(v_scope_4159_);
if (v_isSharedCheck_4181_ == 0)
{
v___x_4174_ = v_scope_4159_;
v_isShared_4175_ = v_isSharedCheck_4181_;
goto v_resetjp_4173_;
}
else
{
lean_inc(v_attrs_4172_);
lean_inc(v_omittedVars_4168_);
lean_inc(v_includedVars_4167_);
lean_inc(v_varUIds_4166_);
lean_inc(v_varDecls_4165_);
lean_inc(v_levelNames_4164_);
lean_inc(v_openDecls_4163_);
lean_inc(v_currNamespace_4162_);
lean_inc(v_opts_4161_);
lean_inc(v_header_4160_);
lean_dec(v_scope_4159_);
v___x_4174_ = lean_box(0);
v_isShared_4175_ = v_isSharedCheck_4181_;
goto v_resetjp_4173_;
}
v_resetjp_4173_:
{
lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4179_; 
v___x_4176_ = l_Lean_Elab_autoImplicit;
v___x_4177_ = l_Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1(v_opts_4161_, v___x_4176_, v_a_4158_);
if (v_isShared_4175_ == 0)
{
lean_ctor_set(v___x_4174_, 1, v___x_4177_);
v___x_4179_ = v___x_4174_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4180_; 
v_reuseFailAlloc_4180_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v_reuseFailAlloc_4180_, 0, v_header_4160_);
lean_ctor_set(v_reuseFailAlloc_4180_, 1, v___x_4177_);
lean_ctor_set(v_reuseFailAlloc_4180_, 2, v_currNamespace_4162_);
lean_ctor_set(v_reuseFailAlloc_4180_, 3, v_openDecls_4163_);
lean_ctor_set(v_reuseFailAlloc_4180_, 4, v_levelNames_4164_);
lean_ctor_set(v_reuseFailAlloc_4180_, 5, v_varDecls_4165_);
lean_ctor_set(v_reuseFailAlloc_4180_, 6, v_varUIds_4166_);
lean_ctor_set(v_reuseFailAlloc_4180_, 7, v_includedVars_4167_);
lean_ctor_set(v_reuseFailAlloc_4180_, 8, v_omittedVars_4168_);
lean_ctor_set(v_reuseFailAlloc_4180_, 9, v_attrs_4172_);
lean_ctor_set_uint8(v_reuseFailAlloc_4180_, sizeof(void*)*10, v_isNoncomputable_4169_);
lean_ctor_set_uint8(v_reuseFailAlloc_4180_, sizeof(void*)*10 + 1, v_isPublic_4170_);
lean_ctor_set_uint8(v_reuseFailAlloc_4180_, sizeof(void*)*10 + 2, v_isMeta_4171_);
v___x_4179_ = v_reuseFailAlloc_4180_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
return v___x_4179_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__1___boxed(lean_object* v_a_4182_, lean_object* v_scope_4183_){
_start:
{
uint8_t v_a_1583__boxed_4184_; lean_object* v_res_4185_; 
v_a_1583__boxed_4184_ = lean_unbox(v_a_4182_);
v_res_4185_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__1(v_a_1583__boxed_4184_, v_scope_4183_);
return v_res_4185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__2(lean_object* v_as_4186_, size_t v_i_4187_, size_t v_stop_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_){
_start:
{
uint8_t v___x_4196_; 
v___x_4196_ = lean_usize_dec_eq(v_i_4187_, v_stop_4188_);
if (v___x_4196_ == 0)
{
uint8_t v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; 
v___x_4197_ = 1;
v___x_4198_ = lean_array_uget_borrowed(v_as_4186_, v_i_4187_);
lean_inc(v___x_4198_);
v___x_4199_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0___redArg(v___x_4198_, v___y_4190_);
if (lean_obj_tag(v___x_4199_) == 0)
{
lean_object* v_a_4200_; lean_object* v___x_4202_; uint8_t v_isShared_4203_; uint8_t v_isSharedCheck_4209_; 
v_a_4200_ = lean_ctor_get(v___x_4199_, 0);
v_isSharedCheck_4209_ = !lean_is_exclusive(v___x_4199_);
if (v_isSharedCheck_4209_ == 0)
{
v___x_4202_ = v___x_4199_;
v_isShared_4203_ = v_isSharedCheck_4209_;
goto v_resetjp_4201_;
}
else
{
lean_inc(v_a_4200_);
lean_dec(v___x_4199_);
v___x_4202_ = lean_box(0);
v_isShared_4203_ = v_isSharedCheck_4209_;
goto v_resetjp_4201_;
}
v_resetjp_4201_:
{
uint8_t v___x_4204_; 
v___x_4204_ = lean_unbox(v_a_4200_);
lean_dec(v_a_4200_);
if (v___x_4204_ == 0)
{
lean_object* v___x_4205_; lean_object* v___x_4207_; 
v___x_4205_ = lean_box(v___x_4197_);
if (v_isShared_4203_ == 0)
{
lean_ctor_set(v___x_4202_, 0, v___x_4205_);
v___x_4207_ = v___x_4202_;
goto v_reusejp_4206_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v___x_4205_);
v___x_4207_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4206_;
}
v_reusejp_4206_:
{
return v___x_4207_;
}
}
else
{
lean_del_object(v___x_4202_);
goto v___jp_4192_;
}
}
}
else
{
if (lean_obj_tag(v___x_4199_) == 0)
{
lean_object* v_a_4210_; lean_object* v___x_4212_; uint8_t v_isShared_4213_; uint8_t v_isSharedCheck_4219_; 
v_a_4210_ = lean_ctor_get(v___x_4199_, 0);
v_isSharedCheck_4219_ = !lean_is_exclusive(v___x_4199_);
if (v_isSharedCheck_4219_ == 0)
{
v___x_4212_ = v___x_4199_;
v_isShared_4213_ = v_isSharedCheck_4219_;
goto v_resetjp_4211_;
}
else
{
lean_inc(v_a_4210_);
lean_dec(v___x_4199_);
v___x_4212_ = lean_box(0);
v_isShared_4213_ = v_isSharedCheck_4219_;
goto v_resetjp_4211_;
}
v_resetjp_4211_:
{
uint8_t v___x_4214_; 
v___x_4214_ = lean_unbox(v_a_4210_);
lean_dec(v_a_4210_);
if (v___x_4214_ == 0)
{
lean_del_object(v___x_4212_);
goto v___jp_4192_;
}
else
{
lean_object* v___x_4215_; lean_object* v___x_4217_; 
v___x_4215_ = lean_box(v___x_4197_);
if (v_isShared_4213_ == 0)
{
lean_ctor_set_tag(v___x_4212_, 0);
lean_ctor_set(v___x_4212_, 0, v___x_4215_);
v___x_4217_ = v___x_4212_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4218_; 
v_reuseFailAlloc_4218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4218_, 0, v___x_4215_);
v___x_4217_ = v_reuseFailAlloc_4218_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
return v___x_4217_;
}
}
}
}
else
{
return v___x_4199_;
}
}
}
else
{
uint8_t v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; 
v___x_4220_ = 0;
v___x_4221_ = lean_box(v___x_4220_);
v___x_4222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4222_, 0, v___x_4221_);
return v___x_4222_;
}
v___jp_4192_:
{
size_t v___x_4193_; size_t v___x_4194_; 
v___x_4193_ = ((size_t)1ULL);
v___x_4194_ = lean_usize_add(v_i_4187_, v___x_4193_);
v_i_4187_ = v___x_4194_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__2___boxed(lean_object* v_as_4223_, lean_object* v_i_4224_, lean_object* v_stop_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_){
_start:
{
size_t v_i_boxed_4229_; size_t v_stop_boxed_4230_; lean_object* v_res_4231_; 
v_i_boxed_4229_ = lean_unbox_usize(v_i_4224_);
lean_dec(v_i_4224_);
v_stop_boxed_4230_ = lean_unbox_usize(v_stop_4225_);
lean_dec(v_stop_4225_);
v_res_4231_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__2(v_as_4223_, v_i_boxed_4229_, v_stop_boxed_4230_, v___y_4226_, v___y_4227_);
lean_dec(v___y_4227_);
lean_dec_ref(v___y_4226_);
lean_dec_ref(v_as_4223_);
return v_res_4231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler(lean_object* v_declNames_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_){
_start:
{
lean_object* v___x_4236_; lean_object* v___x_4237_; uint8_t v_a_4239_; lean_object* v___y_4280_; uint8_t v___x_4284_; 
v___x_4236_ = lean_unsigned_to_nat(0u);
v___x_4237_ = lean_array_get_size(v_declNames_4232_);
v___x_4284_ = lean_nat_dec_lt(v___x_4236_, v___x_4237_);
if (v___x_4284_ == 0)
{
lean_object* v___x_4285_; 
v___x_4285_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__0(v___x_4284_, v_a_4233_, v_a_4234_);
v___y_4280_ = v___x_4285_;
goto v___jp_4279_;
}
else
{
if (v___x_4284_ == 0)
{
v_a_4239_ = v___x_4284_;
goto v___jp_4238_;
}
else
{
size_t v___x_4286_; size_t v___x_4287_; lean_object* v___x_4288_; 
v___x_4286_ = ((size_t)0ULL);
v___x_4287_ = lean_usize_of_nat(v___x_4237_);
v___x_4288_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__2(v_declNames_4232_, v___x_4286_, v___x_4287_, v_a_4233_, v_a_4234_);
if (lean_obj_tag(v___x_4288_) == 0)
{
lean_object* v_a_4289_; uint8_t v___x_4290_; lean_object* v___x_4291_; 
v_a_4289_ = lean_ctor_get(v___x_4288_, 0);
lean_inc(v_a_4289_);
lean_dec_ref_known(v___x_4288_, 1);
v___x_4290_ = lean_unbox(v_a_4289_);
lean_dec(v_a_4289_);
v___x_4291_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__0(v___x_4290_, v_a_4233_, v_a_4234_);
v___y_4280_ = v___x_4291_;
goto v___jp_4279_;
}
else
{
v___y_4280_ = v___x_4288_;
goto v___jp_4279_;
}
}
}
v___jp_4238_:
{
uint8_t v___x_4240_; 
v___x_4240_ = lean_nat_dec_lt(v___x_4236_, v___x_4237_);
if (v___x_4240_ == 0)
{
lean_object* v___x_4241_; lean_object* v___x_4242_; 
lean_dec_ref(v_declNames_4232_);
v___x_4241_ = lean_box(v___x_4240_);
v___x_4242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4242_, 0, v___x_4241_);
return v___x_4242_;
}
else
{
lean_object* v___x_4243_; lean_object* v___f_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; 
v___x_4243_ = lean_box(v_a_4239_);
v___f_4244_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__1___boxed), 2, 1);
lean_closure_set(v___f_4244_, 0, v___x_4243_);
v___x_4245_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___boxed), 8, 1);
lean_closure_set(v___x_4245_, 0, v_declNames_4232_);
v___x_4246_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftTermElabM___boxed), 5, 2);
lean_closure_set(v___x_4246_, 0, lean_box(0));
lean_closure_set(v___x_4246_, 1, v___x_4245_);
v___x_4247_ = l_Lean_Elab_Command_withFreshMacroScope___redArg(v___x_4246_, v_a_4233_, v_a_4234_);
if (lean_obj_tag(v___x_4247_) == 0)
{
lean_object* v_a_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; 
v_a_4248_ = lean_ctor_get(v___x_4247_, 0);
lean_inc(v_a_4248_);
lean_dec_ref_known(v___x_4247_, 1);
v___x_4249_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_4250_ = lean_box(2);
v___x_4251_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4251_, 0, v___x_4250_);
lean_ctor_set(v___x_4251_, 1, v___x_4249_);
lean_ctor_set(v___x_4251_, 2, v_a_4248_);
v___x_4252_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(v___x_4252_, 0, v___x_4251_);
v___x_4253_ = l_Lean_Elab_Command_withScope___redArg(v___f_4244_, v___x_4252_, v_a_4233_, v_a_4234_);
if (lean_obj_tag(v___x_4253_) == 0)
{
lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4261_; 
v_isSharedCheck_4261_ = !lean_is_exclusive(v___x_4253_);
if (v_isSharedCheck_4261_ == 0)
{
lean_object* v_unused_4262_; 
v_unused_4262_ = lean_ctor_get(v___x_4253_, 0);
lean_dec(v_unused_4262_);
v___x_4255_ = v___x_4253_;
v_isShared_4256_ = v_isSharedCheck_4261_;
goto v_resetjp_4254_;
}
else
{
lean_dec(v___x_4253_);
v___x_4255_ = lean_box(0);
v_isShared_4256_ = v_isSharedCheck_4261_;
goto v_resetjp_4254_;
}
v_resetjp_4254_:
{
lean_object* v___x_4257_; lean_object* v___x_4259_; 
v___x_4257_ = lean_box(v_a_4239_);
if (v_isShared_4256_ == 0)
{
lean_ctor_set(v___x_4255_, 0, v___x_4257_);
v___x_4259_ = v___x_4255_;
goto v_reusejp_4258_;
}
else
{
lean_object* v_reuseFailAlloc_4260_; 
v_reuseFailAlloc_4260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4260_, 0, v___x_4257_);
v___x_4259_ = v_reuseFailAlloc_4260_;
goto v_reusejp_4258_;
}
v_reusejp_4258_:
{
return v___x_4259_;
}
}
}
else
{
lean_object* v_a_4263_; lean_object* v___x_4265_; uint8_t v_isShared_4266_; uint8_t v_isSharedCheck_4270_; 
v_a_4263_ = lean_ctor_get(v___x_4253_, 0);
v_isSharedCheck_4270_ = !lean_is_exclusive(v___x_4253_);
if (v_isSharedCheck_4270_ == 0)
{
v___x_4265_ = v___x_4253_;
v_isShared_4266_ = v_isSharedCheck_4270_;
goto v_resetjp_4264_;
}
else
{
lean_inc(v_a_4263_);
lean_dec(v___x_4253_);
v___x_4265_ = lean_box(0);
v_isShared_4266_ = v_isSharedCheck_4270_;
goto v_resetjp_4264_;
}
v_resetjp_4264_:
{
lean_object* v___x_4268_; 
if (v_isShared_4266_ == 0)
{
v___x_4268_ = v___x_4265_;
goto v_reusejp_4267_;
}
else
{
lean_object* v_reuseFailAlloc_4269_; 
v_reuseFailAlloc_4269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4269_, 0, v_a_4263_);
v___x_4268_ = v_reuseFailAlloc_4269_;
goto v_reusejp_4267_;
}
v_reusejp_4267_:
{
return v___x_4268_;
}
}
}
}
else
{
lean_object* v_a_4271_; lean_object* v___x_4273_; uint8_t v_isShared_4274_; uint8_t v_isSharedCheck_4278_; 
lean_dec_ref(v___f_4244_);
v_a_4271_ = lean_ctor_get(v___x_4247_, 0);
v_isSharedCheck_4278_ = !lean_is_exclusive(v___x_4247_);
if (v_isSharedCheck_4278_ == 0)
{
v___x_4273_ = v___x_4247_;
v_isShared_4274_ = v_isSharedCheck_4278_;
goto v_resetjp_4272_;
}
else
{
lean_inc(v_a_4271_);
lean_dec(v___x_4247_);
v___x_4273_ = lean_box(0);
v_isShared_4274_ = v_isSharedCheck_4278_;
goto v_resetjp_4272_;
}
v_resetjp_4272_:
{
lean_object* v___x_4276_; 
if (v_isShared_4274_ == 0)
{
v___x_4276_ = v___x_4273_;
goto v_reusejp_4275_;
}
else
{
lean_object* v_reuseFailAlloc_4277_; 
v_reuseFailAlloc_4277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4277_, 0, v_a_4271_);
v___x_4276_ = v_reuseFailAlloc_4277_;
goto v_reusejp_4275_;
}
v_reusejp_4275_:
{
return v___x_4276_;
}
}
}
}
}
v___jp_4279_:
{
if (lean_obj_tag(v___y_4280_) == 0)
{
lean_object* v_a_4281_; uint8_t v___x_4282_; 
v_a_4281_ = lean_ctor_get(v___y_4280_, 0);
v___x_4282_ = lean_unbox(v_a_4281_);
if (v___x_4282_ == 0)
{
lean_dec_ref(v_declNames_4232_);
return v___y_4280_;
}
else
{
uint8_t v___x_4283_; 
lean_inc(v_a_4281_);
lean_dec_ref_known(v___y_4280_, 1);
v___x_4283_ = lean_unbox(v_a_4281_);
lean_dec(v_a_4281_);
v_a_4239_ = v___x_4283_;
goto v___jp_4238_;
}
}
else
{
lean_dec_ref(v_declNames_4232_);
return v___y_4280_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___boxed(lean_object* v_declNames_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_){
_start:
{
lean_object* v_res_4296_; 
v_res_4296_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler(v_declNames_4292_, v_a_4293_, v_a_4294_);
lean_dec(v_a_4294_);
lean_dec_ref(v_a_4293_);
return v_res_4296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; 
v___x_4364_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__14));
v___x_4365_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__0_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_));
v___x_4366_ = l_Lean_Elab_registerDerivingHandler(v___x_4364_, v___x_4365_);
if (lean_obj_tag(v___x_4366_) == 0)
{
lean_object* v___x_4367_; uint8_t v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; 
lean_dec_ref_known(v___x_4366_, 1);
v___x_4367_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__0));
v___x_4368_ = 0;
v___x_4369_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__25_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_));
v___x_4370_ = l_Lean_registerTraceClass(v___x_4367_, v___x_4368_, v___x_4369_);
return v___x_4370_;
}
else
{
return v___x_4366_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2____boxed(lean_object* v_a_4371_){
_start:
{
lean_object* v_res_4372_; 
v_res_4372_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_();
return v_res_4372_;
}
}
lean_object* runtime_initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Deriving_ToExpr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
