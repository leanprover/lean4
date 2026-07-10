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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
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
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdent(lean_object*);
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
lean_object* l_Lean_MessageData_ofList(lean_object*);
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
lean_inc_n(v___x_49_, 2);
v___x_55_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_55_, 0, v___x_49_);
lean_ctor_set(v___x_55_, 1, v___x_51_);
lean_ctor_set(v___x_55_, 2, v___x_53_);
lean_ctor_set(v___x_55_, 3, v___x_54_);
v___x_56_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
lean_inc(v___x_48_);
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
lean_dec_ref(v___y_67_);
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
lean_dec_ref(v_a_95_);
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
lean_dec_ref(v___y_115_);
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
v___x_145_ = l_Lean_mkIdent(v_v_142_);
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
lean_dec_ref_known(v___x_216_, 1);
if (lean_obj_tag(v_val_218_) == 1)
{
uint8_t v_v_219_; 
v_v_219_ = lean_ctor_get_uint8(v_val_218_, 0);
lean_dec_ref_known(v_val_218_, 0);
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
lean_object* v_options_234_; lean_object* v___x_235_; uint8_t v___x_236_; uint8_t v___x_237_; 
v_options_234_ = lean_ctor_get(v___y_232_, 2);
v___x_235_ = l_Lean_Elab_pp_macroStack;
v___x_236_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__2(v_options_234_, v___x_235_);
v___x_237_ = lean_bool_not(v___x_236_);
if (v___x_237_ == 0)
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
else
{
lean_object* v___x_257_; 
lean_dec(v_macroStack_231_);
v___x_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_257_, 0, v_msgData_230_);
return v___x_257_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_258_, lean_object* v_macroStack_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg(v_msgData_258_, v_macroStack_259_, v___y_260_);
lean_dec_ref(v___y_260_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(lean_object* v_msg_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v_ref_271_; lean_object* v___x_272_; lean_object* v_a_273_; lean_object* v_macroStack_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_285_; 
v_ref_271_ = lean_ctor_get(v___y_268_, 5);
v___x_272_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__0(v_msg_263_, v___y_266_, v___y_267_, v___y_268_, v___y_269_);
v_a_273_ = lean_ctor_get(v___x_272_, 0);
lean_inc(v_a_273_);
lean_dec_ref(v___x_272_);
v_macroStack_274_ = lean_ctor_get(v___y_264_, 1);
v___x_275_ = l_Lean_Elab_getBetterRef(v_ref_271_, v_macroStack_274_);
lean_inc(v_macroStack_274_);
v___x_276_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg(v_a_273_, v_macroStack_274_, v___y_268_);
v_a_277_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_285_ == 0)
{
v___x_279_ = v___x_276_;
v_isShared_280_ = v_isSharedCheck_285_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_276_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_285_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_281_; lean_object* v___x_283_; 
v___x_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_275_);
lean_ctor_set(v___x_281_, 1, v_a_277_);
if (v_isShared_280_ == 0)
{
lean_ctor_set_tag(v___x_279_, 1);
lean_ctor_set(v___x_279_, 0, v___x_281_);
v___x_283_ = v___x_279_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_281_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg___boxed(lean_object* v_msg_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v_msg_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
return v_res_294_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__1(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__0));
v___x_297_ = l_Lean_stringToMessageData(v___x_296_);
return v___x_297_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8(void){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l_Array_mkArray0(lean_box(0));
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType(lean_object* v_indVal_315_, lean_object* v_t_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v_toConstantVal_324_; lean_object* v_levelParams_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_373_; 
v_toConstantVal_324_ = lean_ctor_get(v_indVal_315_, 0);
lean_inc_ref(v_toConstantVal_324_);
lean_dec_ref(v_indVal_315_);
v_levelParams_325_ = lean_ctor_get(v_toConstantVal_324_, 1);
v_isSharedCheck_373_ = !lean_is_exclusive(v_toConstantVal_324_);
if (v_isSharedCheck_373_ == 0)
{
lean_object* v_unused_374_; lean_object* v_unused_375_; 
v_unused_374_ = lean_ctor_get(v_toConstantVal_324_, 2);
lean_dec(v_unused_374_);
v_unused_375_ = lean_ctor_get(v_toConstantVal_324_, 0);
lean_dec(v_unused_375_);
v___x_327_ = v_toConstantVal_324_;
v_isShared_328_ = v_isSharedCheck_373_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_levelParams_325_);
lean_dec(v_toConstantVal_324_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_373_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_329_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
lean_inc(v_t_316_);
v___x_330_ = l_Lean_Syntax_isOfKind(v_t_316_, v___x_329_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; lean_object* v___x_332_; 
lean_del_object(v___x_327_);
lean_dec(v_levelParams_325_);
lean_dec(v_t_316_);
v___x_331_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__1, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__1_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__1);
v___x_332_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v___x_331_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
return v___x_332_;
}
else
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_333_ = lean_unsigned_to_nat(0u);
v___x_334_ = l_Lean_Syntax_getArg(v_t_316_, v___x_333_);
v___x_335_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__3));
lean_inc(v___x_334_);
v___x_336_ = l_Lean_Syntax_isOfKind(v___x_334_, v___x_335_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; lean_object* v___x_338_; 
lean_dec(v___x_334_);
lean_del_object(v___x_327_);
lean_dec(v_levelParams_325_);
lean_dec(v_t_316_);
v___x_337_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__1, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__1_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__1);
v___x_338_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v___x_337_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
return v___x_338_;
}
else
{
lean_object* v_ref_339_; lean_object* v___x_340_; size_t v_sz_341_; size_t v___x_342_; lean_object* v_levels_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v_args_347_; uint8_t v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; size_t v_sz_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_363_; 
v_ref_339_ = lean_ctor_get(v_a_321_, 5);
v___x_340_ = lean_array_mk(v_levelParams_325_);
v_sz_341_ = lean_array_size(v___x_340_);
v___x_342_ = ((size_t)0ULL);
v_levels_343_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__1(v_sz_341_, v___x_342_, v___x_340_);
v___x_344_ = lean_unsigned_to_nat(1u);
v___x_345_ = l_Lean_Syntax_getArg(v___x_334_, v___x_344_);
lean_dec(v___x_334_);
v___x_346_ = l_Lean_Syntax_getArg(v_t_316_, v___x_344_);
lean_dec(v_t_316_);
v_args_347_ = l_Lean_Syntax_getArgs(v___x_346_);
lean_dec(v___x_346_);
v___x_348_ = 0;
v___x_349_ = l_Lean_SourceInfo_fromRef(v_ref_339_, v___x_348_);
v___x_350_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__4));
lean_inc_n(v___x_349_, 3);
v___x_351_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_351_, 0, v___x_349_);
lean_ctor_set(v___x_351_, 1, v___x_350_);
v___x_352_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__6));
v___x_353_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__7));
v___x_354_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_349_);
lean_ctor_set(v___x_354_, 1, v___x_353_);
v___x_355_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_356_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_357_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__9));
v_sz_358_ = lean_array_size(v_levels_343_);
v___x_359_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__2(v_sz_358_, v___x_342_, v_levels_343_);
v___x_360_ = l_Lean_Syntax_SepArray_ofElems(v___x_357_, v___x_359_);
lean_dec_ref(v___x_359_);
v___x_361_ = l_Array_append___redArg(v___x_356_, v___x_360_);
lean_dec_ref(v___x_360_);
if (v_isShared_328_ == 0)
{
lean_ctor_set_tag(v___x_327_, 1);
lean_ctor_set(v___x_327_, 2, v___x_361_);
lean_ctor_set(v___x_327_, 1, v___x_355_);
lean_ctor_set(v___x_327_, 0, v___x_349_);
v___x_363_ = v___x_327_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_349_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v___x_355_);
lean_ctor_set(v_reuseFailAlloc_372_, 2, v___x_361_);
v___x_363_ = v_reuseFailAlloc_372_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_364_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__10));
lean_inc_n(v___x_349_, 4);
v___x_365_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_365_, 0, v___x_349_);
lean_ctor_set(v___x_365_, 1, v___x_364_);
v___x_366_ = l_Lean_Syntax_node4(v___x_349_, v___x_352_, v___x_345_, v___x_354_, v___x_363_, v___x_365_);
v___x_367_ = l_Lean_Syntax_node2(v___x_349_, v___x_335_, v___x_351_, v___x_366_);
v___x_368_ = l_Array_append___redArg(v___x_356_, v_args_347_);
lean_dec_ref(v_args_347_);
v___x_369_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_369_, 0, v___x_349_);
lean_ctor_set(v___x_369_, 1, v___x_355_);
lean_ctor_set(v___x_369_, 2, v___x_368_);
v___x_370_ = l_Lean_Syntax_node2(v___x_349_, v___x_329_, v___x_367_, v___x_369_);
v___x_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
return v___x_371_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___boxed(lean_object* v_indVal_376_, lean_object* v_t_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType(v_indVal_376_, v_t_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_);
lean_dec(v_a_383_);
lean_dec_ref(v_a_382_);
lean_dec(v_a_381_);
lean_dec_ref(v_a_380_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0(lean_object* v_00_u03b1_386_, lean_object* v_msg_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v_msg_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___boxed(lean_object* v_00_u03b1_396_, lean_object* v_msg_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0(v_00_u03b1_396_, v_msg_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1(lean_object* v_msgData_406_, lean_object* v_macroStack_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg(v_msgData_406_, v_macroStack_407_, v___y_412_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___boxed(lean_object* v_msgData_416_, lean_object* v_macroStack_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1(v_msgData_416_, v_macroStack_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg___lam__0(lean_object* v_k_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v_b_429_, lean_object* v_c_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v___x_436_; 
lean_inc(v___y_434_);
lean_inc_ref(v___y_433_);
lean_inc(v___y_432_);
lean_inc_ref(v___y_431_);
lean_inc(v___y_428_);
lean_inc_ref(v___y_427_);
v___x_436_ = lean_apply_9(v_k_426_, v_b_429_, v_c_430_, v___y_427_, v___y_428_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, lean_box(0));
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg___lam__0___boxed(lean_object* v_k_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v_b_440_, lean_object* v_c_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg___lam__0(v_k_437_, v___y_438_, v___y_439_, v_b_440_, v_c_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg(lean_object* v_type_448_, lean_object* v_k_449_, uint8_t v_cleanupAnnotations_450_, uint8_t v_whnfType_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v___f_459_; lean_object* v___x_460_; 
lean_inc(v___y_453_);
lean_inc_ref(v___y_452_);
v___f_459_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_459_, 0, v_k_449_);
lean_closure_set(v___f_459_, 1, v___y_452_);
lean_closure_set(v___f_459_, 2, v___y_453_);
v___x_460_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_448_, v___f_459_, v_cleanupAnnotations_450_, v_whnfType_451_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
if (lean_obj_tag(v___x_460_) == 0)
{
return v___x_460_;
}
else
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v___x_460_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_460_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_461_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg___boxed(lean_object* v_type_469_, lean_object* v_k_470_, lean_object* v_cleanupAnnotations_471_, lean_object* v_whnfType_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_480_; uint8_t v_whnfType_boxed_481_; lean_object* v_res_482_; 
v_cleanupAnnotations_boxed_480_ = lean_unbox(v_cleanupAnnotations_471_);
v_whnfType_boxed_481_ = lean_unbox(v_whnfType_472_);
v_res_482_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg(v_type_469_, v_k_470_, v_cleanupAnnotations_boxed_480_, v_whnfType_boxed_481_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2(lean_object* v_00_u03b1_483_, lean_object* v_type_484_, lean_object* v_k_485_, uint8_t v_cleanupAnnotations_486_, uint8_t v_whnfType_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg(v_type_484_, v_k_485_, v_cleanupAnnotations_486_, v_whnfType_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___boxed(lean_object* v_00_u03b1_496_, lean_object* v_type_497_, lean_object* v_k_498_, lean_object* v_cleanupAnnotations_499_, lean_object* v_whnfType_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_508_; uint8_t v_whnfType_boxed_509_; lean_object* v_res_510_; 
v_cleanupAnnotations_boxed_508_ = lean_unbox(v_cleanupAnnotations_499_);
v_whnfType_boxed_509_ = lean_unbox(v_whnfType_500_);
v_res_510_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2(v_00_u03b1_496_, v_type_497_, v_k_498_, v_cleanupAnnotations_boxed_508_, v_whnfType_boxed_509_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
return v_res_510_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__0));
v___x_513_ = l_String_toRawSubstring_x27(v___x_512_);
return v___x_513_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__7));
v___x_529_ = l_String_toRawSubstring_x27(v___x_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg(lean_object* v_as_542_, size_t v_sz_543_, size_t v_i_544_, lean_object* v_b_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
uint8_t v___x_551_; 
v___x_551_ = lean_usize_dec_lt(v_i_544_, v_sz_543_);
if (v___x_551_ == 0)
{
lean_object* v___x_552_; 
v___x_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_552_, 0, v_b_545_);
return v___x_552_;
}
else
{
lean_object* v_snd_553_; lean_object* v_fst_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_633_; 
v_snd_553_ = lean_ctor_get(v_b_545_, 1);
v_fst_554_ = lean_ctor_get(v_b_545_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v_b_545_);
if (v_isSharedCheck_633_ == 0)
{
v___x_556_ = v_b_545_;
v_isShared_557_ = v_isSharedCheck_633_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_snd_553_);
lean_inc(v_fst_554_);
lean_dec(v_b_545_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_633_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v_array_558_; lean_object* v_start_559_; lean_object* v_stop_560_; uint8_t v___x_561_; 
v_array_558_ = lean_ctor_get(v_snd_553_, 0);
v_start_559_ = lean_ctor_get(v_snd_553_, 1);
v_stop_560_ = lean_ctor_get(v_snd_553_, 2);
v___x_561_ = lean_nat_dec_lt(v_start_559_, v_stop_560_);
if (v___x_561_ == 0)
{
lean_object* v___x_563_; 
if (v_isShared_557_ == 0)
{
v___x_563_ = v___x_556_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_fst_554_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v_snd_553_);
v___x_563_ = v_reuseFailAlloc_565_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
lean_object* v___x_564_; 
v___x_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
return v___x_564_;
}
}
else
{
lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_629_; 
lean_inc(v_stop_560_);
lean_inc(v_start_559_);
lean_inc_ref(v_array_558_);
v_isSharedCheck_629_ = !lean_is_exclusive(v_snd_553_);
if (v_isSharedCheck_629_ == 0)
{
lean_object* v_unused_630_; lean_object* v_unused_631_; lean_object* v_unused_632_; 
v_unused_630_ = lean_ctor_get(v_snd_553_, 2);
lean_dec(v_unused_630_);
v_unused_631_ = lean_ctor_get(v_snd_553_, 1);
lean_dec(v_unused_631_);
v_unused_632_ = lean_ctor_get(v_snd_553_, 0);
lean_dec(v_unused_632_);
v___x_567_ = v_snd_553_;
v_isShared_568_ = v_isSharedCheck_629_;
goto v_resetjp_566_;
}
else
{
lean_dec(v_snd_553_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_629_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = lean_array_fget_borrowed(v_array_558_, v_start_559_);
lean_inc(v___x_569_);
v___x_570_ = l_Lean_Meta_isType(v___x_569_, v___y_546_, v___y_547_, v___y_548_, v___y_549_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; lean_object* v_a_573_; lean_object* v_a_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_581_; 
v_a_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_a_571_);
lean_dec_ref_known(v___x_570_, 1);
v_a_577_ = lean_array_uget_borrowed(v_as_542_, v_i_544_);
v___x_578_ = lean_unsigned_to_nat(1u);
v___x_579_ = lean_nat_add(v_start_559_, v___x_578_);
lean_dec(v_start_559_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 1, v___x_579_);
v___x_581_ = v___x_567_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_array_558_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v___x_579_);
lean_ctor_set(v_reuseFailAlloc_620_, 2, v_stop_560_);
v___x_581_ = v_reuseFailAlloc_620_;
goto v_reusejp_580_;
}
v___jp_572_:
{
size_t v___x_574_; size_t v___x_575_; 
v___x_574_ = ((size_t)1ULL);
v___x_575_ = lean_usize_add(v_i_544_, v___x_574_);
v_i_544_ = v___x_575_;
v_b_545_ = v_a_573_;
goto _start;
}
v_reusejp_580_:
{
lean_object* v___x_582_; uint8_t v___x_583_; 
lean_inc(v_a_577_);
v___x_582_ = l_Lean_mkIdent(v_a_577_);
v___x_583_ = lean_unbox(v_a_571_);
if (v___x_583_ == 0)
{
lean_object* v_ref_584_; lean_object* v_quotContext_585_; lean_object* v_currMacroScope_586_; uint8_t v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_600_; 
v_ref_584_ = lean_ctor_get(v___y_548_, 5);
v_quotContext_585_ = lean_ctor_get(v___y_548_, 10);
v_currMacroScope_586_ = lean_ctor_get(v___y_548_, 11);
v___x_587_ = lean_unbox(v_a_571_);
lean_dec(v_a_571_);
v___x_588_ = l_Lean_SourceInfo_fromRef(v_ref_584_, v___x_587_);
v___x_589_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_590_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1);
v___x_591_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__2));
lean_inc(v_currMacroScope_586_);
lean_inc(v_quotContext_585_);
v___x_592_ = l_Lean_addMacroScope(v_quotContext_585_, v___x_591_, v_currMacroScope_586_);
v___x_593_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__6));
lean_inc_n(v___x_588_, 2);
v___x_594_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_594_, 0, v___x_588_);
lean_ctor_set(v___x_594_, 1, v___x_590_);
lean_ctor_set(v___x_594_, 2, v___x_592_);
lean_ctor_set(v___x_594_, 3, v___x_593_);
v___x_595_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_596_ = l_Lean_Syntax_node1(v___x_588_, v___x_595_, v___x_582_);
v___x_597_ = l_Lean_Syntax_node2(v___x_588_, v___x_589_, v___x_594_, v___x_596_);
v___x_598_ = lean_array_push(v_fst_554_, v___x_597_);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 1, v___x_581_);
lean_ctor_set(v___x_556_, 0, v___x_598_);
v___x_600_ = v___x_556_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_598_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v___x_581_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
v_a_573_ = v___x_600_;
goto v___jp_572_;
}
}
else
{
lean_object* v_ref_602_; lean_object* v_quotContext_603_; lean_object* v_currMacroScope_604_; uint8_t v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_618_; 
lean_dec(v_a_571_);
v_ref_602_ = lean_ctor_get(v___y_548_, 5);
v_quotContext_603_ = lean_ctor_get(v___y_548_, 10);
v_currMacroScope_604_ = lean_ctor_get(v___y_548_, 11);
v___x_605_ = 0;
v___x_606_ = l_Lean_SourceInfo_fromRef(v_ref_602_, v___x_605_);
v___x_607_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_608_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8);
v___x_609_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__9));
lean_inc(v_currMacroScope_604_);
lean_inc(v_quotContext_603_);
v___x_610_ = l_Lean_addMacroScope(v_quotContext_603_, v___x_609_, v_currMacroScope_604_);
v___x_611_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__12));
lean_inc_n(v___x_606_, 2);
v___x_612_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_612_, 0, v___x_606_);
lean_ctor_set(v___x_612_, 1, v___x_608_);
lean_ctor_set(v___x_612_, 2, v___x_610_);
lean_ctor_set(v___x_612_, 3, v___x_611_);
v___x_613_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_614_ = l_Lean_Syntax_node1(v___x_606_, v___x_613_, v___x_582_);
v___x_615_ = l_Lean_Syntax_node2(v___x_606_, v___x_607_, v___x_612_, v___x_614_);
v___x_616_ = lean_array_push(v_fst_554_, v___x_615_);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 1, v___x_581_);
lean_ctor_set(v___x_556_, 0, v___x_616_);
v___x_618_ = v___x_556_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_616_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v___x_581_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
v_a_573_ = v___x_618_;
goto v___jp_572_;
}
}
}
}
else
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
lean_del_object(v___x_567_);
lean_dec(v_stop_560_);
lean_dec(v_start_559_);
lean_dec_ref(v_array_558_);
lean_del_object(v___x_556_);
lean_dec(v_fst_554_);
v_a_621_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_628_ == 0)
{
v___x_623_ = v___x_570_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_570_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_621_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___boxed(lean_object* v_as_634_, lean_object* v_sz_635_, lean_object* v_i_636_, lean_object* v_b_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
size_t v_sz_boxed_643_; size_t v_i_boxed_644_; lean_object* v_res_645_; 
v_sz_boxed_643_ = lean_unbox_usize(v_sz_635_);
lean_dec(v_sz_635_);
v_i_boxed_644_ = lean_unbox_usize(v_i_636_);
lean_dec(v_i_636_);
v_res_645_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg(v_as_634_, v_sz_boxed_643_, v_i_boxed_644_, v_b_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec_ref(v_as_634_);
return v_res_645_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__1));
v___x_650_ = l_String_toRawSubstring_x27(v___x_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0(lean_object* v_argNames_686_, size_t v___x_687_, lean_object* v_a_688_, lean_object* v_name_689_, lean_object* v_xs_690_, lean_object* v_x_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; size_t v_sz_704_; lean_object* v___x_705_; 
v___x_699_ = lean_unsigned_to_nat(0u);
v___x_700_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__0));
v___x_701_ = lean_array_get_size(v_xs_690_);
v___x_702_ = l_Array_toSubarray___redArg(v_xs_690_, v___x_699_, v___x_701_);
v___x_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_700_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
v_sz_704_ = lean_array_size(v_argNames_686_);
v___x_705_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg(v_argNames_686_, v_sz_704_, v___x_687_, v___x_703_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; lean_object* v_fst_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_756_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_a_706_);
lean_dec_ref_known(v___x_705_, 1);
v_fst_707_ = lean_ctor_get(v_a_706_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v_a_706_);
if (v_isSharedCheck_756_ == 0)
{
lean_object* v_unused_757_; 
v_unused_757_ = lean_ctor_get(v_a_706_, 1);
lean_dec(v_unused_757_);
v___x_709_ = v_a_706_;
v_isShared_710_ = v_isSharedCheck_756_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_fst_707_);
lean_dec(v_a_706_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_756_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v_ref_711_; lean_object* v_quotContext_712_; lean_object* v_currMacroScope_713_; uint8_t v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___y_725_; lean_object* v___x_742_; 
v_ref_711_ = lean_ctor_get(v___y_696_, 5);
v_quotContext_712_ = lean_ctor_get(v___y_696_, 10);
v_currMacroScope_713_ = lean_ctor_get(v___y_696_, 11);
v___x_714_ = 0;
v___x_715_ = l_Lean_SourceInfo_fromRef(v_ref_711_, v___x_714_);
v___x_716_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_717_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__2, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__2_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__2);
v___x_718_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__4));
lean_inc(v_currMacroScope_713_);
lean_inc(v_quotContext_712_);
v___x_719_ = l_Lean_addMacroScope(v_quotContext_712_, v___x_718_, v_currMacroScope_713_);
v___x_720_ = lean_box(0);
v___x_721_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__10));
lean_inc(v___x_715_);
v___x_722_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_722_, 0, v___x_715_);
lean_ctor_set(v___x_722_, 1, v___x_717_);
lean_ctor_set(v___x_722_, 2, v___x_719_);
lean_ctor_set(v___x_722_, 3, v___x_721_);
v___x_723_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
lean_inc(v_name_689_);
v___x_742_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_720_, v_name_689_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v___x_743_; 
v___x_743_ = l_Lean_quoteNameMk(v_name_689_);
v___y_725_ = v___x_743_;
goto v___jp_724_;
}
else
{
lean_object* v_val_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
lean_dec(v_name_689_);
v_val_744_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_val_744_);
lean_dec_ref_known(v___x_742_, 1);
v___x_745_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__16));
v___x_746_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__17));
v___x_747_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__18));
v___x_748_ = lean_string_intercalate(v___x_747_, v_val_744_);
v___x_749_ = lean_string_append(v___x_746_, v___x_748_);
lean_dec_ref(v___x_748_);
v___x_750_ = lean_box(2);
v___x_751_ = l_Lean_Syntax_mkNameLit(v___x_749_, v___x_750_);
v___x_752_ = lean_unsigned_to_nat(1u);
v___x_753_ = lean_mk_empty_array_with_capacity(v___x_752_);
v___x_754_ = lean_array_push(v___x_753_, v___x_751_);
v___x_755_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_755_, 0, v___x_750_);
lean_ctor_set(v___x_755_, 1, v___x_745_);
lean_ctor_set(v___x_755_, 2, v___x_754_);
v___y_725_ = v___x_755_;
goto v___jp_724_;
}
v___jp_724_:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_729_; 
v___x_726_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__12));
v___x_727_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__13));
lean_inc(v___x_715_);
if (v_isShared_710_ == 0)
{
lean_ctor_set_tag(v___x_709_, 2);
lean_ctor_set(v___x_709_, 1, v___x_727_);
lean_ctor_set(v___x_709_, 0, v___x_715_);
v___x_729_ = v___x_709_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v___x_727_);
v___x_729_ = v_reuseFailAlloc_741_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_730_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_731_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__9));
v___x_732_ = l_Lean_Syntax_SepArray_ofElems(v___x_731_, v_a_688_);
v___x_733_ = l_Array_append___redArg(v___x_730_, v___x_732_);
lean_dec_ref(v___x_732_);
lean_inc_n(v___x_715_, 4);
v___x_734_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_734_, 0, v___x_715_);
lean_ctor_set(v___x_734_, 1, v___x_723_);
lean_ctor_set(v___x_734_, 2, v___x_733_);
v___x_735_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__14));
v___x_736_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_715_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v___x_737_ = l_Lean_Syntax_node3(v___x_715_, v___x_726_, v___x_729_, v___x_734_, v___x_736_);
v___x_738_ = l_Lean_Syntax_node2(v___x_715_, v___x_723_, v___y_725_, v___x_737_);
v___x_739_ = l_Lean_Syntax_node2(v___x_715_, v___x_716_, v___x_722_, v___x_738_);
v___x_740_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm(v___x_739_, v_fst_707_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
lean_dec(v_fst_707_);
return v___x_740_;
}
}
}
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_dec(v_name_689_);
v_a_758_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_705_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_705_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___boxed(lean_object* v_argNames_766_, lean_object* v___x_767_, lean_object* v_a_768_, lean_object* v_name_769_, lean_object* v_xs_770_, lean_object* v_x_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
size_t v___x_11663__boxed_779_; lean_object* v_res_780_; 
v___x_11663__boxed_779_ = lean_unbox_usize(v___x_767_);
lean_dec(v___x_767_);
v_res_780_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0(v_argNames_766_, v___x_11663__boxed_779_, v_a_768_, v_name_769_, v_xs_770_, v_x_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec_ref(v_x_771_);
lean_dec_ref(v_a_768_);
lean_dec_ref(v_argNames_766_);
return v_res_780_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_782_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__0));
v___x_783_ = l_String_toRawSubstring_x27(v___x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg(size_t v_sz_799_, size_t v_i_800_, lean_object* v_bs_801_, lean_object* v___y_802_){
_start:
{
uint8_t v___x_804_; 
v___x_804_ = lean_usize_dec_lt(v_i_800_, v_sz_799_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; 
v___x_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_805_, 0, v_bs_801_);
return v___x_805_;
}
else
{
lean_object* v_ref_806_; lean_object* v_quotContext_807_; lean_object* v_currMacroScope_808_; lean_object* v_v_809_; lean_object* v___x_810_; lean_object* v_bs_x27_811_; uint8_t v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; size_t v___x_828_; size_t v___x_829_; lean_object* v___x_830_; 
v_ref_806_ = lean_ctor_get(v___y_802_, 5);
v_quotContext_807_ = lean_ctor_get(v___y_802_, 10);
v_currMacroScope_808_ = lean_ctor_get(v___y_802_, 11);
v_v_809_ = lean_array_uget(v_bs_801_, v_i_800_);
v___x_810_ = lean_unsigned_to_nat(0u);
v_bs_x27_811_ = lean_array_uset(v_bs_801_, v_i_800_, v___x_810_);
v___x_812_ = 0;
v___x_813_ = l_Lean_SourceInfo_fromRef(v_ref_806_, v___x_812_);
v___x_814_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__6));
v___x_815_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__1);
v___x_816_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__3));
lean_inc(v_currMacroScope_808_);
lean_inc(v_quotContext_807_);
v___x_817_ = l_Lean_addMacroScope(v_quotContext_807_, v___x_816_, v_currMacroScope_808_);
v___x_818_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__7));
lean_inc_n(v___x_813_, 4);
v___x_819_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_819_, 0, v___x_813_);
lean_ctor_set(v___x_819_, 1, v___x_815_);
lean_ctor_set(v___x_819_, 2, v___x_817_);
lean_ctor_set(v___x_819_, 3, v___x_818_);
v___x_820_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__7));
v___x_821_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_813_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
v___x_822_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_823_ = l_Lean_mkIdent(v_v_809_);
v___x_824_ = l_Lean_Syntax_node1(v___x_813_, v___x_822_, v___x_823_);
v___x_825_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__10));
v___x_826_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_813_);
lean_ctor_set(v___x_826_, 1, v___x_825_);
v___x_827_ = l_Lean_Syntax_node4(v___x_813_, v___x_814_, v___x_819_, v___x_821_, v___x_824_, v___x_826_);
v___x_828_ = ((size_t)1ULL);
v___x_829_ = lean_usize_add(v_i_800_, v___x_828_);
v___x_830_ = lean_array_uset(v_bs_x27_811_, v_i_800_, v___x_827_);
v_i_800_ = v___x_829_;
v_bs_801_ = v___x_830_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___boxed(lean_object* v_sz_832_, lean_object* v_i_833_, lean_object* v_bs_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
size_t v_sz_boxed_837_; size_t v_i_boxed_838_; lean_object* v_res_839_; 
v_sz_boxed_837_ = lean_unbox_usize(v_sz_832_);
lean_dec(v_sz_832_);
v_i_boxed_838_ = lean_unbox_usize(v_i_833_);
lean_dec(v_i_833_);
v_res_839_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg(v_sz_boxed_837_, v_i_boxed_838_, v_bs_834_, v___y_835_);
lean_dec_ref(v___y_835_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr(lean_object* v_indVal_842_, lean_object* v_argNames_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
lean_object* v_toConstantVal_851_; lean_object* v_name_852_; lean_object* v_levelParams_853_; lean_object* v_type_854_; lean_object* v___x_855_; size_t v_sz_856_; size_t v___x_857_; lean_object* v___x_858_; 
v_toConstantVal_851_ = lean_ctor_get(v_indVal_842_, 0);
lean_inc_ref(v_toConstantVal_851_);
lean_dec_ref(v_indVal_842_);
v_name_852_ = lean_ctor_get(v_toConstantVal_851_, 0);
lean_inc(v_name_852_);
v_levelParams_853_ = lean_ctor_get(v_toConstantVal_851_, 1);
lean_inc(v_levelParams_853_);
v_type_854_ = lean_ctor_get(v_toConstantVal_851_, 2);
lean_inc_ref(v_type_854_);
lean_dec_ref(v_toConstantVal_851_);
v___x_855_ = lean_array_mk(v_levelParams_853_);
v_sz_856_ = lean_array_size(v___x_855_);
v___x_857_ = ((size_t)0ULL);
v___x_858_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg(v_sz_856_, v___x_857_, v___x_855_, v_a_848_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; lean_object* v___x_860_; lean_object* v___f_861_; uint8_t v___x_862_; lean_object* v___x_863_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_a_859_);
lean_dec_ref_known(v___x_858_, 1);
v___x_860_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___boxed__const__1));
v___f_861_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___boxed), 13, 4);
lean_closure_set(v___f_861_, 0, v_argNames_843_);
lean_closure_set(v___f_861_, 1, v___x_860_);
lean_closure_set(v___f_861_, 2, v_a_859_);
lean_closure_set(v___f_861_, 3, v_name_852_);
v___x_862_ = 0;
v___x_863_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg(v_type_854_, v___f_861_, v___x_862_, v___x_862_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
return v___x_863_;
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
lean_dec_ref(v_type_854_);
lean_dec(v_name_852_);
lean_dec_ref(v_argNames_843_);
v_a_864_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_858_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_858_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_864_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___boxed(lean_object* v_indVal_872_, lean_object* v_argNames_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr(v_indVal_872_, v_argNames_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
lean_dec(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0(size_t v_sz_882_, size_t v_i_883_, lean_object* v_bs_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg(v_sz_882_, v_i_883_, v_bs_884_, v___y_889_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___boxed(lean_object* v_sz_893_, lean_object* v_i_894_, lean_object* v_bs_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
size_t v_sz_boxed_903_; size_t v_i_boxed_904_; lean_object* v_res_905_; 
v_sz_boxed_903_ = lean_unbox_usize(v_sz_893_);
lean_dec(v_sz_893_);
v_i_boxed_904_ = lean_unbox_usize(v_i_894_);
lean_dec(v_i_894_);
v_res_905_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0(v_sz_boxed_903_, v_i_boxed_904_, v_bs_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1(lean_object* v_as_906_, size_t v_sz_907_, size_t v_i_908_, lean_object* v_b_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg(v_as_906_, v_sz_907_, v_i_908_, v_b_909_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___boxed(lean_object* v_as_918_, lean_object* v_sz_919_, lean_object* v_i_920_, lean_object* v_b_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
size_t v_sz_boxed_929_; size_t v_i_boxed_930_; lean_object* v_res_931_; 
v_sz_boxed_929_ = lean_unbox_usize(v_sz_919_);
lean_dec(v_sz_919_);
v_i_boxed_930_ = lean_unbox_usize(v_i_920_);
lean_dec(v_i_920_);
v_res_931_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1(v_as_918_, v_sz_boxed_929_, v_i_boxed_930_, v_b_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec_ref(v_as_918_);
return v_res_931_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__2));
v___x_939_ = l_String_toRawSubstring_x27(v___x_938_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg(size_t v_sz_942_, size_t v_i_943_, lean_object* v_bs_944_, lean_object* v___y_945_){
_start:
{
uint8_t v___x_947_; 
v___x_947_ = lean_usize_dec_lt(v_i_943_, v_sz_942_);
if (v___x_947_ == 0)
{
lean_object* v___x_948_; 
v___x_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_948_, 0, v_bs_944_);
return v___x_948_;
}
else
{
lean_object* v_ref_949_; lean_object* v_quotContext_950_; lean_object* v_currMacroScope_951_; lean_object* v_v_952_; lean_object* v___x_953_; lean_object* v_bs_x27_954_; uint8_t v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; size_t v___x_966_; size_t v___x_967_; lean_object* v___x_968_; 
v_ref_949_ = lean_ctor_get(v___y_945_, 5);
v_quotContext_950_ = lean_ctor_get(v___y_945_, 10);
v_currMacroScope_951_ = lean_ctor_get(v___y_945_, 11);
v_v_952_ = lean_array_uget(v_bs_944_, v_i_943_);
v___x_953_ = lean_unsigned_to_nat(0u);
v_bs_x27_954_ = lean_array_uset(v_bs_944_, v_i_943_, v___x_953_);
v___x_955_ = 0;
v___x_956_ = l_Lean_SourceInfo_fromRef(v_ref_949_, v___x_955_);
v___x_957_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__1));
v___x_958_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__18));
lean_inc_n(v___x_956_, 2);
v___x_959_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_956_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
v___x_960_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__2);
v___x_961_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__3));
lean_inc(v_currMacroScope_951_);
lean_inc(v_quotContext_950_);
v___x_962_ = l_Lean_addMacroScope(v_quotContext_950_, v___x_961_, v_currMacroScope_951_);
v___x_963_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__7));
v___x_964_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_964_, 0, v___x_956_);
lean_ctor_set(v___x_964_, 1, v___x_960_);
lean_ctor_set(v___x_964_, 2, v___x_962_);
lean_ctor_set(v___x_964_, 3, v___x_963_);
v___x_965_ = l_Lean_Syntax_node3(v___x_956_, v___x_957_, v_v_952_, v___x_959_, v___x_964_);
v___x_966_ = ((size_t)1ULL);
v___x_967_ = lean_usize_add(v_i_943_, v___x_966_);
v___x_968_ = lean_array_uset(v_bs_x27_954_, v_i_943_, v___x_965_);
v_i_943_ = v___x_967_;
v_bs_944_ = v___x_968_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___boxed(lean_object* v_sz_970_, lean_object* v_i_971_, lean_object* v_bs_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
size_t v_sz_boxed_975_; size_t v_i_boxed_976_; lean_object* v_res_977_; 
v_sz_boxed_975_ = lean_unbox_usize(v_sz_970_);
lean_dec(v_sz_970_);
v_i_boxed_976_ = lean_unbox_usize(v_i_971_);
lean_dec(v_i_971_);
v_res_977_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg(v_sz_boxed_975_, v_i_boxed_976_, v_bs_972_, v___y_973_);
lean_dec_ref(v___y_973_);
return v_res_977_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l_instMonadEIO(lean_box(0));
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1(lean_object* v_msg_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v_toApplicative_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1086_; 
v___x_993_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__0);
v___x_994_ = l_StateRefT_x27_instMonad___redArg(v___x_993_);
v_toApplicative_995_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1086_ == 0)
{
lean_object* v_unused_1087_; 
v_unused_1087_ = lean_ctor_get(v___x_994_, 1);
lean_dec(v_unused_1087_);
v___x_997_ = v___x_994_;
v_isShared_998_ = v_isSharedCheck_1086_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_toApplicative_995_);
lean_dec(v___x_994_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1086_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v_toFunctor_999_; lean_object* v_toSeq_1000_; lean_object* v_toSeqLeft_1001_; lean_object* v_toSeqRight_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1084_; 
v_toFunctor_999_ = lean_ctor_get(v_toApplicative_995_, 0);
v_toSeq_1000_ = lean_ctor_get(v_toApplicative_995_, 2);
v_toSeqLeft_1001_ = lean_ctor_get(v_toApplicative_995_, 3);
v_toSeqRight_1002_ = lean_ctor_get(v_toApplicative_995_, 4);
v_isSharedCheck_1084_ = !lean_is_exclusive(v_toApplicative_995_);
if (v_isSharedCheck_1084_ == 0)
{
lean_object* v_unused_1085_; 
v_unused_1085_ = lean_ctor_get(v_toApplicative_995_, 1);
lean_dec(v_unused_1085_);
v___x_1004_ = v_toApplicative_995_;
v_isShared_1005_ = v_isSharedCheck_1084_;
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
v_isShared_1005_ = v_isSharedCheck_1084_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___f_1006_; lean_object* v___f_1007_; lean_object* v___f_1008_; lean_object* v___f_1009_; lean_object* v___x_1010_; lean_object* v___f_1011_; lean_object* v___f_1012_; lean_object* v___f_1013_; lean_object* v___x_1015_; 
v___f_1006_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__1));
v___f_1007_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__2));
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
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1010_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v___f_1006_);
lean_ctor_set(v_reuseFailAlloc_1083_, 2, v___f_1013_);
lean_ctor_set(v_reuseFailAlloc_1083_, 3, v___f_1012_);
lean_ctor_set(v_reuseFailAlloc_1083_, 4, v___f_1011_);
v___x_1015_ = v_reuseFailAlloc_1083_;
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
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1015_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v___f_1007_);
v___x_1017_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v___x_1018_; lean_object* v_toApplicative_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1080_; 
v___x_1018_ = l_StateRefT_x27_instMonad___redArg(v___x_1017_);
v_toApplicative_1019_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1080_ == 0)
{
lean_object* v_unused_1081_; 
v_unused_1081_ = lean_ctor_get(v___x_1018_, 1);
lean_dec(v_unused_1081_);
v___x_1021_ = v___x_1018_;
v_isShared_1022_ = v_isSharedCheck_1080_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_toApplicative_1019_);
lean_dec(v___x_1018_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1080_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v_toFunctor_1023_; lean_object* v_toSeq_1024_; lean_object* v_toSeqLeft_1025_; lean_object* v_toSeqRight_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1078_; 
v_toFunctor_1023_ = lean_ctor_get(v_toApplicative_1019_, 0);
v_toSeq_1024_ = lean_ctor_get(v_toApplicative_1019_, 2);
v_toSeqLeft_1025_ = lean_ctor_get(v_toApplicative_1019_, 3);
v_toSeqRight_1026_ = lean_ctor_get(v_toApplicative_1019_, 4);
v_isSharedCheck_1078_ = !lean_is_exclusive(v_toApplicative_1019_);
if (v_isSharedCheck_1078_ == 0)
{
lean_object* v_unused_1079_; 
v_unused_1079_ = lean_ctor_get(v_toApplicative_1019_, 1);
lean_dec(v_unused_1079_);
v___x_1028_ = v_toApplicative_1019_;
v_isShared_1029_ = v_isSharedCheck_1078_;
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
v_isShared_1029_ = v_isSharedCheck_1078_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___f_1030_; lean_object* v___f_1031_; lean_object* v___f_1032_; lean_object* v___f_1033_; lean_object* v___x_1034_; lean_object* v___f_1035_; lean_object* v___f_1036_; lean_object* v___f_1037_; lean_object* v___x_1039_; 
v___f_1030_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__3));
v___f_1031_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__4));
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
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1034_);
lean_ctor_set(v_reuseFailAlloc_1077_, 1, v___f_1030_);
lean_ctor_set(v_reuseFailAlloc_1077_, 2, v___f_1037_);
lean_ctor_set(v_reuseFailAlloc_1077_, 3, v___f_1036_);
lean_ctor_set(v_reuseFailAlloc_1077_, 4, v___f_1035_);
v___x_1039_ = v_reuseFailAlloc_1077_;
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
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v___f_1031_);
v___x_1041_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1042_; lean_object* v_toApplicative_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1074_; 
v___x_1042_ = l_StateRefT_x27_instMonad___redArg(v___x_1041_);
v_toApplicative_1043_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1074_ == 0)
{
lean_object* v_unused_1075_; 
v_unused_1075_ = lean_ctor_get(v___x_1042_, 1);
lean_dec(v_unused_1075_);
v___x_1045_ = v___x_1042_;
v_isShared_1046_ = v_isSharedCheck_1074_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_toApplicative_1043_);
lean_dec(v___x_1042_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1074_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v_toFunctor_1047_; lean_object* v_toSeq_1048_; lean_object* v_toSeqLeft_1049_; lean_object* v_toSeqRight_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1072_; 
v_toFunctor_1047_ = lean_ctor_get(v_toApplicative_1043_, 0);
v_toSeq_1048_ = lean_ctor_get(v_toApplicative_1043_, 2);
v_toSeqLeft_1049_ = lean_ctor_get(v_toApplicative_1043_, 3);
v_toSeqRight_1050_ = lean_ctor_get(v_toApplicative_1043_, 4);
v_isSharedCheck_1072_ = !lean_is_exclusive(v_toApplicative_1043_);
if (v_isSharedCheck_1072_ == 0)
{
lean_object* v_unused_1073_; 
v_unused_1073_ = lean_ctor_get(v_toApplicative_1043_, 1);
lean_dec(v_unused_1073_);
v___x_1052_ = v_toApplicative_1043_;
v_isShared_1053_ = v_isSharedCheck_1072_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_toSeqRight_1050_);
lean_inc(v_toSeqLeft_1049_);
lean_inc(v_toSeq_1048_);
lean_inc(v_toFunctor_1047_);
lean_dec(v_toApplicative_1043_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1072_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___f_1054_; lean_object* v___f_1055_; lean_object* v___f_1056_; lean_object* v___f_1057_; lean_object* v___x_1058_; lean_object* v___f_1059_; lean_object* v___f_1060_; lean_object* v___f_1061_; lean_object* v___x_1063_; 
v___f_1054_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__5));
v___f_1055_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__6));
lean_inc_ref(v_toFunctor_1047_);
v___f_1056_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1056_, 0, v_toFunctor_1047_);
v___f_1057_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1057_, 0, v_toFunctor_1047_);
v___x_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___f_1056_);
lean_ctor_set(v___x_1058_, 1, v___f_1057_);
v___f_1059_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1059_, 0, v_toSeqRight_1050_);
v___f_1060_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1060_, 0, v_toSeqLeft_1049_);
v___f_1061_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1061_, 0, v_toSeq_1048_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 4, v___f_1059_);
lean_ctor_set(v___x_1052_, 3, v___f_1060_);
lean_ctor_set(v___x_1052_, 2, v___f_1061_);
lean_ctor_set(v___x_1052_, 1, v___f_1054_);
lean_ctor_set(v___x_1052_, 0, v___x_1058_);
v___x_1063_ = v___x_1052_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1058_);
lean_ctor_set(v_reuseFailAlloc_1071_, 1, v___f_1054_);
lean_ctor_set(v_reuseFailAlloc_1071_, 2, v___f_1061_);
lean_ctor_set(v_reuseFailAlloc_1071_, 3, v___f_1060_);
lean_ctor_set(v_reuseFailAlloc_1071_, 4, v___f_1059_);
v___x_1063_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
lean_object* v___x_1065_; 
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 1, v___f_1055_);
lean_ctor_set(v___x_1045_, 0, v___x_1063_);
v___x_1065_ = v___x_1045_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1063_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v___f_1055_);
v___x_1065_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_28031__overap_1068_; lean_object* v___x_1069_; 
v___x_1066_ = lean_box(0);
v___x_1067_ = l_instInhabitedOfMonad___redArg(v___x_1065_, v___x_1066_);
v___x_28031__overap_1068_ = lean_panic_fn_borrowed(v___x_1067_, v_msg_985_);
lean_dec(v___x_1067_);
lean_inc(v___y_991_);
lean_inc_ref(v___y_990_);
lean_inc(v___y_989_);
lean_inc_ref(v___y_988_);
lean_inc(v___y_987_);
lean_inc_ref(v___y_986_);
v___x_1069_ = lean_apply_7(v___x_28031__overap_1068_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, lean_box(0));
return v___x_1069_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___boxed(lean_object* v_msg_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1(v_msg_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
return v_res_1096_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__17));
v___x_1098_ = l_Lean_stringToMessageData(v___x_1097_);
return v___x_1098_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__2(void){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__1));
v___x_1101_ = l_Lean_stringToMessageData(v___x_1100_);
return v___x_1101_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__6(void){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1105_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__5));
v___x_1106_ = lean_unsigned_to_nat(11u);
v___x_1107_ = lean_unsigned_to_nat(122u);
v___x_1108_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__4));
v___x_1109_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__3));
v___x_1110_ = l_mkPanicMessageWithDecl(v___x_1109_, v___x_1108_, v___x_1107_, v___x_1106_, v___x_1105_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1(lean_object* v_constName_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v___x_1127_; lean_object* v_env_1128_; uint8_t v___x_1129_; lean_object* v___x_1130_; 
v___x_1127_ = lean_st_ref_get(v___y_1117_);
v_env_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc_ref(v_env_1128_);
lean_dec(v___x_1127_);
v___x_1129_ = 0;
lean_inc(v_constName_1111_);
v___x_1130_ = l_Lean_Environment_findAsync_x3f(v_env_1128_, v_constName_1111_, v___x_1129_);
if (lean_obj_tag(v___x_1130_) == 1)
{
lean_object* v_val_1131_; uint8_t v_kind_1132_; 
v_val_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_val_1131_);
lean_dec_ref_known(v___x_1130_, 1);
v_kind_1132_ = lean_ctor_get_uint8(v_val_1131_, sizeof(void*)*3);
if (v_kind_1132_ == 6)
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1131_);
if (lean_obj_tag(v___x_1133_) == 6)
{
lean_object* v_val_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
lean_dec(v_constName_1111_);
v_val_1134_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1136_ = v___x_1133_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_val_1134_);
lean_dec(v___x_1133_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1139_; 
if (v_isShared_1137_ == 0)
{
lean_ctor_set_tag(v___x_1136_, 0);
v___x_1139_ = v___x_1136_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_val_1134_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
else
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
lean_dec_ref(v___x_1133_);
v___x_1142_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__6, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__6_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__6);
v___x_1143_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1(v___x_1142_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1152_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1146_ = v___x_1143_;
v_isShared_1147_ = v_isSharedCheck_1152_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1143_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1152_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
if (lean_obj_tag(v_a_1144_) == 0)
{
lean_del_object(v___x_1146_);
goto v___jp_1119_;
}
else
{
lean_object* v_val_1148_; lean_object* v___x_1150_; 
lean_dec(v_constName_1111_);
v_val_1148_ = lean_ctor_get(v_a_1144_, 0);
lean_inc(v_val_1148_);
lean_dec_ref_known(v_a_1144_, 1);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v_val_1148_);
v___x_1150_ = v___x_1146_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_val_1148_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
else
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
lean_dec(v_constName_1111_);
v_a_1153_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1143_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1143_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
}
else
{
lean_dec(v_val_1131_);
goto v___jp_1119_;
}
}
else
{
lean_dec(v___x_1130_);
goto v___jp_1119_;
}
v___jp_1119_:
{
lean_object* v___x_1120_; uint8_t v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1120_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__0, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__0_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__0);
v___x_1121_ = 0;
v___x_1122_ = l_Lean_MessageData_ofConstName(v_constName_1111_, v___x_1121_);
v___x_1123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1120_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
v___x_1124_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__2, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__2_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__2);
v___x_1125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1123_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
v___x_1126_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v___x_1125_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
return v___x_1126_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___boxed(lean_object* v_constName_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1(v_constName_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__0(lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
lean_object* v_ref_1177_; uint8_t v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v_ref_1177_ = lean_ctor_get(v___y_1174_, 5);
v___x_1178_ = 0;
v___x_1179_ = l_Lean_SourceInfo_fromRef(v_ref_1177_, v___x_1178_);
v___x_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__0___boxed(lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__0(v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg(lean_object* v_upperBound_1196_, lean_object* v_a_1197_, lean_object* v_b_1198_, lean_object* v___y_1199_){
_start:
{
uint8_t v___x_1201_; 
v___x_1201_ = lean_nat_dec_lt(v_a_1197_, v_upperBound_1196_);
if (v___x_1201_ == 0)
{
lean_object* v___x_1202_; 
lean_dec(v_a_1197_);
v___x_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1202_, 0, v_b_1198_);
return v___x_1202_;
}
else
{
lean_object* v_ref_1203_; uint8_t v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v_ref_1203_ = lean_ctor_get(v___y_1199_, 5);
v___x_1204_ = 0;
v___x_1205_ = l_Lean_SourceInfo_fromRef(v_ref_1203_, v___x_1204_);
v___x_1206_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__1));
v___x_1207_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__2));
lean_inc(v___x_1205_);
v___x_1208_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1205_);
lean_ctor_set(v___x_1208_, 1, v___x_1207_);
v___x_1209_ = l_Lean_Syntax_node1(v___x_1205_, v___x_1206_, v___x_1208_);
v___x_1210_ = lean_array_push(v_b_1198_, v___x_1209_);
v___x_1211_ = lean_unsigned_to_nat(1u);
v___x_1212_ = lean_nat_add(v_a_1197_, v___x_1211_);
lean_dec(v_a_1197_);
v_a_1197_ = v___x_1212_;
v_b_1198_ = v___x_1210_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___boxed(lean_object* v_upperBound_1214_, lean_object* v_a_1215_, lean_object* v_b_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg(v_upperBound_1214_, v_a_1215_, v_b_1216_, v___y_1217_);
lean_dec_ref(v___y_1217_);
lean_dec(v_upperBound_1214_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6___redArg(lean_object* v_upperBound_1220_, lean_object* v_header_1221_, lean_object* v_xs_1222_, lean_object* v_indVal_1223_, lean_object* v_auxFunName_1224_, lean_object* v_levelInsts_1225_, lean_object* v_a_1226_, lean_object* v_b_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
uint8_t v___x_1233_; 
v___x_1233_ = lean_nat_dec_lt(v_a_1226_, v_upperBound_1220_);
if (v___x_1233_ == 0)
{
lean_object* v___x_1234_; 
lean_dec(v_a_1226_);
lean_dec(v_auxFunName_1224_);
lean_dec_ref(v_indVal_1223_);
v___x_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1234_, 0, v_b_1227_);
return v___x_1234_;
}
else
{
lean_object* v_argNames_1235_; lean_object* v_ref_1236_; lean_object* v_quotContext_1237_; lean_object* v_currMacroScope_1238_; lean_object* v_a_1240_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v_argNames_1235_ = lean_ctor_get(v_header_1221_, 1);
v_ref_1236_ = lean_ctor_get(v___y_1230_, 5);
v_quotContext_1237_ = lean_ctor_get(v___y_1230_, 10);
v_currMacroScope_1238_ = lean_ctor_get(v___y_1230_, 11);
v___x_1261_ = l_Lean_instInhabitedExpr;
v___x_1262_ = lean_array_get_borrowed(v___x_1261_, v_xs_1222_, v_a_1226_);
lean_inc(v___y_1231_);
lean_inc_ref(v___y_1230_);
lean_inc(v___y_1229_);
lean_inc_ref(v___y_1228_);
lean_inc(v___x_1262_);
v___x_1263_ = lean_infer_type(v___x_1262_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_toConstantVal_1264_; lean_object* v_a_1265_; lean_object* v_name_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1318_; 
v_toConstantVal_1264_ = lean_ctor_get(v_indVal_1223_, 0);
lean_inc_ref(v_toConstantVal_1264_);
v_a_1265_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_a_1265_);
lean_dec_ref_known(v___x_1263_, 1);
v_name_1266_ = lean_ctor_get(v_toConstantVal_1264_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v_toConstantVal_1264_);
if (v_isSharedCheck_1318_ == 0)
{
lean_object* v_unused_1319_; lean_object* v_unused_1320_; 
v_unused_1319_ = lean_ctor_get(v_toConstantVal_1264_, 2);
lean_dec(v_unused_1319_);
v_unused_1320_ = lean_ctor_get(v_toConstantVal_1264_, 1);
lean_dec(v_unused_1320_);
v___x_1268_ = v_toConstantVal_1264_;
v_isShared_1269_ = v_isSharedCheck_1318_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_name_1266_);
lean_dec(v_toConstantVal_1264_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1318_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; uint8_t v___x_1273_; 
v___x_1270_ = lean_box(0);
v___x_1271_ = lean_array_get_borrowed(v___x_1270_, v_argNames_1235_, v_a_1226_);
lean_inc(v___x_1271_);
v___x_1272_ = l_Lean_mkIdent(v___x_1271_);
v___x_1273_ = l_Lean_Expr_isAppOf(v_a_1265_, v_name_1266_);
lean_dec(v_name_1266_);
lean_dec(v_a_1265_);
if (v___x_1273_ == 0)
{
lean_object* v___x_1274_; 
lean_del_object(v___x_1268_);
lean_inc(v___x_1262_);
v___x_1274_ = l_Lean_Meta_isType(v___x_1262_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; uint8_t v___x_1276_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_a_1275_);
lean_dec_ref_known(v___x_1274_, 1);
v___x_1276_ = lean_unbox(v_a_1275_);
if (v___x_1276_ == 0)
{
uint8_t v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1277_ = lean_unbox(v_a_1275_);
lean_dec(v_a_1275_);
v___x_1278_ = l_Lean_SourceInfo_fromRef(v_ref_1236_, v___x_1277_);
v___x_1279_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1280_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1);
v___x_1281_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__2));
lean_inc(v_currMacroScope_1238_);
lean_inc(v_quotContext_1237_);
v___x_1282_ = l_Lean_addMacroScope(v_quotContext_1237_, v___x_1281_, v_currMacroScope_1238_);
v___x_1283_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__6));
lean_inc_n(v___x_1278_, 2);
v___x_1284_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1278_);
lean_ctor_set(v___x_1284_, 1, v___x_1280_);
lean_ctor_set(v___x_1284_, 2, v___x_1282_);
lean_ctor_set(v___x_1284_, 3, v___x_1283_);
v___x_1285_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1286_ = l_Lean_Syntax_node1(v___x_1278_, v___x_1285_, v___x_1272_);
v___x_1287_ = l_Lean_Syntax_node2(v___x_1278_, v___x_1279_, v___x_1284_, v___x_1286_);
v_a_1240_ = v___x_1287_;
goto v___jp_1239_;
}
else
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
lean_dec(v_a_1275_);
v___x_1288_ = l_Lean_SourceInfo_fromRef(v_ref_1236_, v___x_1273_);
v___x_1289_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1290_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8);
v___x_1291_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__9));
lean_inc(v_currMacroScope_1238_);
lean_inc(v_quotContext_1237_);
v___x_1292_ = l_Lean_addMacroScope(v_quotContext_1237_, v___x_1291_, v_currMacroScope_1238_);
v___x_1293_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__12));
lean_inc_n(v___x_1288_, 2);
v___x_1294_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1288_);
lean_ctor_set(v___x_1294_, 1, v___x_1290_);
lean_ctor_set(v___x_1294_, 2, v___x_1292_);
lean_ctor_set(v___x_1294_, 3, v___x_1293_);
v___x_1295_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1296_ = l_Lean_Syntax_node1(v___x_1288_, v___x_1295_, v___x_1272_);
v___x_1297_ = l_Lean_Syntax_node2(v___x_1288_, v___x_1289_, v___x_1294_, v___x_1296_);
v_a_1240_ = v___x_1297_;
goto v___jp_1239_;
}
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
lean_dec(v___x_1272_);
lean_dec_ref(v_b_1227_);
lean_dec(v_a_1226_);
lean_dec(v_auxFunName_1224_);
lean_dec_ref(v_indVal_1223_);
v_a_1298_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1274_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1274_);
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
}
else
{
uint8_t v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1315_; 
v___x_1306_ = 0;
v___x_1307_ = l_Lean_SourceInfo_fromRef(v_ref_1236_, v___x_1306_);
v___x_1308_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
lean_inc(v_auxFunName_1224_);
v___x_1309_ = l_Lean_mkIdent(v_auxFunName_1224_);
v___x_1310_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1311_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_1312_ = l_Array_append___redArg(v___x_1311_, v_levelInsts_1225_);
v___x_1313_ = lean_array_push(v___x_1312_, v___x_1272_);
lean_inc(v___x_1307_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set_tag(v___x_1268_, 1);
lean_ctor_set(v___x_1268_, 2, v___x_1313_);
lean_ctor_set(v___x_1268_, 1, v___x_1310_);
lean_ctor_set(v___x_1268_, 0, v___x_1307_);
v___x_1315_ = v___x_1268_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1307_);
lean_ctor_set(v_reuseFailAlloc_1317_, 1, v___x_1310_);
lean_ctor_set(v_reuseFailAlloc_1317_, 2, v___x_1313_);
v___x_1315_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
lean_object* v___x_1316_; 
v___x_1316_ = l_Lean_Syntax_node2(v___x_1307_, v___x_1308_, v___x_1309_, v___x_1315_);
v_a_1240_ = v___x_1316_;
goto v___jp_1239_;
}
}
}
}
else
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
lean_dec_ref(v_b_1227_);
lean_dec(v_a_1226_);
lean_dec(v_auxFunName_1224_);
lean_dec_ref(v_indVal_1223_);
v_a_1321_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___x_1263_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1263_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
v___jp_1239_:
{
lean_object* v_fst_1241_; lean_object* v_snd_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1260_; 
v_fst_1241_ = lean_ctor_get(v_b_1227_, 0);
v_snd_1242_ = lean_ctor_get(v_b_1227_, 1);
v_isSharedCheck_1260_ = !lean_is_exclusive(v_b_1227_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1244_ = v_b_1227_;
v_isShared_1245_ = v_isSharedCheck_1260_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_snd_1242_);
lean_inc(v_fst_1241_);
lean_dec(v_b_1227_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1260_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
uint8_t v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1255_; 
v___x_1246_ = 0;
v___x_1247_ = l_Lean_SourceInfo_fromRef(v_ref_1236_, v___x_1246_);
v___x_1248_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__2));
lean_inc(v___x_1247_);
v___x_1249_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1247_);
lean_ctor_set(v___x_1249_, 1, v___x_1248_);
v___x_1250_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__1));
v___x_1251_ = l_Lean_Syntax_node1(v___x_1247_, v___x_1250_, v___x_1249_);
v___x_1252_ = lean_array_push(v_fst_1241_, v___x_1251_);
v___x_1253_ = lean_array_push(v_snd_1242_, v_a_1240_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 1, v___x_1253_);
lean_ctor_set(v___x_1244_, 0, v___x_1252_);
v___x_1255_ = v___x_1244_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v___x_1252_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v___x_1253_);
v___x_1255_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = lean_unsigned_to_nat(1u);
v___x_1257_ = lean_nat_add(v_a_1226_, v___x_1256_);
lean_dec(v_a_1226_);
v_a_1226_ = v___x_1257_;
v_b_1227_ = v___x_1255_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6___redArg___boxed(lean_object* v_upperBound_1329_, lean_object* v_header_1330_, lean_object* v_xs_1331_, lean_object* v_indVal_1332_, lean_object* v_auxFunName_1333_, lean_object* v_levelInsts_1334_, lean_object* v_a_1335_, lean_object* v_b_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6___redArg(v_upperBound_1329_, v_header_1330_, v_xs_1331_, v_indVal_1332_, v_auxFunName_1333_, v_levelInsts_1334_, v_a_1335_, v_b_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec_ref(v_levelInsts_1334_);
lean_dec_ref(v_xs_1331_);
lean_dec_ref(v_header_1330_);
lean_dec(v_upperBound_1329_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4___redArg(lean_object* v_upperBound_1343_, lean_object* v_header_1344_, lean_object* v_xs_1345_, lean_object* v_indVal_1346_, lean_object* v_auxFunName_1347_, lean_object* v_levelInsts_1348_, lean_object* v_a_1349_, lean_object* v_b_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
uint8_t v___x_1358_; 
v___x_1358_ = lean_nat_dec_lt(v_a_1349_, v_upperBound_1343_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; 
lean_dec(v_auxFunName_1347_);
lean_dec_ref(v_indVal_1346_);
v___x_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1359_, 0, v_b_1350_);
return v___x_1359_;
}
else
{
lean_object* v_argNames_1360_; lean_object* v_ref_1361_; lean_object* v_quotContext_1362_; lean_object* v_currMacroScope_1363_; lean_object* v_a_1365_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v_argNames_1360_ = lean_ctor_get(v_header_1344_, 1);
v_ref_1361_ = lean_ctor_get(v___y_1355_, 5);
v_quotContext_1362_ = lean_ctor_get(v___y_1355_, 10);
v_currMacroScope_1363_ = lean_ctor_get(v___y_1355_, 11);
v___x_1386_ = l_Lean_instInhabitedExpr;
v___x_1387_ = lean_array_get_borrowed(v___x_1386_, v_xs_1345_, v_a_1349_);
lean_inc(v___y_1356_);
lean_inc_ref(v___y_1355_);
lean_inc(v___y_1354_);
lean_inc_ref(v___y_1353_);
lean_inc(v___x_1387_);
v___x_1388_ = lean_infer_type(v___x_1387_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_toConstantVal_1389_; lean_object* v_a_1390_; lean_object* v_name_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1443_; 
v_toConstantVal_1389_ = lean_ctor_get(v_indVal_1346_, 0);
lean_inc_ref(v_toConstantVal_1389_);
v_a_1390_ = lean_ctor_get(v___x_1388_, 0);
lean_inc(v_a_1390_);
lean_dec_ref_known(v___x_1388_, 1);
v_name_1391_ = lean_ctor_get(v_toConstantVal_1389_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v_toConstantVal_1389_);
if (v_isSharedCheck_1443_ == 0)
{
lean_object* v_unused_1444_; lean_object* v_unused_1445_; 
v_unused_1444_ = lean_ctor_get(v_toConstantVal_1389_, 2);
lean_dec(v_unused_1444_);
v_unused_1445_ = lean_ctor_get(v_toConstantVal_1389_, 1);
lean_dec(v_unused_1445_);
v___x_1393_ = v_toConstantVal_1389_;
v_isShared_1394_ = v_isSharedCheck_1443_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_name_1391_);
lean_dec(v_toConstantVal_1389_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1443_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; uint8_t v___x_1398_; 
v___x_1395_ = lean_box(0);
v___x_1396_ = lean_array_get_borrowed(v___x_1395_, v_argNames_1360_, v_a_1349_);
lean_inc(v___x_1396_);
v___x_1397_ = l_Lean_mkIdent(v___x_1396_);
v___x_1398_ = l_Lean_Expr_isAppOf(v_a_1390_, v_name_1391_);
lean_dec(v_name_1391_);
lean_dec(v_a_1390_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1399_; 
lean_del_object(v___x_1393_);
lean_inc(v___x_1387_);
v___x_1399_ = l_Lean_Meta_isType(v___x_1387_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v_a_1400_; uint8_t v___x_1401_; 
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
lean_inc(v_a_1400_);
lean_dec_ref_known(v___x_1399_, 1);
v___x_1401_ = lean_unbox(v_a_1400_);
if (v___x_1401_ == 0)
{
uint8_t v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1402_ = lean_unbox(v_a_1400_);
lean_dec(v_a_1400_);
v___x_1403_ = l_Lean_SourceInfo_fromRef(v_ref_1361_, v___x_1402_);
v___x_1404_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1405_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1);
v___x_1406_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__2));
lean_inc(v_currMacroScope_1363_);
lean_inc(v_quotContext_1362_);
v___x_1407_ = l_Lean_addMacroScope(v_quotContext_1362_, v___x_1406_, v_currMacroScope_1363_);
v___x_1408_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__6));
lean_inc_n(v___x_1403_, 2);
v___x_1409_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1403_);
lean_ctor_set(v___x_1409_, 1, v___x_1405_);
lean_ctor_set(v___x_1409_, 2, v___x_1407_);
lean_ctor_set(v___x_1409_, 3, v___x_1408_);
v___x_1410_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1411_ = l_Lean_Syntax_node1(v___x_1403_, v___x_1410_, v___x_1397_);
v___x_1412_ = l_Lean_Syntax_node2(v___x_1403_, v___x_1404_, v___x_1409_, v___x_1411_);
v_a_1365_ = v___x_1412_;
goto v___jp_1364_;
}
else
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
lean_dec(v_a_1400_);
v___x_1413_ = l_Lean_SourceInfo_fromRef(v_ref_1361_, v___x_1398_);
v___x_1414_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1415_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8);
v___x_1416_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__9));
lean_inc(v_currMacroScope_1363_);
lean_inc(v_quotContext_1362_);
v___x_1417_ = l_Lean_addMacroScope(v_quotContext_1362_, v___x_1416_, v_currMacroScope_1363_);
v___x_1418_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__12));
lean_inc_n(v___x_1413_, 2);
v___x_1419_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1413_);
lean_ctor_set(v___x_1419_, 1, v___x_1415_);
lean_ctor_set(v___x_1419_, 2, v___x_1417_);
lean_ctor_set(v___x_1419_, 3, v___x_1418_);
v___x_1420_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1421_ = l_Lean_Syntax_node1(v___x_1413_, v___x_1420_, v___x_1397_);
v___x_1422_ = l_Lean_Syntax_node2(v___x_1413_, v___x_1414_, v___x_1419_, v___x_1421_);
v_a_1365_ = v___x_1422_;
goto v___jp_1364_;
}
}
else
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1430_; 
lean_dec(v___x_1397_);
lean_dec_ref(v_b_1350_);
lean_dec(v_auxFunName_1347_);
lean_dec_ref(v_indVal_1346_);
v_a_1423_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1425_ = v___x_1399_;
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1399_);
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
}
else
{
uint8_t v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1440_; 
v___x_1431_ = 0;
v___x_1432_ = l_Lean_SourceInfo_fromRef(v_ref_1361_, v___x_1431_);
v___x_1433_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
lean_inc(v_auxFunName_1347_);
v___x_1434_ = l_Lean_mkIdent(v_auxFunName_1347_);
v___x_1435_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1436_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_1437_ = l_Array_append___redArg(v___x_1436_, v_levelInsts_1348_);
v___x_1438_ = lean_array_push(v___x_1437_, v___x_1397_);
lean_inc(v___x_1432_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set_tag(v___x_1393_, 1);
lean_ctor_set(v___x_1393_, 2, v___x_1438_);
lean_ctor_set(v___x_1393_, 1, v___x_1435_);
lean_ctor_set(v___x_1393_, 0, v___x_1432_);
v___x_1440_ = v___x_1393_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1432_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v___x_1435_);
lean_ctor_set(v_reuseFailAlloc_1442_, 2, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1441_; 
v___x_1441_ = l_Lean_Syntax_node2(v___x_1432_, v___x_1433_, v___x_1434_, v___x_1440_);
v_a_1365_ = v___x_1441_;
goto v___jp_1364_;
}
}
}
}
else
{
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
lean_dec_ref(v_b_1350_);
lean_dec(v_auxFunName_1347_);
lean_dec_ref(v_indVal_1346_);
v_a_1446_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1388_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1388_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1446_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
v___jp_1364_:
{
lean_object* v_fst_1366_; lean_object* v_snd_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1385_; 
v_fst_1366_ = lean_ctor_get(v_b_1350_, 0);
v_snd_1367_ = lean_ctor_get(v_b_1350_, 1);
v_isSharedCheck_1385_ = !lean_is_exclusive(v_b_1350_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1369_ = v_b_1350_;
v_isShared_1370_ = v_isSharedCheck_1385_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_snd_1367_);
lean_inc(v_fst_1366_);
lean_dec(v_b_1350_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1385_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
uint8_t v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1380_; 
v___x_1371_ = 0;
v___x_1372_ = l_Lean_SourceInfo_fromRef(v_ref_1361_, v___x_1371_);
v___x_1373_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__2));
lean_inc(v___x_1372_);
v___x_1374_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1372_);
lean_ctor_set(v___x_1374_, 1, v___x_1373_);
v___x_1375_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__1));
v___x_1376_ = l_Lean_Syntax_node1(v___x_1372_, v___x_1375_, v___x_1374_);
v___x_1377_ = lean_array_push(v_fst_1366_, v___x_1376_);
v___x_1378_ = lean_array_push(v_snd_1367_, v_a_1365_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 1, v___x_1378_);
lean_ctor_set(v___x_1369_, 0, v___x_1377_);
v___x_1380_ = v___x_1369_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v___x_1378_);
v___x_1380_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1381_ = lean_unsigned_to_nat(1u);
v___x_1382_ = lean_nat_add(v_a_1349_, v___x_1381_);
v___x_1383_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6___redArg(v_upperBound_1343_, v_header_1344_, v_xs_1345_, v_indVal_1346_, v_auxFunName_1347_, v_levelInsts_1348_, v___x_1382_, v___x_1380_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
return v___x_1383_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4___redArg___boxed(lean_object* v_upperBound_1454_, lean_object* v_header_1455_, lean_object* v_xs_1456_, lean_object* v_indVal_1457_, lean_object* v_auxFunName_1458_, lean_object* v_levelInsts_1459_, lean_object* v_a_1460_, lean_object* v_b_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4___redArg(v_upperBound_1454_, v_header_1455_, v_xs_1456_, v_indVal_1457_, v_auxFunName_1458_, v_levelInsts_1459_, v_a_1460_, v_b_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v_a_1460_);
lean_dec_ref(v_levelInsts_1459_);
lean_dec_ref(v_xs_1456_);
lean_dec_ref(v_header_1455_);
lean_dec(v_upperBound_1454_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg(lean_object* v_upperBound_1473_, lean_object* v___x_1474_, lean_object* v_xs_1475_, lean_object* v_indVal_1476_, lean_object* v_auxFunName_1477_, lean_object* v_levelInsts_1478_, lean_object* v_a_1479_, lean_object* v_b_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
uint8_t v___x_1486_; 
v___x_1486_ = lean_nat_dec_lt(v_a_1479_, v_upperBound_1473_);
if (v___x_1486_ == 0)
{
lean_object* v___x_1487_; 
lean_dec(v_a_1479_);
lean_dec(v_auxFunName_1477_);
lean_dec_ref(v_indVal_1476_);
v___x_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1487_, 0, v_b_1480_);
return v___x_1487_;
}
else
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg___closed__1));
v___x_1489_ = l_Lean_Core_mkFreshUserName(v___x_1488_, v___y_1483_, v___y_1484_);
if (lean_obj_tag(v___x_1489_) == 0)
{
lean_object* v_a_1490_; lean_object* v_fst_1491_; lean_object* v_snd_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1580_; 
v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
lean_inc(v_a_1490_);
lean_dec_ref_known(v___x_1489_, 1);
v_fst_1491_ = lean_ctor_get(v_b_1480_, 0);
v_snd_1492_ = lean_ctor_get(v_b_1480_, 1);
v_isSharedCheck_1580_ = !lean_is_exclusive(v_b_1480_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1494_ = v_b_1480_;
v_isShared_1495_ = v_isSharedCheck_1580_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_snd_1492_);
lean_inc(v_fst_1491_);
lean_dec(v_b_1480_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1580_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1496_ = l_Lean_instInhabitedExpr;
v___x_1497_ = lean_nat_add(v___x_1474_, v_a_1479_);
v___x_1498_ = lean_array_get_borrowed(v___x_1496_, v_xs_1475_, v___x_1497_);
lean_dec(v___x_1497_);
lean_inc(v___y_1484_);
lean_inc_ref(v___y_1483_);
lean_inc(v___y_1482_);
lean_inc_ref(v___y_1481_);
lean_inc(v___x_1498_);
v___x_1499_ = lean_infer_type(v___x_1498_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_toConstantVal_1500_; lean_object* v_a_1501_; lean_object* v_name_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1569_; 
v_toConstantVal_1500_ = lean_ctor_get(v_indVal_1476_, 0);
lean_inc_ref(v_toConstantVal_1500_);
v_a_1501_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_a_1501_);
lean_dec_ref_known(v___x_1499_, 1);
v_name_1502_ = lean_ctor_get(v_toConstantVal_1500_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v_toConstantVal_1500_);
if (v_isSharedCheck_1569_ == 0)
{
lean_object* v_unused_1570_; lean_object* v_unused_1571_; 
v_unused_1570_ = lean_ctor_get(v_toConstantVal_1500_, 2);
lean_dec(v_unused_1570_);
v_unused_1571_ = lean_ctor_get(v_toConstantVal_1500_, 1);
lean_dec(v_unused_1571_);
v___x_1504_ = v_toConstantVal_1500_;
v_isShared_1505_ = v_isSharedCheck_1569_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_name_1502_);
lean_dec(v_toConstantVal_1500_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1569_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v_a_1509_; uint8_t v___x_1517_; 
v___x_1506_ = l_Lean_mkIdent(v_a_1490_);
lean_inc(v___x_1506_);
v___x_1507_ = lean_array_push(v_fst_1491_, v___x_1506_);
v___x_1517_ = l_Lean_Expr_isAppOf(v_a_1501_, v_name_1502_);
lean_dec(v_name_1502_);
lean_dec(v_a_1501_);
if (v___x_1517_ == 0)
{
lean_object* v___x_1518_; 
lean_del_object(v___x_1504_);
lean_inc(v___x_1498_);
v___x_1518_ = l_Lean_Meta_isType(v___x_1498_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; uint8_t v___x_1520_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_a_1519_);
lean_dec_ref_known(v___x_1518_, 1);
v___x_1520_ = lean_unbox(v_a_1519_);
if (v___x_1520_ == 0)
{
lean_object* v_ref_1521_; lean_object* v_quotContext_1522_; lean_object* v_currMacroScope_1523_; uint8_t v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v_ref_1521_ = lean_ctor_get(v___y_1483_, 5);
v_quotContext_1522_ = lean_ctor_get(v___y_1483_, 10);
v_currMacroScope_1523_ = lean_ctor_get(v___y_1483_, 11);
v___x_1524_ = lean_unbox(v_a_1519_);
lean_dec(v_a_1519_);
v___x_1525_ = l_Lean_SourceInfo_fromRef(v_ref_1521_, v___x_1524_);
v___x_1526_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1527_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1);
v___x_1528_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__2));
lean_inc(v_currMacroScope_1523_);
lean_inc(v_quotContext_1522_);
v___x_1529_ = l_Lean_addMacroScope(v_quotContext_1522_, v___x_1528_, v_currMacroScope_1523_);
v___x_1530_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__6));
lean_inc_n(v___x_1525_, 2);
v___x_1531_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1525_);
lean_ctor_set(v___x_1531_, 1, v___x_1527_);
lean_ctor_set(v___x_1531_, 2, v___x_1529_);
lean_ctor_set(v___x_1531_, 3, v___x_1530_);
v___x_1532_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1533_ = l_Lean_Syntax_node1(v___x_1525_, v___x_1532_, v___x_1506_);
v___x_1534_ = l_Lean_Syntax_node2(v___x_1525_, v___x_1526_, v___x_1531_, v___x_1533_);
v_a_1509_ = v___x_1534_;
goto v___jp_1508_;
}
else
{
lean_object* v_ref_1535_; lean_object* v_quotContext_1536_; lean_object* v_currMacroScope_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
lean_dec(v_a_1519_);
v_ref_1535_ = lean_ctor_get(v___y_1483_, 5);
v_quotContext_1536_ = lean_ctor_get(v___y_1483_, 10);
v_currMacroScope_1537_ = lean_ctor_get(v___y_1483_, 11);
v___x_1538_ = l_Lean_SourceInfo_fromRef(v_ref_1535_, v___x_1517_);
v___x_1539_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1540_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8);
v___x_1541_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__9));
lean_inc(v_currMacroScope_1537_);
lean_inc(v_quotContext_1536_);
v___x_1542_ = l_Lean_addMacroScope(v_quotContext_1536_, v___x_1541_, v_currMacroScope_1537_);
v___x_1543_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__12));
lean_inc_n(v___x_1538_, 2);
v___x_1544_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1538_);
lean_ctor_set(v___x_1544_, 1, v___x_1540_);
lean_ctor_set(v___x_1544_, 2, v___x_1542_);
lean_ctor_set(v___x_1544_, 3, v___x_1543_);
v___x_1545_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1546_ = l_Lean_Syntax_node1(v___x_1538_, v___x_1545_, v___x_1506_);
v___x_1547_ = l_Lean_Syntax_node2(v___x_1538_, v___x_1539_, v___x_1544_, v___x_1546_);
v_a_1509_ = v___x_1547_;
goto v___jp_1508_;
}
}
else
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1555_; 
lean_dec_ref(v___x_1507_);
lean_dec(v___x_1506_);
lean_del_object(v___x_1494_);
lean_dec(v_snd_1492_);
lean_dec(v_a_1479_);
lean_dec(v_auxFunName_1477_);
lean_dec_ref(v_indVal_1476_);
v_a_1548_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1550_ = v___x_1518_;
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1518_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1553_; 
if (v_isShared_1551_ == 0)
{
v___x_1553_ = v___x_1550_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_a_1548_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
}
else
{
lean_object* v_ref_1556_; uint8_t v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1566_; 
v_ref_1556_ = lean_ctor_get(v___y_1483_, 5);
v___x_1557_ = 0;
v___x_1558_ = l_Lean_SourceInfo_fromRef(v_ref_1556_, v___x_1557_);
v___x_1559_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
lean_inc(v_auxFunName_1477_);
v___x_1560_ = l_Lean_mkIdent(v_auxFunName_1477_);
v___x_1561_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1562_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_1563_ = l_Array_append___redArg(v___x_1562_, v_levelInsts_1478_);
v___x_1564_ = lean_array_push(v___x_1563_, v___x_1506_);
lean_inc(v___x_1558_);
if (v_isShared_1505_ == 0)
{
lean_ctor_set_tag(v___x_1504_, 1);
lean_ctor_set(v___x_1504_, 2, v___x_1564_);
lean_ctor_set(v___x_1504_, 1, v___x_1561_);
lean_ctor_set(v___x_1504_, 0, v___x_1558_);
v___x_1566_ = v___x_1504_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___x_1558_);
lean_ctor_set(v_reuseFailAlloc_1568_, 1, v___x_1561_);
lean_ctor_set(v_reuseFailAlloc_1568_, 2, v___x_1564_);
v___x_1566_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
lean_object* v___x_1567_; 
v___x_1567_ = l_Lean_Syntax_node2(v___x_1558_, v___x_1559_, v___x_1560_, v___x_1566_);
v_a_1509_ = v___x_1567_;
goto v___jp_1508_;
}
}
v___jp_1508_:
{
lean_object* v___x_1510_; lean_object* v___x_1512_; 
v___x_1510_ = lean_array_push(v_snd_1492_, v_a_1509_);
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 1, v___x_1510_);
lean_ctor_set(v___x_1494_, 0, v___x_1507_);
v___x_1512_ = v___x_1494_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1507_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v___x_1510_);
v___x_1512_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1513_ = lean_unsigned_to_nat(1u);
v___x_1514_ = lean_nat_add(v_a_1479_, v___x_1513_);
lean_dec(v_a_1479_);
v_a_1479_ = v___x_1514_;
v_b_1480_ = v___x_1512_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
lean_del_object(v___x_1494_);
lean_dec(v_snd_1492_);
lean_dec(v_fst_1491_);
lean_dec(v_a_1490_);
lean_dec(v_a_1479_);
lean_dec(v_auxFunName_1477_);
lean_dec_ref(v_indVal_1476_);
v_a_1572_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1499_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1499_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1572_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
}
else
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
lean_dec_ref(v_b_1480_);
lean_dec(v_a_1479_);
lean_dec(v_auxFunName_1477_);
lean_dec_ref(v_indVal_1476_);
v_a_1581_ = lean_ctor_get(v___x_1489_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1489_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1583_ = v___x_1489_;
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1489_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1586_; 
if (v_isShared_1584_ == 0)
{
v___x_1586_ = v___x_1583_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_a_1581_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg___boxed(lean_object* v_upperBound_1589_, lean_object* v___x_1590_, lean_object* v_xs_1591_, lean_object* v_indVal_1592_, lean_object* v_auxFunName_1593_, lean_object* v_levelInsts_1594_, lean_object* v_a_1595_, lean_object* v_b_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg(v_upperBound_1589_, v___x_1590_, v_xs_1591_, v_indVal_1592_, v_auxFunName_1593_, v_levelInsts_1594_, v_a_1595_, v_b_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec_ref(v_levelInsts_1594_);
lean_dec_ref(v_xs_1591_);
lean_dec(v___x_1590_);
lean_dec(v_upperBound_1589_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3___redArg(lean_object* v_upperBound_1603_, lean_object* v___x_1604_, lean_object* v_xs_1605_, lean_object* v_indVal_1606_, lean_object* v_auxFunName_1607_, lean_object* v_levelInsts_1608_, lean_object* v_a_1609_, lean_object* v_b_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
uint8_t v___x_1618_; 
v___x_1618_ = lean_nat_dec_lt(v_a_1609_, v_upperBound_1603_);
if (v___x_1618_ == 0)
{
lean_object* v___x_1619_; 
lean_dec(v_auxFunName_1607_);
lean_dec_ref(v_indVal_1606_);
v___x_1619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1619_, 0, v_b_1610_);
return v___x_1619_;
}
else
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1620_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg___closed__1));
v___x_1621_ = l_Lean_Core_mkFreshUserName(v___x_1620_, v___y_1615_, v___y_1616_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_a_1622_; lean_object* v_fst_1623_; lean_object* v_snd_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1712_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_a_1622_);
lean_dec_ref_known(v___x_1621_, 1);
v_fst_1623_ = lean_ctor_get(v_b_1610_, 0);
v_snd_1624_ = lean_ctor_get(v_b_1610_, 1);
v_isSharedCheck_1712_ = !lean_is_exclusive(v_b_1610_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1626_ = v_b_1610_;
v_isShared_1627_ = v_isSharedCheck_1712_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_snd_1624_);
lean_inc(v_fst_1623_);
lean_dec(v_b_1610_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1712_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1628_ = l_Lean_instInhabitedExpr;
v___x_1629_ = lean_nat_add(v___x_1604_, v_a_1609_);
v___x_1630_ = lean_array_get_borrowed(v___x_1628_, v_xs_1605_, v___x_1629_);
lean_dec(v___x_1629_);
lean_inc(v___y_1616_);
lean_inc_ref(v___y_1615_);
lean_inc(v___y_1614_);
lean_inc_ref(v___y_1613_);
lean_inc(v___x_1630_);
v___x_1631_ = lean_infer_type(v___x_1630_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_toConstantVal_1632_; lean_object* v_a_1633_; lean_object* v_name_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1701_; 
v_toConstantVal_1632_ = lean_ctor_get(v_indVal_1606_, 0);
lean_inc_ref(v_toConstantVal_1632_);
v_a_1633_ = lean_ctor_get(v___x_1631_, 0);
lean_inc(v_a_1633_);
lean_dec_ref_known(v___x_1631_, 1);
v_name_1634_ = lean_ctor_get(v_toConstantVal_1632_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v_toConstantVal_1632_);
if (v_isSharedCheck_1701_ == 0)
{
lean_object* v_unused_1702_; lean_object* v_unused_1703_; 
v_unused_1702_ = lean_ctor_get(v_toConstantVal_1632_, 2);
lean_dec(v_unused_1702_);
v_unused_1703_ = lean_ctor_get(v_toConstantVal_1632_, 1);
lean_dec(v_unused_1703_);
v___x_1636_ = v_toConstantVal_1632_;
v_isShared_1637_ = v_isSharedCheck_1701_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_name_1634_);
lean_dec(v_toConstantVal_1632_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1701_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v_a_1641_; uint8_t v___x_1649_; 
v___x_1638_ = l_Lean_mkIdent(v_a_1622_);
lean_inc(v___x_1638_);
v___x_1639_ = lean_array_push(v_fst_1623_, v___x_1638_);
v___x_1649_ = l_Lean_Expr_isAppOf(v_a_1633_, v_name_1634_);
lean_dec(v_name_1634_);
lean_dec(v_a_1633_);
if (v___x_1649_ == 0)
{
lean_object* v___x_1650_; 
lean_del_object(v___x_1636_);
lean_inc(v___x_1630_);
v___x_1650_ = l_Lean_Meta_isType(v___x_1630_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; uint8_t v___x_1652_; 
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_a_1651_);
lean_dec_ref_known(v___x_1650_, 1);
v___x_1652_ = lean_unbox(v_a_1651_);
if (v___x_1652_ == 0)
{
lean_object* v_ref_1653_; lean_object* v_quotContext_1654_; lean_object* v_currMacroScope_1655_; uint8_t v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v_ref_1653_ = lean_ctor_get(v___y_1615_, 5);
v_quotContext_1654_ = lean_ctor_get(v___y_1615_, 10);
v_currMacroScope_1655_ = lean_ctor_get(v___y_1615_, 11);
v___x_1656_ = lean_unbox(v_a_1651_);
lean_dec(v_a_1651_);
v___x_1657_ = l_Lean_SourceInfo_fromRef(v_ref_1653_, v___x_1656_);
v___x_1658_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1659_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1);
v___x_1660_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__2));
lean_inc(v_currMacroScope_1655_);
lean_inc(v_quotContext_1654_);
v___x_1661_ = l_Lean_addMacroScope(v_quotContext_1654_, v___x_1660_, v_currMacroScope_1655_);
v___x_1662_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__6));
lean_inc_n(v___x_1657_, 2);
v___x_1663_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1657_);
lean_ctor_set(v___x_1663_, 1, v___x_1659_);
lean_ctor_set(v___x_1663_, 2, v___x_1661_);
lean_ctor_set(v___x_1663_, 3, v___x_1662_);
v___x_1664_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1665_ = l_Lean_Syntax_node1(v___x_1657_, v___x_1664_, v___x_1638_);
v___x_1666_ = l_Lean_Syntax_node2(v___x_1657_, v___x_1658_, v___x_1663_, v___x_1665_);
v_a_1641_ = v___x_1666_;
goto v___jp_1640_;
}
else
{
lean_object* v_ref_1667_; lean_object* v_quotContext_1668_; lean_object* v_currMacroScope_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
lean_dec(v_a_1651_);
v_ref_1667_ = lean_ctor_get(v___y_1615_, 5);
v_quotContext_1668_ = lean_ctor_get(v___y_1615_, 10);
v_currMacroScope_1669_ = lean_ctor_get(v___y_1615_, 11);
v___x_1670_ = l_Lean_SourceInfo_fromRef(v_ref_1667_, v___x_1649_);
v___x_1671_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1672_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8);
v___x_1673_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__9));
lean_inc(v_currMacroScope_1669_);
lean_inc(v_quotContext_1668_);
v___x_1674_ = l_Lean_addMacroScope(v_quotContext_1668_, v___x_1673_, v_currMacroScope_1669_);
v___x_1675_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__12));
lean_inc_n(v___x_1670_, 2);
v___x_1676_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1670_);
lean_ctor_set(v___x_1676_, 1, v___x_1672_);
lean_ctor_set(v___x_1676_, 2, v___x_1674_);
lean_ctor_set(v___x_1676_, 3, v___x_1675_);
v___x_1677_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1678_ = l_Lean_Syntax_node1(v___x_1670_, v___x_1677_, v___x_1638_);
v___x_1679_ = l_Lean_Syntax_node2(v___x_1670_, v___x_1671_, v___x_1676_, v___x_1678_);
v_a_1641_ = v___x_1679_;
goto v___jp_1640_;
}
}
else
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1687_; 
lean_dec_ref(v___x_1639_);
lean_dec(v___x_1638_);
lean_del_object(v___x_1626_);
lean_dec(v_snd_1624_);
lean_dec(v_auxFunName_1607_);
lean_dec_ref(v_indVal_1606_);
v_a_1680_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1682_ = v___x_1650_;
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1650_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1685_; 
if (v_isShared_1683_ == 0)
{
v___x_1685_ = v___x_1682_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1680_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
else
{
lean_object* v_ref_1688_; uint8_t v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1698_; 
v_ref_1688_ = lean_ctor_get(v___y_1615_, 5);
v___x_1689_ = 0;
v___x_1690_ = l_Lean_SourceInfo_fromRef(v_ref_1688_, v___x_1689_);
v___x_1691_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
lean_inc(v_auxFunName_1607_);
v___x_1692_ = l_Lean_mkIdent(v_auxFunName_1607_);
v___x_1693_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1694_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_1695_ = l_Array_append___redArg(v___x_1694_, v_levelInsts_1608_);
v___x_1696_ = lean_array_push(v___x_1695_, v___x_1638_);
lean_inc(v___x_1690_);
if (v_isShared_1637_ == 0)
{
lean_ctor_set_tag(v___x_1636_, 1);
lean_ctor_set(v___x_1636_, 2, v___x_1696_);
lean_ctor_set(v___x_1636_, 1, v___x_1693_);
lean_ctor_set(v___x_1636_, 0, v___x_1690_);
v___x_1698_ = v___x_1636_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v___x_1690_);
lean_ctor_set(v_reuseFailAlloc_1700_, 1, v___x_1693_);
lean_ctor_set(v_reuseFailAlloc_1700_, 2, v___x_1696_);
v___x_1698_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
lean_object* v___x_1699_; 
v___x_1699_ = l_Lean_Syntax_node2(v___x_1690_, v___x_1691_, v___x_1692_, v___x_1698_);
v_a_1641_ = v___x_1699_;
goto v___jp_1640_;
}
}
v___jp_1640_:
{
lean_object* v___x_1642_; lean_object* v___x_1644_; 
v___x_1642_ = lean_array_push(v_snd_1624_, v_a_1641_);
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 1, v___x_1642_);
lean_ctor_set(v___x_1626_, 0, v___x_1639_);
v___x_1644_ = v___x_1626_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v___x_1639_);
lean_ctor_set(v_reuseFailAlloc_1648_, 1, v___x_1642_);
v___x_1644_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1645_ = lean_unsigned_to_nat(1u);
v___x_1646_ = lean_nat_add(v_a_1609_, v___x_1645_);
v___x_1647_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg(v_upperBound_1603_, v___x_1604_, v_xs_1605_, v_indVal_1606_, v_auxFunName_1607_, v_levelInsts_1608_, v___x_1646_, v___x_1644_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
return v___x_1647_;
}
}
}
}
else
{
lean_object* v_a_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1711_; 
lean_del_object(v___x_1626_);
lean_dec(v_snd_1624_);
lean_dec(v_fst_1623_);
lean_dec(v_a_1622_);
lean_dec(v_auxFunName_1607_);
lean_dec_ref(v_indVal_1606_);
v_a_1704_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1706_ = v___x_1631_;
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_a_1704_);
lean_dec(v___x_1631_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1709_; 
if (v_isShared_1707_ == 0)
{
v___x_1709_ = v___x_1706_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_a_1704_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
}
}
else
{
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
lean_dec_ref(v_b_1610_);
lean_dec(v_auxFunName_1607_);
lean_dec_ref(v_indVal_1606_);
v_a_1713_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1715_ = v___x_1621_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1621_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1713_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3___redArg___boxed(lean_object* v_upperBound_1721_, lean_object* v___x_1722_, lean_object* v_xs_1723_, lean_object* v_indVal_1724_, lean_object* v_auxFunName_1725_, lean_object* v_levelInsts_1726_, lean_object* v_a_1727_, lean_object* v_b_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3___redArg(v_upperBound_1721_, v___x_1722_, v_xs_1723_, v_indVal_1724_, v_auxFunName_1725_, v_levelInsts_1726_, v_a_1727_, v_b_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v_a_1727_);
lean_dec_ref(v_levelInsts_1726_);
lean_dec_ref(v_xs_1723_);
lean_dec(v___x_1722_);
lean_dec(v_upperBound_1721_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__2(size_t v_sz_1737_, size_t v_i_1738_, lean_object* v_bs_1739_){
_start:
{
uint8_t v___x_1740_; 
v___x_1740_ = lean_usize_dec_lt(v_i_1738_, v_sz_1737_);
if (v___x_1740_ == 0)
{
return v_bs_1739_;
}
else
{
lean_object* v_v_1741_; lean_object* v___x_1742_; lean_object* v_bs_x27_1743_; size_t v___x_1744_; size_t v___x_1745_; lean_object* v___x_1746_; 
v_v_1741_ = lean_array_uget(v_bs_1739_, v_i_1738_);
v___x_1742_ = lean_unsigned_to_nat(0u);
v_bs_x27_1743_ = lean_array_uset(v_bs_1739_, v_i_1738_, v___x_1742_);
v___x_1744_ = ((size_t)1ULL);
v___x_1745_ = lean_usize_add(v_i_1738_, v___x_1744_);
v___x_1746_ = lean_array_uset(v_bs_x27_1743_, v_i_1738_, v_v_1741_);
v_i_1738_ = v___x_1745_;
v_bs_1739_ = v___x_1746_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__2___boxed(lean_object* v_sz_1748_, lean_object* v_i_1749_, lean_object* v_bs_1750_){
_start:
{
size_t v_sz_boxed_1751_; size_t v_i_boxed_1752_; lean_object* v_res_1753_; 
v_sz_boxed_1751_ = lean_unbox_usize(v_sz_1748_);
lean_dec(v_sz_1748_);
v_i_boxed_1752_ = lean_unbox_usize(v_i_1749_);
lean_dec(v_i_1749_);
v_res_1753_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__2(v_sz_boxed_1751_, v_i_boxed_1752_, v_bs_1750_);
return v_res_1753_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__9));
v___x_1762_ = l_Lean_mkAtom(v___x_1761_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1(lean_object* v_indVal_1764_, lean_object* v___x_1765_, lean_object* v___x_1766_, lean_object* v_numParams_1767_, lean_object* v_header_1768_, lean_object* v_auxFunName_1769_, lean_object* v_levelInsts_1770_, lean_object* v_numFields_1771_, lean_object* v___f_1772_, lean_object* v_head_1773_, lean_object* v_a_1774_, lean_object* v_name_1775_, lean_object* v_xs_1776_, lean_object* v_x_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_){
_start:
{
lean_object* v_numIndices_1785_; lean_object* v___x_1786_; 
v_numIndices_1785_ = lean_ctor_get(v_indVal_1764_, 2);
lean_inc_ref(v___x_1766_);
lean_inc(v___x_1765_);
v___x_1786_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg(v_numIndices_1785_, v___x_1765_, v___x_1766_, v___y_1782_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v_a_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v_a_1787_ = lean_ctor_get(v___x_1786_, 0);
lean_inc(v_a_1787_);
lean_dec_ref_known(v___x_1786_, 1);
lean_inc_ref(v___x_1766_);
v___x_1788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1766_);
lean_ctor_set(v___x_1788_, 1, v___x_1766_);
lean_inc(v_auxFunName_1769_);
lean_inc_ref(v_indVal_1764_);
v___x_1789_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4___redArg(v_numParams_1767_, v_header_1768_, v_xs_1776_, v_indVal_1764_, v_auxFunName_1769_, v_levelInsts_1770_, v___x_1765_, v___x_1788_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v_a_1790_; lean_object* v_fst_1791_; lean_object* v_snd_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1911_; 
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
lean_inc(v_a_1790_);
lean_dec_ref_known(v___x_1789_, 1);
v_fst_1791_ = lean_ctor_get(v_a_1790_, 0);
v_snd_1792_ = lean_ctor_get(v_a_1790_, 1);
v_isSharedCheck_1911_ = !lean_is_exclusive(v_a_1790_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1794_ = v_a_1790_;
v_isShared_1795_ = v_isSharedCheck_1911_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_snd_1792_);
lean_inc(v_fst_1791_);
lean_dec(v_a_1790_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1911_;
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
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_fst_1791_);
lean_ctor_set(v_reuseFailAlloc_1910_, 1, v_snd_1792_);
v___x_1797_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
lean_object* v___x_1798_; 
v___x_1798_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3___redArg(v_numFields_1771_, v_numParams_1767_, v_xs_1776_, v_indVal_1764_, v_auxFunName_1769_, v_levelInsts_1770_, v___x_1765_, v___x_1797_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_);
lean_dec(v___x_1765_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_object* v_a_1799_; lean_object* v_ref_1800_; lean_object* v_quotContext_1801_; lean_object* v_currMacroScope_1802_; lean_object* v___x_1803_; 
v_a_1799_ = lean_ctor_get(v___x_1798_, 0);
lean_inc(v_a_1799_);
lean_dec_ref_known(v___x_1798_, 1);
v_ref_1800_ = lean_ctor_get(v___y_1782_, 5);
v_quotContext_1801_ = lean_ctor_get(v___y_1782_, 10);
v_currMacroScope_1802_ = lean_ctor_get(v___y_1782_, 11);
lean_inc_ref(v___f_1772_);
lean_inc(v___y_1783_);
lean_inc_ref(v___y_1782_);
lean_inc(v___y_1781_);
lean_inc_ref(v___y_1780_);
lean_inc(v___y_1779_);
lean_inc_ref(v___y_1778_);
v___x_1803_ = lean_apply_7(v___f_1772_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, lean_box(0));
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v_a_1804_; lean_object* v_fst_1805_; lean_object* v_snd_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1893_; 
v_a_1804_ = lean_ctor_get(v___x_1803_, 0);
lean_inc(v_a_1804_);
lean_dec_ref_known(v___x_1803_, 1);
v_fst_1805_ = lean_ctor_get(v_a_1799_, 0);
v_snd_1806_ = lean_ctor_get(v_a_1799_, 1);
v_isSharedCheck_1893_ = !lean_is_exclusive(v_a_1799_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1808_ = v_a_1799_;
v_isShared_1809_ = v_isSharedCheck_1893_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_snd_1806_);
lean_inc(v_fst_1805_);
lean_dec(v_a_1799_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1893_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
uint8_t v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1815_; 
v___x_1810_ = 0;
v___x_1811_ = l_Lean_SourceInfo_fromRef(v_ref_1800_, v___x_1810_);
v___x_1812_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1813_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__4));
lean_inc(v___x_1811_);
if (v_isShared_1809_ == 0)
{
lean_ctor_set_tag(v___x_1808_, 2);
lean_ctor_set(v___x_1808_, 1, v___x_1813_);
lean_ctor_set(v___x_1808_, 0, v___x_1811_);
v___x_1815_ = v___x_1808_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1811_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v___x_1813_);
v___x_1815_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___y_1832_; lean_object* v___x_1878_; 
v___x_1816_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__3));
v___x_1817_ = l_Lean_mkIdent(v_head_1773_);
lean_inc_n(v___x_1811_, 2);
v___x_1818_ = l_Lean_Syntax_node2(v___x_1811_, v___x_1816_, v___x_1815_, v___x_1817_);
v___x_1819_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__4));
v___x_1820_ = lean_box(0);
v___x_1821_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1822_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_1823_ = l_Array_append___redArg(v___x_1822_, v_fst_1805_);
lean_dec(v_fst_1805_);
v___x_1824_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1811_);
lean_ctor_set(v___x_1824_, 1, v___x_1821_);
lean_ctor_set(v___x_1824_, 2, v___x_1823_);
v___x_1825_ = l_Lean_Syntax_node2(v___x_1811_, v___x_1812_, v___x_1818_, v___x_1824_);
v___x_1826_ = lean_array_push(v_a_1787_, v___x_1825_);
v___x_1827_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__2, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__2_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__2);
lean_inc(v_currMacroScope_1802_);
lean_inc(v_quotContext_1801_);
v___x_1828_ = l_Lean_addMacroScope(v_quotContext_1801_, v___x_1819_, v_currMacroScope_1802_);
v___x_1829_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__10));
lean_inc(v_a_1804_);
v___x_1830_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1830_, 0, v_a_1804_);
lean_ctor_set(v___x_1830_, 1, v___x_1827_);
lean_ctor_set(v___x_1830_, 2, v___x_1828_);
lean_ctor_set(v___x_1830_, 3, v___x_1829_);
lean_inc(v_name_1775_);
v___x_1878_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_1820_, v_name_1775_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v___x_1879_; 
v___x_1879_ = l_Lean_quoteNameMk(v_name_1775_);
v___y_1832_ = v___x_1879_;
goto v___jp_1831_;
}
else
{
lean_object* v_val_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
lean_dec(v_name_1775_);
v_val_1880_ = lean_ctor_get(v___x_1878_, 0);
lean_inc(v_val_1880_);
lean_dec_ref_known(v___x_1878_, 1);
v___x_1881_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__16));
v___x_1882_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__17));
v___x_1883_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__18));
v___x_1884_ = lean_string_intercalate(v___x_1883_, v_val_1880_);
v___x_1885_ = lean_string_append(v___x_1882_, v___x_1884_);
lean_dec_ref(v___x_1884_);
v___x_1886_ = lean_box(2);
v___x_1887_ = l_Lean_Syntax_mkNameLit(v___x_1885_, v___x_1886_);
v___x_1888_ = lean_unsigned_to_nat(1u);
v___x_1889_ = lean_mk_empty_array_with_capacity(v___x_1888_);
v___x_1890_ = lean_array_push(v___x_1889_, v___x_1887_);
v___x_1891_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1886_);
lean_ctor_set(v___x_1891_, 1, v___x_1881_);
lean_ctor_set(v___x_1891_, 2, v___x_1890_);
v___y_1832_ = v___x_1891_;
goto v___jp_1831_;
}
v___jp_1831_:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1833_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__12));
v___x_1834_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__13));
lean_inc_n(v_a_1804_, 5);
v___x_1835_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1835_, 0, v_a_1804_);
lean_ctor_set(v___x_1835_, 1, v___x_1834_);
v___x_1836_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__9));
v___x_1837_ = l_Lean_Syntax_SepArray_ofElems(v___x_1836_, v_a_1774_);
v___x_1838_ = l_Array_append___redArg(v___x_1822_, v___x_1837_);
lean_dec_ref(v___x_1837_);
v___x_1839_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1839_, 0, v_a_1804_);
lean_ctor_set(v___x_1839_, 1, v___x_1821_);
lean_ctor_set(v___x_1839_, 2, v___x_1838_);
v___x_1840_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__14));
v___x_1841_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1841_, 0, v_a_1804_);
lean_ctor_set(v___x_1841_, 1, v___x_1840_);
v___x_1842_ = l_Lean_Syntax_node3(v_a_1804_, v___x_1833_, v___x_1835_, v___x_1839_, v___x_1841_);
v___x_1843_ = l_Lean_Syntax_node2(v_a_1804_, v___x_1821_, v___y_1832_, v___x_1842_);
v___x_1844_ = l_Lean_Syntax_node2(v_a_1804_, v___x_1812_, v___x_1830_, v___x_1843_);
v___x_1845_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm(v___x_1844_, v_snd_1806_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_);
lean_dec(v_snd_1806_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; lean_object* v___x_1847_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_a_1846_);
lean_dec_ref_known(v___x_1845_, 1);
lean_inc(v___y_1783_);
lean_inc_ref(v___y_1782_);
lean_inc(v___y_1781_);
lean_inc_ref(v___y_1780_);
lean_inc(v___y_1779_);
lean_inc_ref(v___y_1778_);
v___x_1847_ = lean_apply_7(v___f_1772_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, lean_box(0));
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1869_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1850_ = v___x_1847_;
v_isShared_1851_ = v_isSharedCheck_1869_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1847_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1869_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; size_t v_sz_1855_; size_t v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1867_; 
v___x_1852_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__1));
v___x_1853_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__2));
lean_inc_n(v_a_1848_, 4);
v___x_1854_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1854_, 0, v_a_1848_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
v_sz_1855_ = lean_array_size(v___x_1826_);
v___x_1856_ = ((size_t)0ULL);
v___x_1857_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__2(v_sz_1855_, v___x_1856_, v___x_1826_);
v___x_1858_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__3);
v___x_1859_ = l_Lean_mkSepArray(v___x_1857_, v___x_1858_);
lean_dec_ref(v___x_1857_);
v___x_1860_ = l_Array_append___redArg(v___x_1822_, v___x_1859_);
lean_dec_ref(v___x_1859_);
v___x_1861_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1861_, 0, v_a_1848_);
lean_ctor_set(v___x_1861_, 1, v___x_1821_);
lean_ctor_set(v___x_1861_, 2, v___x_1860_);
v___x_1862_ = l_Lean_Syntax_node1(v_a_1848_, v___x_1821_, v___x_1861_);
v___x_1863_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__4));
v___x_1864_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1864_, 0, v_a_1848_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
v___x_1865_ = l_Lean_Syntax_node4(v_a_1848_, v___x_1852_, v___x_1854_, v___x_1862_, v___x_1864_, v_a_1846_);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v___x_1865_);
v___x_1867_ = v___x_1850_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1865_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
lean_dec(v_a_1846_);
lean_dec_ref(v___x_1826_);
v_a_1870_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1847_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1847_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
else
{
lean_dec_ref(v___x_1826_);
lean_dec_ref(v___f_1772_);
return v___x_1845_;
}
}
}
}
}
else
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
lean_dec(v_a_1799_);
lean_dec(v_a_1787_);
lean_dec(v_name_1775_);
lean_dec(v_head_1773_);
lean_dec_ref(v___f_1772_);
v_a_1894_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v___x_1803_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1803_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1894_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
}
else
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
lean_dec(v_a_1787_);
lean_dec(v_name_1775_);
lean_dec(v_head_1773_);
lean_dec_ref(v___f_1772_);
v_a_1902_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1904_ = v___x_1798_;
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1798_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1902_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
}
}
else
{
lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1919_; 
lean_dec(v_a_1787_);
lean_dec(v_name_1775_);
lean_dec(v_head_1773_);
lean_dec_ref(v___f_1772_);
lean_dec(v_auxFunName_1769_);
lean_dec(v___x_1765_);
lean_dec_ref(v_indVal_1764_);
v_a_1912_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1914_ = v___x_1789_;
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1789_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1917_; 
if (v_isShared_1915_ == 0)
{
v___x_1917_ = v___x_1914_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1912_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
else
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1927_; 
lean_dec(v_name_1775_);
lean_dec(v_head_1773_);
lean_dec_ref(v___f_1772_);
lean_dec(v_auxFunName_1769_);
lean_dec_ref(v___x_1766_);
lean_dec(v___x_1765_);
lean_dec_ref(v_indVal_1764_);
v_a_1920_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1922_ = v___x_1786_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1786_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_a_1920_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_indVal_1928_ = _args[0];
lean_object* v___x_1929_ = _args[1];
lean_object* v___x_1930_ = _args[2];
lean_object* v_numParams_1931_ = _args[3];
lean_object* v_header_1932_ = _args[4];
lean_object* v_auxFunName_1933_ = _args[5];
lean_object* v_levelInsts_1934_ = _args[6];
lean_object* v_numFields_1935_ = _args[7];
lean_object* v___f_1936_ = _args[8];
lean_object* v_head_1937_ = _args[9];
lean_object* v_a_1938_ = _args[10];
lean_object* v_name_1939_ = _args[11];
lean_object* v_xs_1940_ = _args[12];
lean_object* v_x_1941_ = _args[13];
lean_object* v___y_1942_ = _args[14];
lean_object* v___y_1943_ = _args[15];
lean_object* v___y_1944_ = _args[16];
lean_object* v___y_1945_ = _args[17];
lean_object* v___y_1946_ = _args[18];
lean_object* v___y_1947_ = _args[19];
lean_object* v___y_1948_ = _args[20];
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1(v_indVal_1928_, v___x_1929_, v___x_1930_, v_numParams_1931_, v_header_1932_, v_auxFunName_1933_, v_levelInsts_1934_, v_numFields_1935_, v___f_1936_, v_head_1937_, v_a_1938_, v_name_1939_, v_xs_1940_, v_x_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec_ref(v_x_1941_);
lean_dec_ref(v_xs_1940_);
lean_dec_ref(v_a_1938_);
lean_dec(v_numFields_1935_);
lean_dec_ref(v_levelInsts_1934_);
lean_dec_ref(v_header_1932_);
lean_dec(v_numParams_1931_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg(lean_object* v_a_1951_, lean_object* v_indVal_1952_, lean_object* v_auxFunName_1953_, lean_object* v_levelInsts_1954_, lean_object* v_header_1955_, lean_object* v_as_x27_1956_, lean_object* v_b_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
if (lean_obj_tag(v_as_x27_1956_) == 0)
{
lean_object* v___x_1965_; 
lean_dec_ref(v_header_1955_);
lean_dec_ref(v_levelInsts_1954_);
lean_dec(v_auxFunName_1953_);
lean_dec_ref(v_indVal_1952_);
lean_dec_ref(v_a_1951_);
v___x_1965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1965_, 0, v_b_1957_);
return v___x_1965_;
}
else
{
lean_object* v_head_1966_; lean_object* v_tail_1967_; lean_object* v___x_1968_; 
v_head_1966_ = lean_ctor_get(v_as_x27_1956_, 0);
v_tail_1967_ = lean_ctor_get(v_as_x27_1956_, 1);
lean_inc(v_head_1966_);
v___x_1968_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1(v_head_1966_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; lean_object* v_toConstantVal_1970_; lean_object* v_numParams_1971_; lean_object* v_numFields_1972_; lean_object* v_name_1973_; lean_object* v_type_1974_; lean_object* v___f_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___f_1978_; uint8_t v___x_1979_; lean_object* v___x_1980_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_a_1969_);
lean_dec_ref_known(v___x_1968_, 1);
v_toConstantVal_1970_ = lean_ctor_get(v_a_1969_, 0);
lean_inc_ref(v_toConstantVal_1970_);
v_numParams_1971_ = lean_ctor_get(v_a_1969_, 3);
lean_inc(v_numParams_1971_);
v_numFields_1972_ = lean_ctor_get(v_a_1969_, 4);
lean_inc(v_numFields_1972_);
lean_dec(v_a_1969_);
v_name_1973_ = lean_ctor_get(v_toConstantVal_1970_, 0);
lean_inc(v_name_1973_);
v_type_1974_ = lean_ctor_get(v_toConstantVal_1970_, 2);
lean_inc_ref(v_type_1974_);
lean_dec_ref(v_toConstantVal_1970_);
v___f_1975_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___closed__0));
v___x_1976_ = lean_unsigned_to_nat(0u);
v___x_1977_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__0));
lean_inc_ref(v_a_1951_);
lean_inc(v_head_1966_);
lean_inc_ref(v_levelInsts_1954_);
lean_inc(v_auxFunName_1953_);
lean_inc_ref(v_header_1955_);
lean_inc_ref(v_indVal_1952_);
v___f_1978_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___boxed), 21, 12);
lean_closure_set(v___f_1978_, 0, v_indVal_1952_);
lean_closure_set(v___f_1978_, 1, v___x_1976_);
lean_closure_set(v___f_1978_, 2, v___x_1977_);
lean_closure_set(v___f_1978_, 3, v_numParams_1971_);
lean_closure_set(v___f_1978_, 4, v_header_1955_);
lean_closure_set(v___f_1978_, 5, v_auxFunName_1953_);
lean_closure_set(v___f_1978_, 6, v_levelInsts_1954_);
lean_closure_set(v___f_1978_, 7, v_numFields_1972_);
lean_closure_set(v___f_1978_, 8, v___f_1975_);
lean_closure_set(v___f_1978_, 9, v_head_1966_);
lean_closure_set(v___f_1978_, 10, v_a_1951_);
lean_closure_set(v___f_1978_, 11, v_name_1973_);
v___x_1979_ = 0;
v___x_1980_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg(v_type_1974_, v___f_1978_, v___x_1979_, v___x_1979_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v_a_1981_; lean_object* v___x_1982_; 
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_a_1981_);
lean_dec_ref_known(v___x_1980_, 1);
v___x_1982_ = lean_array_push(v_b_1957_, v_a_1981_);
v_as_x27_1956_ = v_tail_1967_;
v_b_1957_ = v___x_1982_;
goto _start;
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1991_; 
lean_dec_ref(v_b_1957_);
lean_dec_ref(v_header_1955_);
lean_dec_ref(v_levelInsts_1954_);
lean_dec(v_auxFunName_1953_);
lean_dec_ref(v_indVal_1952_);
lean_dec_ref(v_a_1951_);
v_a_1984_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1986_ = v___x_1980_;
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1980_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1987_ == 0)
{
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
else
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
lean_dec_ref(v_b_1957_);
lean_dec_ref(v_header_1955_);
lean_dec_ref(v_levelInsts_1954_);
lean_dec(v_auxFunName_1953_);
lean_dec_ref(v_indVal_1952_);
lean_dec_ref(v_a_1951_);
v_a_1992_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1968_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1968_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1992_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___boxed(lean_object* v_a_2000_, lean_object* v_indVal_2001_, lean_object* v_auxFunName_2002_, lean_object* v_levelInsts_2003_, lean_object* v_header_2004_, lean_object* v_as_x27_2005_, lean_object* v_b_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg(v_a_2000_, v_indVal_2001_, v_auxFunName_2002_, v_levelInsts_2003_, v_header_2004_, v_as_x27_2005_, v_b_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
lean_dec(v_as_x27_2005_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__7(size_t v_sz_2015_, size_t v_i_2016_, lean_object* v_bs_2017_){
_start:
{
uint8_t v___x_2018_; 
v___x_2018_ = lean_usize_dec_lt(v_i_2016_, v_sz_2015_);
if (v___x_2018_ == 0)
{
return v_bs_2017_;
}
else
{
lean_object* v_v_2019_; lean_object* v___x_2020_; lean_object* v_bs_x27_2021_; size_t v___x_2022_; size_t v___x_2023_; lean_object* v___x_2024_; 
v_v_2019_ = lean_array_uget(v_bs_2017_, v_i_2016_);
v___x_2020_ = lean_unsigned_to_nat(0u);
v_bs_x27_2021_ = lean_array_uset(v_bs_2017_, v_i_2016_, v___x_2020_);
v___x_2022_ = ((size_t)1ULL);
v___x_2023_ = lean_usize_add(v_i_2016_, v___x_2022_);
v___x_2024_ = lean_array_uset(v_bs_x27_2021_, v_i_2016_, v_v_2019_);
v_i_2016_ = v___x_2023_;
v_bs_2017_ = v___x_2024_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__7___boxed(lean_object* v_sz_2026_, lean_object* v_i_2027_, lean_object* v_bs_2028_){
_start:
{
size_t v_sz_boxed_2029_; size_t v_i_boxed_2030_; lean_object* v_res_2031_; 
v_sz_boxed_2029_ = lean_unbox_usize(v_sz_2026_);
lean_dec(v_sz_2026_);
v_i_boxed_2030_ = lean_unbox_usize(v_i_2027_);
lean_dec(v_i_2027_);
v_res_2031_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__7(v_sz_boxed_2029_, v_i_boxed_2030_, v_bs_2028_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts(lean_object* v_header_2032_, lean_object* v_indVal_2033_, lean_object* v_auxFunName_2034_, lean_object* v_levelInsts_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_){
_start:
{
size_t v_sz_2043_; size_t v___x_2044_; lean_object* v___x_2045_; 
v_sz_2043_ = lean_array_size(v_levelInsts_2035_);
v___x_2044_ = ((size_t)0ULL);
lean_inc_ref(v_levelInsts_2035_);
v___x_2045_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg(v_sz_2043_, v___x_2044_, v_levelInsts_2035_, v_a_2040_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; lean_object* v_ctors_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
lean_inc(v_a_2046_);
lean_dec_ref_known(v___x_2045_, 1);
v_ctors_2047_ = lean_ctor_get(v_indVal_2033_, 4);
lean_inc(v_ctors_2047_);
v___x_2048_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__0));
v___x_2049_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg(v_a_2046_, v_indVal_2033_, v_auxFunName_2034_, v_levelInsts_2035_, v_header_2032_, v_ctors_2047_, v___x_2048_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_);
lean_dec(v_ctors_2047_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2059_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2052_ = v___x_2049_;
v_isShared_2053_ = v_isSharedCheck_2059_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2049_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2059_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
size_t v_sz_2054_; lean_object* v___x_2055_; lean_object* v___x_2057_; 
v_sz_2054_ = lean_array_size(v_a_2050_);
v___x_2055_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__7(v_sz_2054_, v___x_2044_, v_a_2050_);
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 0, v___x_2055_);
v___x_2057_ = v___x_2052_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v___x_2055_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
else
{
return v___x_2049_;
}
}
else
{
lean_dec_ref(v_levelInsts_2035_);
lean_dec(v_auxFunName_2034_);
lean_dec_ref(v_indVal_2033_);
lean_dec_ref(v_header_2032_);
return v___x_2045_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts___boxed(lean_object* v_header_2060_, lean_object* v_indVal_2061_, lean_object* v_auxFunName_2062_, lean_object* v_levelInsts_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts(v_header_2060_, v_indVal_2061_, v_auxFunName_2062_, v_levelInsts_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_);
lean_dec(v_a_2069_);
lean_dec_ref(v_a_2068_);
lean_dec(v_a_2067_);
lean_dec_ref(v_a_2066_);
lean_dec(v_a_2065_);
lean_dec_ref(v_a_2064_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0(size_t v_sz_2072_, size_t v_i_2073_, lean_object* v_bs_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_){
_start:
{
lean_object* v___x_2082_; 
v___x_2082_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg(v_sz_2072_, v_i_2073_, v_bs_2074_, v___y_2079_);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___boxed(lean_object* v_sz_2083_, lean_object* v_i_2084_, lean_object* v_bs_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_){
_start:
{
size_t v_sz_boxed_2093_; size_t v_i_boxed_2094_; lean_object* v_res_2095_; 
v_sz_boxed_2093_ = lean_unbox_usize(v_sz_2083_);
lean_dec(v_sz_2083_);
v_i_boxed_2094_ = lean_unbox_usize(v_i_2084_);
lean_dec(v_i_2084_);
v_res_2095_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0(v_sz_boxed_2093_, v_i_boxed_2094_, v_bs_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3(lean_object* v_upperBound_2096_, lean_object* v___x_2097_, lean_object* v_xs_2098_, lean_object* v_indVal_2099_, lean_object* v_auxFunName_2100_, lean_object* v_levelInsts_2101_, lean_object* v_inst_2102_, lean_object* v_R_2103_, lean_object* v_a_2104_, lean_object* v_b_2105_, lean_object* v_c_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
lean_object* v___x_2114_; 
v___x_2114_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3___redArg(v_upperBound_2096_, v___x_2097_, v_xs_2098_, v_indVal_2099_, v_auxFunName_2100_, v_levelInsts_2101_, v_a_2104_, v_b_2105_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3___boxed(lean_object** _args){
lean_object* v_upperBound_2115_ = _args[0];
lean_object* v___x_2116_ = _args[1];
lean_object* v_xs_2117_ = _args[2];
lean_object* v_indVal_2118_ = _args[3];
lean_object* v_auxFunName_2119_ = _args[4];
lean_object* v_levelInsts_2120_ = _args[5];
lean_object* v_inst_2121_ = _args[6];
lean_object* v_R_2122_ = _args[7];
lean_object* v_a_2123_ = _args[8];
lean_object* v_b_2124_ = _args[9];
lean_object* v_c_2125_ = _args[10];
lean_object* v___y_2126_ = _args[11];
lean_object* v___y_2127_ = _args[12];
lean_object* v___y_2128_ = _args[13];
lean_object* v___y_2129_ = _args[14];
lean_object* v___y_2130_ = _args[15];
lean_object* v___y_2131_ = _args[16];
lean_object* v___y_2132_ = _args[17];
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3(v_upperBound_2115_, v___x_2116_, v_xs_2117_, v_indVal_2118_, v_auxFunName_2119_, v_levelInsts_2120_, v_inst_2121_, v_R_2122_, v_a_2123_, v_b_2124_, v_c_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec(v_a_2123_);
lean_dec_ref(v_levelInsts_2120_);
lean_dec_ref(v_xs_2117_);
lean_dec(v___x_2116_);
lean_dec(v_upperBound_2115_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4(lean_object* v_upperBound_2134_, lean_object* v_header_2135_, lean_object* v_xs_2136_, lean_object* v_indVal_2137_, lean_object* v_auxFunName_2138_, lean_object* v_levelInsts_2139_, lean_object* v_inst_2140_, lean_object* v_R_2141_, lean_object* v_a_2142_, lean_object* v_b_2143_, lean_object* v_c_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v___x_2152_; 
v___x_2152_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4___redArg(v_upperBound_2134_, v_header_2135_, v_xs_2136_, v_indVal_2137_, v_auxFunName_2138_, v_levelInsts_2139_, v_a_2142_, v_b_2143_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_2153_ = _args[0];
lean_object* v_header_2154_ = _args[1];
lean_object* v_xs_2155_ = _args[2];
lean_object* v_indVal_2156_ = _args[3];
lean_object* v_auxFunName_2157_ = _args[4];
lean_object* v_levelInsts_2158_ = _args[5];
lean_object* v_inst_2159_ = _args[6];
lean_object* v_R_2160_ = _args[7];
lean_object* v_a_2161_ = _args[8];
lean_object* v_b_2162_ = _args[9];
lean_object* v_c_2163_ = _args[10];
lean_object* v___y_2164_ = _args[11];
lean_object* v___y_2165_ = _args[12];
lean_object* v___y_2166_ = _args[13];
lean_object* v___y_2167_ = _args[14];
lean_object* v___y_2168_ = _args[15];
lean_object* v___y_2169_ = _args[16];
lean_object* v___y_2170_ = _args[17];
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4(v_upperBound_2153_, v_header_2154_, v_xs_2155_, v_indVal_2156_, v_auxFunName_2157_, v_levelInsts_2158_, v_inst_2159_, v_R_2160_, v_a_2161_, v_b_2162_, v_c_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v_a_2161_);
lean_dec_ref(v_levelInsts_2158_);
lean_dec_ref(v_xs_2155_);
lean_dec_ref(v_header_2154_);
lean_dec(v_upperBound_2153_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5(lean_object* v_upperBound_2172_, lean_object* v_inst_2173_, lean_object* v_R_2174_, lean_object* v_a_2175_, lean_object* v_b_2176_, lean_object* v_c_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
lean_object* v___x_2185_; 
v___x_2185_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg(v_upperBound_2172_, v_a_2175_, v_b_2176_, v___y_2182_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___boxed(lean_object* v_upperBound_2186_, lean_object* v_inst_2187_, lean_object* v_R_2188_, lean_object* v_a_2189_, lean_object* v_b_2190_, lean_object* v_c_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5(v_upperBound_2186_, v_inst_2187_, v_R_2188_, v_a_2189_, v_b_2190_, v_c_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec(v_upperBound_2186_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6(lean_object* v_a_2200_, lean_object* v_indVal_2201_, lean_object* v_auxFunName_2202_, lean_object* v_levelInsts_2203_, lean_object* v_header_2204_, lean_object* v_as_2205_, lean_object* v_as_x27_2206_, lean_object* v_b_2207_, lean_object* v_a_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
lean_object* v___x_2216_; 
v___x_2216_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg(v_a_2200_, v_indVal_2201_, v_auxFunName_2202_, v_levelInsts_2203_, v_header_2204_, v_as_x27_2206_, v_b_2207_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___boxed(lean_object* v_a_2217_, lean_object* v_indVal_2218_, lean_object* v_auxFunName_2219_, lean_object* v_levelInsts_2220_, lean_object* v_header_2221_, lean_object* v_as_2222_, lean_object* v_as_x27_2223_, lean_object* v_b_2224_, lean_object* v_a_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6(v_a_2217_, v_indVal_2218_, v_auxFunName_2219_, v_levelInsts_2220_, v_header_2221_, v_as_2222_, v_as_x27_2223_, v_b_2224_, v_a_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v_as_x27_2223_);
lean_dec(v_as_2222_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4(lean_object* v_upperBound_2234_, lean_object* v___x_2235_, lean_object* v_xs_2236_, lean_object* v_indVal_2237_, lean_object* v_auxFunName_2238_, lean_object* v_levelInsts_2239_, lean_object* v_inst_2240_, lean_object* v_R_2241_, lean_object* v_a_2242_, lean_object* v_b_2243_, lean_object* v_c_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_){
_start:
{
lean_object* v___x_2252_; 
v___x_2252_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg(v_upperBound_2234_, v___x_2235_, v_xs_2236_, v_indVal_2237_, v_auxFunName_2238_, v_levelInsts_2239_, v_a_2242_, v_b_2243_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_2253_ = _args[0];
lean_object* v___x_2254_ = _args[1];
lean_object* v_xs_2255_ = _args[2];
lean_object* v_indVal_2256_ = _args[3];
lean_object* v_auxFunName_2257_ = _args[4];
lean_object* v_levelInsts_2258_ = _args[5];
lean_object* v_inst_2259_ = _args[6];
lean_object* v_R_2260_ = _args[7];
lean_object* v_a_2261_ = _args[8];
lean_object* v_b_2262_ = _args[9];
lean_object* v_c_2263_ = _args[10];
lean_object* v___y_2264_ = _args[11];
lean_object* v___y_2265_ = _args[12];
lean_object* v___y_2266_ = _args[13];
lean_object* v___y_2267_ = _args[14];
lean_object* v___y_2268_ = _args[15];
lean_object* v___y_2269_ = _args[16];
lean_object* v___y_2270_ = _args[17];
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4(v_upperBound_2253_, v___x_2254_, v_xs_2255_, v_indVal_2256_, v_auxFunName_2257_, v_levelInsts_2258_, v_inst_2259_, v_R_2260_, v_a_2261_, v_b_2262_, v_c_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec_ref(v_levelInsts_2258_);
lean_dec_ref(v_xs_2255_);
lean_dec(v___x_2254_);
lean_dec(v_upperBound_2253_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6(lean_object* v_upperBound_2272_, lean_object* v_header_2273_, lean_object* v_xs_2274_, lean_object* v_indVal_2275_, lean_object* v_auxFunName_2276_, lean_object* v_levelInsts_2277_, lean_object* v_inst_2278_, lean_object* v_R_2279_, lean_object* v_a_2280_, lean_object* v_b_2281_, lean_object* v_c_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_){
_start:
{
lean_object* v___x_2290_; 
v___x_2290_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6___redArg(v_upperBound_2272_, v_header_2273_, v_xs_2274_, v_indVal_2275_, v_auxFunName_2276_, v_levelInsts_2277_, v_a_2280_, v_b_2281_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6___boxed(lean_object** _args){
lean_object* v_upperBound_2291_ = _args[0];
lean_object* v_header_2292_ = _args[1];
lean_object* v_xs_2293_ = _args[2];
lean_object* v_indVal_2294_ = _args[3];
lean_object* v_auxFunName_2295_ = _args[4];
lean_object* v_levelInsts_2296_ = _args[5];
lean_object* v_inst_2297_ = _args[6];
lean_object* v_R_2298_ = _args[7];
lean_object* v_a_2299_ = _args[8];
lean_object* v_b_2300_ = _args[9];
lean_object* v_c_2301_ = _args[10];
lean_object* v___y_2302_ = _args[11];
lean_object* v___y_2303_ = _args[12];
lean_object* v___y_2304_ = _args[13];
lean_object* v___y_2305_ = _args[14];
lean_object* v___y_2306_ = _args[15];
lean_object* v___y_2307_ = _args[16];
lean_object* v___y_2308_ = _args[17];
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6(v_upperBound_2291_, v_header_2292_, v_xs_2293_, v_indVal_2294_, v_auxFunName_2295_, v_levelInsts_2296_, v_inst_2297_, v_R_2298_, v_a_2299_, v_b_2300_, v_c_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
lean_dec_ref(v_levelInsts_2296_);
lean_dec_ref(v_xs_2293_);
lean_dec_ref(v_header_2292_);
lean_dec(v_upperBound_2291_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody(lean_object* v_header_2323_, lean_object* v_indVal_2324_, lean_object* v_auxFunName_2325_, lean_object* v_levelInsts_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_){
_start:
{
lean_object* v___x_2334_; 
lean_inc_ref(v_indVal_2324_);
lean_inc_ref(v_header_2323_);
v___x_2334_ = l_Lean_Elab_Deriving_mkDiscrs(v_header_2323_, v_indVal_2324_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; lean_object* v___x_2336_; 
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2335_);
lean_dec_ref_known(v___x_2334_, 1);
v___x_2336_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts(v_header_2323_, v_indVal_2324_, v_auxFunName_2325_, v_levelInsts_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2367_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2339_ = v___x_2336_;
v_isShared_2340_ = v_isSharedCheck_2367_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2336_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2367_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v_ref_2341_; uint8_t v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; size_t v_sz_2350_; size_t v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2365_; 
v_ref_2341_ = lean_ctor_get(v_a_2331_, 5);
v___x_2342_ = 0;
v___x_2343_ = l_Lean_SourceInfo_fromRef(v_ref_2341_, v___x_2342_);
v___x_2344_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__0));
v___x_2345_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__1));
lean_inc_n(v___x_2343_, 6);
v___x_2346_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2343_);
lean_ctor_set(v___x_2346_, 1, v___x_2344_);
v___x_2347_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_2348_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_2349_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2343_);
lean_ctor_set(v___x_2349_, 1, v___x_2347_);
lean_ctor_set(v___x_2349_, 2, v___x_2348_);
v_sz_2350_ = lean_array_size(v_a_2335_);
v___x_2351_ = ((size_t)0ULL);
v___x_2352_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__2(v_sz_2350_, v___x_2351_, v_a_2335_);
v___x_2353_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__3);
v___x_2354_ = l_Lean_mkSepArray(v___x_2352_, v___x_2353_);
lean_dec_ref(v___x_2352_);
v___x_2355_ = l_Array_append___redArg(v___x_2348_, v___x_2354_);
lean_dec_ref(v___x_2354_);
v___x_2356_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2343_);
lean_ctor_set(v___x_2356_, 1, v___x_2347_);
lean_ctor_set(v___x_2356_, 2, v___x_2355_);
v___x_2357_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__2));
v___x_2358_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2343_);
lean_ctor_set(v___x_2358_, 1, v___x_2357_);
v___x_2359_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__4));
v___x_2360_ = l_Array_append___redArg(v___x_2348_, v_a_2337_);
lean_dec(v_a_2337_);
v___x_2361_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2343_);
lean_ctor_set(v___x_2361_, 1, v___x_2347_);
lean_ctor_set(v___x_2361_, 2, v___x_2360_);
v___x_2362_ = l_Lean_Syntax_node1(v___x_2343_, v___x_2359_, v___x_2361_);
lean_inc_ref(v___x_2349_);
v___x_2363_ = l_Lean_Syntax_node6(v___x_2343_, v___x_2345_, v___x_2346_, v___x_2349_, v___x_2349_, v___x_2356_, v___x_2358_, v___x_2362_);
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 0, v___x_2363_);
v___x_2365_ = v___x_2339_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v___x_2363_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
lean_dec(v_a_2335_);
v_a_2368_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2336_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2336_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2368_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
else
{
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2383_; 
lean_dec_ref(v_levelInsts_2326_);
lean_dec(v_auxFunName_2325_);
lean_dec_ref(v_indVal_2324_);
lean_dec_ref(v_header_2323_);
v_a_2376_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2378_ = v___x_2334_;
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2334_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2381_; 
if (v_isShared_2379_ == 0)
{
v___x_2381_ = v___x_2378_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_a_2376_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___boxed(lean_object* v_header_2384_, lean_object* v_indVal_2385_, lean_object* v_auxFunName_2386_, lean_object* v_levelInsts_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_){
_start:
{
lean_object* v_res_2395_; 
v_res_2395_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody(v_header_2384_, v_indVal_2385_, v_auxFunName_2386_, v_levelInsts_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_);
lean_dec(v_a_2393_);
lean_dec_ref(v_a_2392_);
lean_dec(v_a_2391_);
lean_dec_ref(v_a_2390_);
lean_dec(v_a_2389_);
lean_dec_ref(v_a_2388_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__0___redArg(lean_object* v_a_2396_, lean_object* v_b_2397_){
_start:
{
lean_object* v_array_2398_; lean_object* v_start_2399_; lean_object* v_stop_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2413_; 
v_array_2398_ = lean_ctor_get(v_a_2396_, 0);
v_start_2399_ = lean_ctor_get(v_a_2396_, 1);
v_stop_2400_ = lean_ctor_get(v_a_2396_, 2);
v_isSharedCheck_2413_ = !lean_is_exclusive(v_a_2396_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2402_ = v_a_2396_;
v_isShared_2403_ = v_isSharedCheck_2413_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_stop_2400_);
lean_inc(v_start_2399_);
lean_inc(v_array_2398_);
lean_dec(v_a_2396_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2413_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
uint8_t v___x_2404_; 
v___x_2404_ = lean_nat_dec_lt(v_start_2399_, v_stop_2400_);
if (v___x_2404_ == 0)
{
lean_del_object(v___x_2402_);
lean_dec(v_stop_2400_);
lean_dec(v_start_2399_);
lean_dec_ref(v_array_2398_);
return v_b_2397_;
}
else
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2408_; 
v___x_2405_ = lean_unsigned_to_nat(1u);
v___x_2406_ = lean_nat_add(v_start_2399_, v___x_2405_);
lean_inc_ref(v_array_2398_);
if (v_isShared_2403_ == 0)
{
lean_ctor_set(v___x_2402_, 1, v___x_2406_);
v___x_2408_ = v___x_2402_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_array_2398_);
lean_ctor_set(v_reuseFailAlloc_2412_, 1, v___x_2406_);
lean_ctor_set(v_reuseFailAlloc_2412_, 2, v_stop_2400_);
v___x_2408_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2409_ = lean_array_fget(v_array_2398_, v_start_2399_);
lean_dec(v_start_2399_);
lean_dec_ref(v_array_2398_);
v___x_2410_ = lean_array_push(v_b_2397_, v___x_2409_);
v_a_2396_ = v___x_2408_;
v_b_2397_ = v___x_2410_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__12(void){
_start:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2444_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__3));
v___x_2445_ = l_String_toRawSubstring_x27(v___x_2444_);
return v___x_2445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1(lean_object* v_argNames_2521_, lean_object* v_levelInsts_2522_, lean_object* v_as_2523_, size_t v_sz_2524_, size_t v_i_2525_, lean_object* v_b_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_){
_start:
{
uint8_t v___x_2534_; 
v___x_2534_ = lean_usize_dec_lt(v_i_2525_, v_sz_2524_);
if (v___x_2534_ == 0)
{
lean_object* v___x_2535_; 
lean_dec_ref(v_argNames_2521_);
v___x_2535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2535_, 0, v_b_2526_);
return v___x_2535_;
}
else
{
lean_object* v_snd_2536_; lean_object* v_fst_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2709_; 
v_snd_2536_ = lean_ctor_get(v_b_2526_, 1);
v_fst_2537_ = lean_ctor_get(v_b_2526_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v_b_2526_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2539_ = v_b_2526_;
v_isShared_2540_ = v_isSharedCheck_2709_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_snd_2536_);
lean_inc(v_fst_2537_);
lean_dec(v_b_2526_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2709_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v_array_2541_; lean_object* v_start_2542_; lean_object* v_stop_2543_; uint8_t v___x_2544_; 
v_array_2541_ = lean_ctor_get(v_snd_2536_, 0);
v_start_2542_ = lean_ctor_get(v_snd_2536_, 1);
v_stop_2543_ = lean_ctor_get(v_snd_2536_, 2);
v___x_2544_ = lean_nat_dec_lt(v_start_2542_, v_stop_2543_);
if (v___x_2544_ == 0)
{
lean_object* v___x_2546_; 
lean_dec_ref(v_argNames_2521_);
if (v_isShared_2540_ == 0)
{
v___x_2546_ = v___x_2539_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_fst_2537_);
lean_ctor_set(v_reuseFailAlloc_2548_, 1, v_snd_2536_);
v___x_2546_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
lean_object* v___x_2547_; 
v___x_2547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2546_);
return v___x_2547_;
}
}
else
{
lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2705_; 
lean_inc(v_stop_2543_);
lean_inc(v_start_2542_);
lean_inc_ref(v_array_2541_);
v_isSharedCheck_2705_ = !lean_is_exclusive(v_snd_2536_);
if (v_isSharedCheck_2705_ == 0)
{
lean_object* v_unused_2706_; lean_object* v_unused_2707_; lean_object* v_unused_2708_; 
v_unused_2706_ = lean_ctor_get(v_snd_2536_, 2);
lean_dec(v_unused_2706_);
v_unused_2707_ = lean_ctor_get(v_snd_2536_, 1);
lean_dec(v_unused_2707_);
v_unused_2708_ = lean_ctor_get(v_snd_2536_, 0);
lean_dec(v_unused_2708_);
v___x_2550_ = v_snd_2536_;
v_isShared_2551_ = v_isSharedCheck_2705_;
goto v_resetjp_2549_;
}
else
{
lean_dec(v_snd_2536_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2705_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v_a_2552_; lean_object* v___x_2553_; 
v_a_2552_ = lean_array_uget_borrowed(v_as_2523_, v_i_2525_);
lean_inc(v_a_2552_);
v___x_2553_ = l_Lean_Elab_Deriving_mkInductArgNames(v_a_2552_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v_a_2554_; lean_object* v_numParams_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2560_; 
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
lean_inc(v_a_2554_);
lean_dec_ref_known(v___x_2553_, 1);
v_numParams_2555_ = lean_ctor_get(v_a_2552_, 1);
v___x_2556_ = lean_array_fget(v_array_2541_, v_start_2542_);
v___x_2557_ = lean_unsigned_to_nat(1u);
v___x_2558_ = lean_nat_add(v_start_2542_, v___x_2557_);
lean_dec(v_start_2542_);
if (v_isShared_2551_ == 0)
{
lean_ctor_set(v___x_2550_, 1, v___x_2558_);
v___x_2560_ = v___x_2550_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_array_2541_);
lean_ctor_set(v_reuseFailAlloc_2696_, 1, v___x_2558_);
lean_ctor_set(v_reuseFailAlloc_2696_, 2, v_stop_2543_);
v___x_2560_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
lean_object* v_lower_2562_; lean_object* v_upper_2563_; lean_object* v___x_2693_; lean_object* v___x_2694_; uint8_t v___x_2695_; 
v___x_2693_ = lean_unsigned_to_nat(0u);
v___x_2694_ = lean_array_get_size(v_a_2554_);
v___x_2695_ = lean_nat_dec_le(v_numParams_2555_, v___x_2693_);
if (v___x_2695_ == 0)
{
lean_inc(v_numParams_2555_);
v_lower_2562_ = v_numParams_2555_;
v_upper_2563_ = v___x_2694_;
goto v___jp_2561_;
}
else
{
v_lower_2562_ = v___x_2693_;
v_upper_2563_ = v___x_2694_;
goto v___jp_2561_;
}
v___jp_2561_:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2564_ = l_Array_toSubarray___redArg(v_a_2554_, v_lower_2562_, v_upper_2563_);
lean_inc_ref(v___x_2564_);
v___x_2565_ = l_Subarray_copy___redArg(v___x_2564_);
v___x_2566_ = l_Lean_Elab_Deriving_mkImplicitBinders(v___x_2565_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v_a_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
lean_inc(v_a_2567_);
lean_dec_ref_known(v___x_2566_, 1);
v___x_2568_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2555_);
lean_inc_ref(v_argNames_2521_);
v___x_2569_ = l_Array_toSubarray___redArg(v_argNames_2521_, v___x_2568_, v_numParams_2555_);
v___x_2570_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__0));
v___x_2571_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__0___redArg(v___x_2569_, v___x_2570_);
v___x_2572_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__0___redArg(v___x_2564_, v___x_2570_);
v_a_2573_ = l_Array_append___redArg(v___x_2571_, v___x_2572_);
lean_dec_ref(v___x_2572_);
v___x_2574_ = lean_array_get_size(v_a_2573_);
v___x_2575_ = l_Array_toSubarray___redArg(v_a_2573_, v___x_2568_, v___x_2574_);
v___x_2576_ = l_Subarray_copy___redArg(v___x_2575_);
lean_inc(v_a_2552_);
v___x_2577_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v_a_2552_, v___x_2576_, v___y_2531_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v_a_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v_a_2578_ = lean_ctor_get(v___x_2577_, 0);
lean_inc(v_a_2578_);
lean_dec_ref_known(v___x_2577_, 1);
v___x_2579_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__2));
v___x_2580_ = l_Lean_Core_mkFreshUserName(v___x_2579_, v___y_2531_, v___y_2532_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_a_2581_; lean_object* v___x_2582_; 
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
lean_inc(v_a_2581_);
lean_dec_ref_known(v___x_2580_, 1);
lean_inc_ref(v_argNames_2521_);
lean_inc(v_a_2552_);
v___x_2582_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr(v_a_2552_, v_argNames_2521_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_object* v_a_2583_; lean_object* v_ref_2584_; lean_object* v_quotContext_2585_; lean_object* v_currMacroScope_2586_; uint8_t v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2656_; 
v_a_2583_ = lean_ctor_get(v___x_2582_, 0);
lean_inc(v_a_2583_);
lean_dec_ref_known(v___x_2582_, 1);
v_ref_2584_ = lean_ctor_get(v___y_2531_, 5);
v_quotContext_2585_ = lean_ctor_get(v___y_2531_, 10);
v_currMacroScope_2586_ = lean_ctor_get(v___y_2531_, 11);
v___x_2587_ = 0;
v___x_2588_ = l_Lean_SourceInfo_fromRef(v_ref_2584_, v___x_2587_);
v___x_2589_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__4));
v___x_2590_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__6));
v___x_2591_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__8));
v___x_2592_ = l_Lean_mkIdent(v_a_2581_);
lean_inc_n(v___x_2588_, 30);
v___x_2593_ = l_Lean_Syntax_node1(v___x_2588_, v___x_2591_, v___x_2592_);
v___x_2594_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_2595_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_2596_ = l_Array_append___redArg(v___x_2595_, v_a_2567_);
lean_dec(v_a_2567_);
v___x_2597_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2588_);
lean_ctor_set(v___x_2597_, 1, v___x_2594_);
lean_ctor_set(v___x_2597_, 2, v___x_2596_);
v___x_2598_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__10));
v___x_2599_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__11));
v___x_2600_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2588_);
lean_ctor_set(v___x_2600_, 1, v___x_2599_);
v___x_2601_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_2602_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__12);
v___x_2603_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__13));
lean_inc_n(v_currMacroScope_2586_, 3);
lean_inc_n(v_quotContext_2585_, 3);
v___x_2604_ = l_Lean_addMacroScope(v_quotContext_2585_, v___x_2603_, v_currMacroScope_2586_);
v___x_2605_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__26));
v___x_2606_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2588_);
lean_ctor_set(v___x_2606_, 1, v___x_2602_);
lean_ctor_set(v___x_2606_, 2, v___x_2604_);
lean_ctor_set(v___x_2606_, 3, v___x_2605_);
v___x_2607_ = l_Lean_Syntax_node1(v___x_2588_, v___x_2594_, v_a_2578_);
v___x_2608_ = l_Lean_Syntax_node2(v___x_2588_, v___x_2601_, v___x_2606_, v___x_2607_);
v___x_2609_ = l_Lean_Syntax_node2(v___x_2588_, v___x_2598_, v___x_2600_, v___x_2608_);
v___x_2610_ = l_Lean_Syntax_node1(v___x_2588_, v___x_2594_, v___x_2609_);
v___x_2611_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__27));
v___x_2612_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2588_);
lean_ctor_set(v___x_2612_, 1, v___x_2611_);
v___x_2613_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__29));
v___x_2614_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__30));
v___x_2615_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2588_);
lean_ctor_set(v___x_2615_, 1, v___x_2614_);
v___x_2616_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2588_);
lean_ctor_set(v___x_2616_, 1, v___x_2594_);
lean_ctor_set(v___x_2616_, 2, v___x_2595_);
v___x_2617_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__32));
v___x_2618_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__34));
v___x_2619_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__36));
v___x_2620_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1);
v___x_2621_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__2));
v___x_2622_ = l_Lean_addMacroScope(v_quotContext_2585_, v___x_2621_, v_currMacroScope_2586_);
v___x_2623_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__6));
v___x_2624_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2588_);
lean_ctor_set(v___x_2624_, 1, v___x_2620_);
lean_ctor_set(v___x_2624_, 2, v___x_2622_);
lean_ctor_set(v___x_2624_, 3, v___x_2623_);
lean_inc_ref_n(v___x_2616_, 10);
v___x_2625_ = l_Lean_Syntax_node2(v___x_2588_, v___x_2619_, v___x_2624_, v___x_2616_);
v___x_2626_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__38));
v___x_2627_ = l_Lean_mkIdent(v___x_2556_);
v___x_2628_ = l_Array_append___redArg(v___x_2595_, v_levelInsts_2522_);
v___x_2629_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2588_);
lean_ctor_set(v___x_2629_, 1, v___x_2594_);
lean_ctor_set(v___x_2629_, 2, v___x_2628_);
v___x_2630_ = l_Lean_Syntax_node2(v___x_2588_, v___x_2601_, v___x_2627_, v___x_2629_);
lean_inc_ref_n(v___x_2612_, 2);
v___x_2631_ = l_Lean_Syntax_node3(v___x_2588_, v___x_2626_, v___x_2612_, v___x_2616_, v___x_2630_);
v___x_2632_ = l_Lean_Syntax_node3(v___x_2588_, v___x_2594_, v___x_2616_, v___x_2616_, v___x_2631_);
v___x_2633_ = l_Lean_Syntax_node2(v___x_2588_, v___x_2618_, v___x_2625_, v___x_2632_);
v___x_2634_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__9));
v___x_2635_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2588_);
lean_ctor_set(v___x_2635_, 1, v___x_2634_);
v___x_2636_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8);
v___x_2637_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__9));
v___x_2638_ = l_Lean_addMacroScope(v_quotContext_2585_, v___x_2637_, v_currMacroScope_2586_);
v___x_2639_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__12));
v___x_2640_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2588_);
lean_ctor_set(v___x_2640_, 1, v___x_2636_);
lean_ctor_set(v___x_2640_, 2, v___x_2638_);
lean_ctor_set(v___x_2640_, 3, v___x_2639_);
v___x_2641_ = l_Lean_Syntax_node2(v___x_2588_, v___x_2619_, v___x_2640_, v___x_2616_);
v___x_2642_ = l_Lean_Syntax_node3(v___x_2588_, v___x_2626_, v___x_2612_, v___x_2616_, v_a_2583_);
v___x_2643_ = l_Lean_Syntax_node3(v___x_2588_, v___x_2594_, v___x_2616_, v___x_2616_, v___x_2642_);
v___x_2644_ = l_Lean_Syntax_node2(v___x_2588_, v___x_2618_, v___x_2641_, v___x_2643_);
v___x_2645_ = l_Lean_Syntax_node3(v___x_2588_, v___x_2594_, v___x_2633_, v___x_2635_, v___x_2644_);
v___x_2646_ = l_Lean_Syntax_node1(v___x_2588_, v___x_2617_, v___x_2645_);
v___x_2647_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__40));
v___x_2648_ = l_Lean_Syntax_node1(v___x_2588_, v___x_2647_, v___x_2616_);
v___x_2649_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__10));
v___x_2650_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2650_, 0, v___x_2588_);
lean_ctor_set(v___x_2650_, 1, v___x_2649_);
v___x_2651_ = l_Lean_Syntax_node6(v___x_2588_, v___x_2613_, v___x_2615_, v___x_2616_, v___x_2646_, v___x_2648_, v___x_2616_, v___x_2650_);
v___x_2652_ = l_Lean_Syntax_node5(v___x_2588_, v___x_2590_, v___x_2593_, v___x_2597_, v___x_2610_, v___x_2612_, v___x_2651_);
v___x_2653_ = l_Lean_Syntax_node1(v___x_2588_, v___x_2589_, v___x_2652_);
v___x_2654_ = lean_array_push(v_fst_2537_, v___x_2653_);
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 1, v___x_2560_);
lean_ctor_set(v___x_2539_, 0, v___x_2654_);
v___x_2656_ = v___x_2539_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v___x_2654_);
lean_ctor_set(v_reuseFailAlloc_2660_, 1, v___x_2560_);
v___x_2656_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
size_t v___x_2657_; size_t v___x_2658_; 
v___x_2657_ = ((size_t)1ULL);
v___x_2658_ = lean_usize_add(v_i_2525_, v___x_2657_);
v_i_2525_ = v___x_2658_;
v_b_2526_ = v___x_2656_;
goto _start;
}
}
else
{
lean_object* v_a_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2668_; 
lean_dec(v_a_2581_);
lean_dec(v_a_2578_);
lean_dec(v_a_2567_);
lean_dec_ref(v___x_2560_);
lean_dec(v___x_2556_);
lean_del_object(v___x_2539_);
lean_dec(v_fst_2537_);
lean_dec_ref(v_argNames_2521_);
v_a_2661_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2663_ = v___x_2582_;
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_a_2661_);
lean_dec(v___x_2582_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2666_; 
if (v_isShared_2664_ == 0)
{
v___x_2666_ = v___x_2663_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2661_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
}
else
{
lean_object* v_a_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2676_; 
lean_dec(v_a_2578_);
lean_dec(v_a_2567_);
lean_dec_ref(v___x_2560_);
lean_dec(v___x_2556_);
lean_del_object(v___x_2539_);
lean_dec(v_fst_2537_);
lean_dec_ref(v_argNames_2521_);
v_a_2669_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2671_ = v___x_2580_;
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_a_2669_);
lean_dec(v___x_2580_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2674_; 
if (v_isShared_2672_ == 0)
{
v___x_2674_ = v___x_2671_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_a_2669_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
}
else
{
lean_object* v_a_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2684_; 
lean_dec(v_a_2567_);
lean_dec_ref(v___x_2560_);
lean_dec(v___x_2556_);
lean_del_object(v___x_2539_);
lean_dec(v_fst_2537_);
lean_dec_ref(v_argNames_2521_);
v_a_2677_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2679_ = v___x_2577_;
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_a_2677_);
lean_dec(v___x_2577_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v___x_2682_; 
if (v_isShared_2680_ == 0)
{
v___x_2682_ = v___x_2679_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_a_2677_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
}
}
else
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2692_; 
lean_dec_ref(v___x_2564_);
lean_dec_ref(v___x_2560_);
lean_dec(v___x_2556_);
lean_del_object(v___x_2539_);
lean_dec(v_fst_2537_);
lean_dec_ref(v_argNames_2521_);
v_a_2685_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2687_ = v___x_2566_;
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2566_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2690_; 
if (v_isShared_2688_ == 0)
{
v___x_2690_ = v___x_2687_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_a_2685_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
}
}
}
}
else
{
lean_object* v_a_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2704_; 
lean_del_object(v___x_2550_);
lean_dec(v_stop_2543_);
lean_dec(v_start_2542_);
lean_dec_ref(v_array_2541_);
lean_del_object(v___x_2539_);
lean_dec(v_fst_2537_);
lean_dec_ref(v_argNames_2521_);
v_a_2697_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2699_ = v___x_2553_;
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_a_2697_);
lean_dec(v___x_2553_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___x_2702_; 
if (v_isShared_2700_ == 0)
{
v___x_2702_ = v___x_2699_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_a_2697_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___boxed(lean_object* v_argNames_2710_, lean_object* v_levelInsts_2711_, lean_object* v_as_2712_, lean_object* v_sz_2713_, lean_object* v_i_2714_, lean_object* v_b_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
size_t v_sz_boxed_2723_; size_t v_i_boxed_2724_; lean_object* v_res_2725_; 
v_sz_boxed_2723_ = lean_unbox_usize(v_sz_2713_);
lean_dec(v_sz_2713_);
v_i_boxed_2724_ = lean_unbox_usize(v_i_2714_);
lean_dec(v_i_2714_);
v_res_2725_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1(v_argNames_2710_, v_levelInsts_2711_, v_as_2712_, v_sz_boxed_2723_, v_i_boxed_2724_, v_b_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
lean_dec_ref(v_as_2712_);
lean_dec_ref(v_levelInsts_2711_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls(lean_object* v_ctx_2726_, lean_object* v_argNames_2727_, lean_object* v_levelInsts_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_){
_start:
{
lean_object* v_typeInfos_2736_; lean_object* v_auxFunNames_2737_; lean_object* v___x_2738_; lean_object* v_letDecls_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; size_t v_sz_2743_; size_t v___x_2744_; lean_object* v___x_2745_; 
v_typeInfos_2736_ = lean_ctor_get(v_ctx_2726_, 1);
lean_inc_ref(v_typeInfos_2736_);
v_auxFunNames_2737_ = lean_ctor_get(v_ctx_2726_, 2);
lean_inc_ref(v_auxFunNames_2737_);
lean_dec_ref(v_ctx_2726_);
v___x_2738_ = lean_unsigned_to_nat(0u);
v_letDecls_2739_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__0));
v___x_2740_ = lean_array_get_size(v_auxFunNames_2737_);
v___x_2741_ = l_Array_toSubarray___redArg(v_auxFunNames_2737_, v___x_2738_, v___x_2740_);
v___x_2742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2742_, 0, v_letDecls_2739_);
lean_ctor_set(v___x_2742_, 1, v___x_2741_);
v_sz_2743_ = lean_array_size(v_typeInfos_2736_);
v___x_2744_ = ((size_t)0ULL);
v___x_2745_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1(v_argNames_2727_, v_levelInsts_2728_, v_typeInfos_2736_, v_sz_2743_, v___x_2744_, v___x_2742_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_);
lean_dec_ref(v_typeInfos_2736_);
if (lean_obj_tag(v___x_2745_) == 0)
{
lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2754_; 
v_a_2746_ = lean_ctor_get(v___x_2745_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2745_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2748_ = v___x_2745_;
v_isShared_2749_ = v_isSharedCheck_2754_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v___x_2745_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2754_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v_fst_2750_; lean_object* v___x_2752_; 
v_fst_2750_ = lean_ctor_get(v_a_2746_, 0);
lean_inc(v_fst_2750_);
lean_dec(v_a_2746_);
if (v_isShared_2749_ == 0)
{
lean_ctor_set(v___x_2748_, 0, v_fst_2750_);
v___x_2752_ = v___x_2748_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_fst_2750_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
else
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
v_a_2755_ = lean_ctor_get(v___x_2745_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2745_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___x_2745_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2745_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2755_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls___boxed(lean_object* v_ctx_2763_, lean_object* v_argNames_2764_, lean_object* v_levelInsts_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls(v_ctx_2763_, v_argNames_2764_, v_levelInsts_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_);
lean_dec(v_a_2771_);
lean_dec_ref(v_a_2770_);
lean_dec(v_a_2769_);
lean_dec_ref(v_a_2768_);
lean_dec(v_a_2767_);
lean_dec_ref(v_a_2766_);
lean_dec_ref(v_levelInsts_2765_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__0(lean_object* v_inst_2774_, lean_object* v_R_2775_, lean_object* v_a_2776_, lean_object* v_b_2777_){
_start:
{
lean_object* v___x_2778_; 
v___x_2778_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__0___redArg(v_a_2776_, v_b_2777_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__2(size_t v_sz_2779_, size_t v_i_2780_, lean_object* v_bs_2781_){
_start:
{
uint8_t v___x_2782_; 
v___x_2782_ = lean_usize_dec_lt(v_i_2780_, v_sz_2779_);
if (v___x_2782_ == 0)
{
return v_bs_2781_;
}
else
{
lean_object* v_v_2783_; lean_object* v___x_2784_; lean_object* v_bs_x27_2785_; size_t v___x_2786_; size_t v___x_2787_; lean_object* v___x_2788_; 
v_v_2783_ = lean_array_uget(v_bs_2781_, v_i_2780_);
v___x_2784_ = lean_unsigned_to_nat(0u);
v_bs_x27_2785_ = lean_array_uset(v_bs_2781_, v_i_2780_, v___x_2784_);
v___x_2786_ = ((size_t)1ULL);
v___x_2787_ = lean_usize_add(v_i_2780_, v___x_2786_);
v___x_2788_ = lean_array_uset(v_bs_x27_2785_, v_i_2780_, v_v_2783_);
v_i_2780_ = v___x_2787_;
v_bs_2781_ = v___x_2788_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__2___boxed(lean_object* v_sz_2790_, lean_object* v_i_2791_, lean_object* v_bs_2792_){
_start:
{
size_t v_sz_boxed_2793_; size_t v_i_boxed_2794_; lean_object* v_res_2795_; 
v_sz_boxed_2793_ = lean_unbox_usize(v_sz_2790_);
lean_dec(v_sz_2790_);
v_i_boxed_2794_ = lean_unbox_usize(v_i_2791_);
lean_dec(v_i_2791_);
v_res_2795_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__2(v_sz_boxed_2793_, v_i_boxed_2794_, v_bs_2792_);
return v_res_2795_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2806_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__4));
v___x_2807_ = l_String_toRawSubstring_x27(v___x_2806_);
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg(size_t v_sz_2828_, size_t v_i_2829_, lean_object* v_bs_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
uint8_t v___x_2834_; 
v___x_2834_ = lean_usize_dec_lt(v_i_2829_, v_sz_2828_);
if (v___x_2834_ == 0)
{
lean_object* v___x_2835_; 
v___x_2835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2835_, 0, v_bs_2830_);
return v___x_2835_;
}
else
{
lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2836_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__1));
v___x_2837_ = l_Lean_Core_mkFreshUserName(v___x_2836_, v___y_2831_, v___y_2832_);
if (lean_obj_tag(v___x_2837_) == 0)
{
lean_object* v_a_2838_; lean_object* v_ref_2839_; lean_object* v_quotContext_2840_; lean_object* v_currMacroScope_2841_; lean_object* v_v_2842_; lean_object* v___x_2843_; lean_object* v_bs_x27_2844_; lean_object* v___x_2845_; uint8_t v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; size_t v___x_2875_; size_t v___x_2876_; lean_object* v___x_2877_; 
v_a_2838_ = lean_ctor_get(v___x_2837_, 0);
lean_inc(v_a_2838_);
lean_dec_ref_known(v___x_2837_, 1);
v_ref_2839_ = lean_ctor_get(v___y_2831_, 5);
v_quotContext_2840_ = lean_ctor_get(v___y_2831_, 10);
v_currMacroScope_2841_ = lean_ctor_get(v___y_2831_, 11);
v_v_2842_ = lean_array_uget(v_bs_2830_, v_i_2829_);
v___x_2843_ = lean_unsigned_to_nat(0u);
v_bs_x27_2844_ = lean_array_uset(v_bs_2830_, v_i_2829_, v___x_2843_);
v___x_2845_ = l_Lean_mkIdent(v_a_2838_);
v___x_2846_ = 0;
v___x_2847_ = l_Lean_SourceInfo_fromRef(v_ref_2839_, v___x_2846_);
v___x_2848_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__3));
v___x_2849_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__4));
lean_inc_n(v___x_2847_, 11);
v___x_2850_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2847_);
lean_ctor_set(v___x_2850_, 1, v___x_2849_);
v___x_2851_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
lean_inc(v___x_2845_);
v___x_2852_ = l_Lean_Syntax_node1(v___x_2847_, v___x_2851_, v___x_2845_);
v___x_2853_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__11));
v___x_2854_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2847_);
lean_ctor_set(v___x_2854_, 1, v___x_2853_);
v___x_2855_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__6));
v___x_2856_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__5);
v___x_2857_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__6));
lean_inc(v_currMacroScope_2841_);
lean_inc(v_quotContext_2840_);
v___x_2858_ = l_Lean_addMacroScope(v_quotContext_2840_, v___x_2857_, v_currMacroScope_2841_);
v___x_2859_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__12));
v___x_2860_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2847_);
lean_ctor_set(v___x_2860_, 1, v___x_2856_);
lean_ctor_set(v___x_2860_, 2, v___x_2858_);
lean_ctor_set(v___x_2860_, 3, v___x_2859_);
v___x_2861_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__7));
v___x_2862_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2847_);
lean_ctor_set(v___x_2862_, 1, v___x_2861_);
v___x_2863_ = l_Lean_mkIdent(v_v_2842_);
v___x_2864_ = l_Lean_Syntax_node1(v___x_2847_, v___x_2851_, v___x_2863_);
v___x_2865_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__10));
v___x_2866_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2847_);
lean_ctor_set(v___x_2866_, 1, v___x_2865_);
v___x_2867_ = l_Lean_Syntax_node4(v___x_2847_, v___x_2855_, v___x_2860_, v___x_2862_, v___x_2864_, v___x_2866_);
v___x_2868_ = l_Lean_Syntax_node2(v___x_2847_, v___x_2851_, v___x_2854_, v___x_2867_);
v___x_2869_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_2870_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2847_);
lean_ctor_set(v___x_2870_, 1, v___x_2851_);
lean_ctor_set(v___x_2870_, 2, v___x_2869_);
v___x_2871_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__13));
v___x_2872_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2847_);
lean_ctor_set(v___x_2872_, 1, v___x_2871_);
v___x_2873_ = l_Lean_Syntax_node5(v___x_2847_, v___x_2848_, v___x_2850_, v___x_2852_, v___x_2868_, v___x_2870_, v___x_2872_);
v___x_2874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2874_, 0, v___x_2845_);
lean_ctor_set(v___x_2874_, 1, v___x_2873_);
v___x_2875_ = ((size_t)1ULL);
v___x_2876_ = lean_usize_add(v_i_2829_, v___x_2875_);
v___x_2877_ = lean_array_uset(v_bs_x27_2844_, v_i_2829_, v___x_2874_);
v_i_2829_ = v___x_2876_;
v_bs_2830_ = v___x_2877_;
goto _start;
}
else
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2886_; 
lean_dec_ref(v_bs_2830_);
v_a_2879_ = lean_ctor_get(v___x_2837_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2881_ = v___x_2837_;
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2837_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2884_; 
if (v_isShared_2882_ == 0)
{
v___x_2884_ = v___x_2881_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2879_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___boxed(lean_object* v_sz_2887_, lean_object* v_i_2888_, lean_object* v_bs_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_){
_start:
{
size_t v_sz_boxed_2893_; size_t v_i_boxed_2894_; lean_object* v_res_2895_; 
v_sz_boxed_2893_ = lean_unbox_usize(v_sz_2887_);
lean_dec(v_sz_2887_);
v_i_boxed_2894_ = lean_unbox_usize(v_i_2888_);
lean_dec(v_i_2888_);
v_res_2895_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg(v_sz_boxed_2893_, v_i_boxed_2894_, v_bs_2889_, v___y_2890_, v___y_2891_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__1(size_t v_sz_2896_, size_t v_i_2897_, lean_object* v_bs_2898_){
_start:
{
uint8_t v___x_2899_; 
v___x_2899_ = lean_usize_dec_lt(v_i_2897_, v_sz_2896_);
if (v___x_2899_ == 0)
{
return v_bs_2898_;
}
else
{
lean_object* v_v_2900_; lean_object* v___x_2901_; lean_object* v_bs_x27_2902_; size_t v___x_2903_; size_t v___x_2904_; lean_object* v___x_2905_; 
v_v_2900_ = lean_array_uget(v_bs_2898_, v_i_2897_);
v___x_2901_ = lean_unsigned_to_nat(0u);
v_bs_x27_2902_ = lean_array_uset(v_bs_2898_, v_i_2897_, v___x_2901_);
v___x_2903_ = ((size_t)1ULL);
v___x_2904_ = lean_usize_add(v_i_2897_, v___x_2903_);
v___x_2905_ = lean_array_uset(v_bs_x27_2902_, v_i_2897_, v_v_2900_);
v_i_2897_ = v___x_2904_;
v_bs_2898_ = v___x_2905_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__1___boxed(lean_object* v_sz_2907_, lean_object* v_i_2908_, lean_object* v_bs_2909_){
_start:
{
size_t v_sz_boxed_2910_; size_t v_i_boxed_2911_; lean_object* v_res_2912_; 
v_sz_boxed_2910_ = lean_unbox_usize(v_sz_2907_);
lean_dec(v_sz_2907_);
v_i_boxed_2911_ = lean_unbox_usize(v_i_2908_);
lean_dec(v_i_2908_);
v_res_2912_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__1(v_sz_boxed_2910_, v_i_boxed_2911_, v_bs_2909_);
return v_res_2912_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__7(void){
_start:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2920_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__7));
v___x_2921_ = l_String_toRawSubstring_x27(v___x_2920_);
return v___x_2921_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20(void){
_start:
{
lean_object* v___x_2946_; lean_object* v___x_2947_; 
v___x_2946_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__19));
v___x_2947_ = l_Lean_stringToMessageData(v___x_2946_);
return v___x_2947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction(lean_object* v_ctx_2948_, lean_object* v_i_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_){
_start:
{
lean_object* v_typeInfos_2957_; lean_object* v_auxFunNames_2958_; uint8_t v_usePartial_2959_; lean_object* v___x_2960_; lean_object* v_indVal_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
v_typeInfos_2957_ = lean_ctor_get(v_ctx_2948_, 1);
v_auxFunNames_2958_ = lean_ctor_get(v_ctx_2948_, 2);
v_usePartial_2959_ = lean_ctor_get_uint8(v_ctx_2948_, sizeof(void*)*3);
v___x_2960_ = l_Lean_instInhabitedInductiveVal_default;
v_indVal_2961_ = lean_array_get(v___x_2960_, v_typeInfos_2957_, v_i_2949_);
v___x_2962_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0));
v___x_2963_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__14));
v___x_2964_ = lean_unsigned_to_nat(1u);
lean_inc(v_indVal_2961_);
v___x_2965_ = l_Lean_Elab_Deriving_mkHeader(v___x_2963_, v___x_2964_, v_indVal_2961_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v_toConstantVal_2966_; lean_object* v_a_2967_; lean_object* v_levelParams_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_3207_; 
v_toConstantVal_2966_ = lean_ctor_get(v_indVal_2961_, 0);
lean_inc_ref(v_toConstantVal_2966_);
v_a_2967_ = lean_ctor_get(v___x_2965_, 0);
lean_inc(v_a_2967_);
lean_dec_ref_known(v___x_2965_, 1);
v_levelParams_2968_ = lean_ctor_get(v_toConstantVal_2966_, 1);
v_isSharedCheck_3207_ = !lean_is_exclusive(v_toConstantVal_2966_);
if (v_isSharedCheck_3207_ == 0)
{
lean_object* v_unused_3208_; lean_object* v_unused_3209_; 
v_unused_3208_ = lean_ctor_get(v_toConstantVal_2966_, 2);
lean_dec(v_unused_3208_);
v_unused_3209_ = lean_ctor_get(v_toConstantVal_2966_, 0);
lean_dec(v_unused_3209_);
v___x_2970_ = v_toConstantVal_2966_;
v_isShared_2971_ = v_isSharedCheck_3207_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_levelParams_2968_);
lean_dec(v_toConstantVal_2966_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_3207_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2972_; size_t v_sz_2973_; size_t v___x_2974_; lean_object* v___x_2975_; 
v___x_2972_ = lean_array_mk(v_levelParams_2968_);
v_sz_2973_ = lean_array_size(v___x_2972_);
v___x_2974_ = ((size_t)0ULL);
v___x_2975_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg(v_sz_2973_, v___x_2974_, v___x_2972_, v_a_2954_, v_a_2955_);
if (lean_obj_tag(v___x_2975_) == 0)
{
lean_object* v_a_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_3198_; 
v_a_2976_ = lean_ctor_get(v___x_2975_, 0);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_2978_ = v___x_2975_;
v_isShared_2979_ = v_isSharedCheck_3198_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_a_2976_);
lean_dec(v___x_2975_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_3198_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2980_; lean_object* v_fst_2981_; lean_object* v_snd_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_3197_; 
v___x_2980_ = l_Array_unzip___redArg(v_a_2976_);
lean_dec(v_a_2976_);
v_fst_2981_ = lean_ctor_get(v___x_2980_, 0);
v_snd_2982_ = lean_ctor_get(v___x_2980_, 1);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_2984_ = v___x_2980_;
v_isShared_2985_ = v_isSharedCheck_3197_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_snd_2982_);
lean_inc(v_fst_2981_);
lean_dec(v___x_2980_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_3197_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2986_; lean_object* v_auxFunName_2987_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v_a_2994_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v_body_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; size_t v_sz_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_2986_ = lean_box(0);
v_auxFunName_2987_ = lean_array_get(v___x_2986_, v_auxFunNames_2958_, v_i_2949_);
v_sz_3179_ = lean_array_size(v_fst_2981_);
v___x_3180_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__2(v_sz_3179_, v___x_2974_, v_fst_2981_);
lean_inc_ref(v___x_3180_);
lean_inc(v_auxFunName_2987_);
lean_inc(v_indVal_2961_);
lean_inc(v_a_2967_);
v___x_3181_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody(v_a_2967_, v_indVal_2961_, v_auxFunName_2987_, v___x_3180_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_);
if (lean_obj_tag(v___x_3181_) == 0)
{
if (v_usePartial_2959_ == 0)
{
lean_object* v_a_3182_; 
lean_dec_ref(v___x_3180_);
lean_dec_ref(v_ctx_2948_);
v_a_3182_ = lean_ctor_get(v___x_3181_, 0);
lean_inc(v_a_3182_);
lean_dec_ref_known(v___x_3181_, 1);
v_body_3127_ = v_a_3182_;
v___y_3128_ = v_a_2950_;
v___y_3129_ = v_a_2951_;
v___y_3130_ = v_a_2952_;
v___y_3131_ = v_a_2953_;
v___y_3132_ = v_a_2954_;
v___y_3133_ = v_a_2955_;
goto v___jp_3126_;
}
else
{
lean_object* v_a_3183_; lean_object* v_argNames_3184_; lean_object* v___x_3185_; 
v_a_3183_ = lean_ctor_get(v___x_3181_, 0);
lean_inc(v_a_3183_);
lean_dec_ref_known(v___x_3181_, 1);
v_argNames_3184_ = lean_ctor_get(v_a_2967_, 1);
lean_inc_ref(v_argNames_3184_);
v___x_3185_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls(v_ctx_2948_, v_argNames_3184_, v___x_3180_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_);
lean_dec_ref(v___x_3180_);
if (lean_obj_tag(v___x_3185_) == 0)
{
lean_object* v_a_3186_; lean_object* v___x_3187_; 
v_a_3186_ = lean_ctor_get(v___x_3185_, 0);
lean_inc(v_a_3186_);
lean_dec_ref_known(v___x_3185_, 1);
v___x_3187_ = l_Lean_Elab_Deriving_mkLet(v_a_3186_, v_a_3183_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_);
lean_dec(v_a_3186_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_object* v_a_3188_; 
v_a_3188_ = lean_ctor_get(v___x_3187_, 0);
lean_inc(v_a_3188_);
lean_dec_ref_known(v___x_3187_, 1);
v_body_3127_ = v_a_3188_;
v___y_3128_ = v_a_2950_;
v___y_3129_ = v_a_2951_;
v___y_3130_ = v_a_2952_;
v___y_3131_ = v_a_2953_;
v___y_3132_ = v_a_2954_;
v___y_3133_ = v_a_2955_;
goto v___jp_3126_;
}
else
{
lean_dec(v_auxFunName_2987_);
lean_del_object(v___x_2984_);
lean_dec(v_snd_2982_);
lean_del_object(v___x_2978_);
lean_del_object(v___x_2970_);
lean_dec(v_a_2967_);
lean_dec(v_indVal_2961_);
return v___x_3187_;
}
}
else
{
lean_object* v_a_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3196_; 
lean_dec(v_a_3183_);
lean_dec(v_auxFunName_2987_);
lean_del_object(v___x_2984_);
lean_dec(v_snd_2982_);
lean_del_object(v___x_2978_);
lean_del_object(v___x_2970_);
lean_dec(v_a_2967_);
lean_dec(v_indVal_2961_);
v_a_3189_ = lean_ctor_get(v___x_3185_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3185_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3191_ = v___x_3185_;
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_a_3189_);
lean_dec(v___x_3185_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3194_; 
if (v_isShared_3192_ == 0)
{
v___x_3194_ = v___x_3191_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_a_3189_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3180_);
lean_dec(v_auxFunName_2987_);
lean_del_object(v___x_2984_);
lean_dec(v_snd_2982_);
lean_del_object(v___x_2978_);
lean_del_object(v___x_2970_);
lean_dec(v_a_2967_);
lean_dec(v_indVal_2961_);
lean_dec_ref(v_ctx_2948_);
return v___x_3181_;
}
v___jp_2988_:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; size_t v_sz_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_2995_ = lean_array_pop(v___y_2992_);
v___x_2996_ = l_Array_append___redArg(v___x_2995_, v_snd_2982_);
lean_dec(v_snd_2982_);
v___x_2997_ = lean_mk_empty_array_with_capacity(v___x_2964_);
v___x_2998_ = lean_array_push(v___x_2997_, v_a_2994_);
v_sz_2999_ = lean_array_size(v___x_2998_);
v___x_3000_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__1(v_sz_2999_, v___x_2974_, v___x_2998_);
v___x_3001_ = l_Array_append___redArg(v___x_2996_, v___x_3000_);
lean_dec_ref(v___x_3000_);
if (v_usePartial_2959_ == 0)
{
lean_object* v_ref_3002_; lean_object* v_quotContext_3003_; lean_object* v_currMacroScope_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3014_; 
v_ref_3002_ = lean_ctor_get(v___y_2993_, 5);
v_quotContext_3003_ = lean_ctor_get(v___y_2993_, 10);
v_currMacroScope_3004_ = lean_ctor_get(v___y_2993_, 11);
v___x_3005_ = l_Lean_SourceInfo_fromRef(v_ref_3002_, v_usePartial_2959_);
v___x_3006_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__0));
v___x_3007_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__1));
lean_inc_ref_n(v___y_2989_, 2);
v___x_3008_ = l_Lean_Name_mkStr4(v___x_2962_, v___y_2989_, v___x_3006_, v___x_3007_);
v___x_3009_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__2));
v___x_3010_ = l_Lean_Name_mkStr4(v___x_2962_, v___y_2989_, v___x_3006_, v___x_3009_);
v___x_3011_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_3012_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
lean_inc(v___x_3005_);
if (v_isShared_2971_ == 0)
{
lean_ctor_set_tag(v___x_2970_, 1);
lean_ctor_set(v___x_2970_, 2, v___x_3012_);
lean_ctor_set(v___x_2970_, 1, v___x_3011_);
lean_ctor_set(v___x_2970_, 0, v___x_3005_);
v___x_3014_ = v___x_2970_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v___x_3005_);
lean_ctor_set(v_reuseFailAlloc_3056_, 1, v___x_3011_);
lean_ctor_set(v_reuseFailAlloc_3056_, 2, v___x_3012_);
v___x_3014_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3020_; 
lean_inc_ref_n(v___x_3014_, 7);
lean_inc_n(v___x_3005_, 2);
v___x_3015_ = l_Lean_Syntax_node7(v___x_3005_, v___x_3010_, v___x_3014_, v___x_3014_, v___x_3014_, v___x_3014_, v___x_3014_, v___x_3014_, v___x_3014_);
v___x_3016_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__3));
lean_inc_ref(v___y_2989_);
v___x_3017_ = l_Lean_Name_mkStr4(v___x_2962_, v___y_2989_, v___x_3006_, v___x_3016_);
v___x_3018_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__4));
if (v_isShared_2985_ == 0)
{
lean_ctor_set_tag(v___x_2984_, 2);
lean_ctor_set(v___x_2984_, 1, v___x_3018_);
lean_ctor_set(v___x_2984_, 0, v___x_3005_);
v___x_3020_ = v___x_2984_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v___x_3005_);
lean_ctor_set(v_reuseFailAlloc_3055_, 1, v___x_3018_);
v___x_3020_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3053_; 
v___x_3021_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__5));
lean_inc_ref_n(v___y_2989_, 5);
v___x_3022_ = l_Lean_Name_mkStr4(v___x_2962_, v___y_2989_, v___x_3006_, v___x_3021_);
v___x_3023_ = l_Lean_mkIdent(v_auxFunName_2987_);
lean_inc_ref_n(v___x_3014_, 4);
lean_inc_n(v___x_3005_, 11);
v___x_3024_ = l_Lean_Syntax_node2(v___x_3005_, v___x_3022_, v___x_3023_, v___x_3014_);
v___x_3025_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__6));
v___x_3026_ = l_Lean_Name_mkStr4(v___x_2962_, v___y_2989_, v___x_3006_, v___x_3025_);
v___x_3027_ = l_Array_append___redArg(v___x_3012_, v___x_3001_);
lean_dec_ref(v___x_3001_);
v___x_3028_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3028_, 0, v___x_3005_);
lean_ctor_set(v___x_3028_, 1, v___x_3011_);
lean_ctor_set(v___x_3028_, 2, v___x_3027_);
v___x_3029_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__9));
lean_inc_ref(v___y_2991_);
v___x_3030_ = l_Lean_Name_mkStr4(v___x_2962_, v___y_2989_, v___y_2991_, v___x_3029_);
v___x_3031_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__11));
v___x_3032_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3005_);
lean_ctor_set(v___x_3032_, 1, v___x_3031_);
v___x_3033_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__7, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__7_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__7);
v___x_3034_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__8));
lean_inc(v_currMacroScope_3004_);
lean_inc(v_quotContext_3003_);
v___x_3035_ = l_Lean_addMacroScope(v_quotContext_3003_, v___x_3034_, v_currMacroScope_3004_);
v___x_3036_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__14));
v___x_3037_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3005_);
lean_ctor_set(v___x_3037_, 1, v___x_3033_);
lean_ctor_set(v___x_3037_, 2, v___x_3035_);
lean_ctor_set(v___x_3037_, 3, v___x_3036_);
v___x_3038_ = l_Lean_Syntax_node2(v___x_3005_, v___x_3030_, v___x_3032_, v___x_3037_);
v___x_3039_ = l_Lean_Syntax_node1(v___x_3005_, v___x_3011_, v___x_3038_);
v___x_3040_ = l_Lean_Syntax_node2(v___x_3005_, v___x_3026_, v___x_3028_, v___x_3039_);
v___x_3041_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__15));
v___x_3042_ = l_Lean_Name_mkStr4(v___x_2962_, v___y_2989_, v___x_3006_, v___x_3041_);
v___x_3043_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__27));
v___x_3044_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3005_);
lean_ctor_set(v___x_3044_, 1, v___x_3043_);
v___x_3045_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__16));
v___x_3046_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__17));
v___x_3047_ = l_Lean_Name_mkStr4(v___x_2962_, v___y_2989_, v___x_3045_, v___x_3046_);
v___x_3048_ = l_Lean_Syntax_node2(v___x_3005_, v___x_3047_, v___x_3014_, v___x_3014_);
v___x_3049_ = l_Lean_Syntax_node4(v___x_3005_, v___x_3042_, v___x_3044_, v___y_2990_, v___x_3048_, v___x_3014_);
v___x_3050_ = l_Lean_Syntax_node5(v___x_3005_, v___x_3017_, v___x_3020_, v___x_3024_, v___x_3040_, v___x_3049_, v___x_3014_);
v___x_3051_ = l_Lean_Syntax_node2(v___x_3005_, v___x_3008_, v___x_3015_, v___x_3050_);
if (v_isShared_2979_ == 0)
{
lean_ctor_set(v___x_2978_, 0, v___x_3051_);
v___x_3053_ = v___x_2978_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v___x_3051_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
return v___x_3053_;
}
}
}
}
else
{
lean_object* v_ref_3057_; lean_object* v_quotContext_3058_; lean_object* v_currMacroScope_3059_; uint8_t v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3070_; 
v_ref_3057_ = lean_ctor_get(v___y_2993_, 5);
v_quotContext_3058_ = lean_ctor_get(v___y_2993_, 10);
v_currMacroScope_3059_ = lean_ctor_get(v___y_2993_, 11);
v___x_3060_ = 0;
v___x_3061_ = l_Lean_SourceInfo_fromRef(v_ref_3057_, v___x_3060_);
v___x_3062_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__0));
v___x_3063_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__1));
lean_inc_ref_n(v___y_2989_, 2);
v___x_3064_ = l_Lean_Name_mkStr4(v___x_2962_, v___y_2989_, v___x_3062_, v___x_3063_);
v___x_3065_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__2));
v___x_3066_ = l_Lean_Name_mkStr4(v___x_2962_, v___y_2989_, v___x_3062_, v___x_3065_);
v___x_3067_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_3068_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
lean_inc(v___x_3061_);
if (v_isShared_2971_ == 0)
{
lean_ctor_set_tag(v___x_2970_, 1);
lean_ctor_set(v___x_2970_, 2, v___x_3068_);
lean_ctor_set(v___x_2970_, 1, v___x_3067_);
lean_ctor_set(v___x_2970_, 0, v___x_3061_);
v___x_3070_ = v___x_2970_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v___x_3061_);
lean_ctor_set(v_reuseFailAlloc_3117_, 1, v___x_3067_);
lean_ctor_set(v_reuseFailAlloc_3117_, 2, v___x_3068_);
v___x_3070_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3074_; 
v___x_3071_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__18));
lean_inc_ref(v___y_2989_);
v___x_3072_ = l_Lean_Name_mkStr4(v___x_2962_, v___y_2989_, v___x_3062_, v___x_3071_);
lean_inc(v___x_3061_);
if (v_isShared_2985_ == 0)
{
lean_ctor_set_tag(v___x_2984_, 2);
lean_ctor_set(v___x_2984_, 1, v___x_3071_);
lean_ctor_set(v___x_2984_, 0, v___x_3061_);
v___x_3074_ = v___x_2984_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v___x_3061_);
lean_ctor_set(v_reuseFailAlloc_3116_, 1, v___x_3071_);
v___x_3074_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3114_; 
lean_inc_n(v___x_3061_, 15);
v___x_3075_ = l_Lean_Syntax_node1(v___x_3061_, v___x_3072_, v___x_3074_);
v___x_3076_ = l_Lean_Syntax_node1(v___x_3061_, v___x_3067_, v___x_3075_);
lean_inc_ref_n(v___x_3070_, 10);
v___x_3077_ = l_Lean_Syntax_node7(v___x_3061_, v___x_3066_, v___x_3070_, v___x_3070_, v___x_3070_, v___x_3070_, v___x_3070_, v___x_3070_, v___x_3076_);
v___x_3078_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__3));
lean_inc_ref_n(v___y_2989_, 6);
v___x_3079_ = l_Lean_Name_mkStr4(v___x_2962_, v___y_2989_, v___x_3062_, v___x_3078_);
v___x_3080_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__4));
v___x_3081_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3081_, 0, v___x_3061_);
lean_ctor_set(v___x_3081_, 1, v___x_3080_);
v___x_3082_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__5));
v___x_3083_ = l_Lean_Name_mkStr4(v___x_2962_, v___y_2989_, v___x_3062_, v___x_3082_);
v___x_3084_ = l_Lean_mkIdent(v_auxFunName_2987_);
v___x_3085_ = l_Lean_Syntax_node2(v___x_3061_, v___x_3083_, v___x_3084_, v___x_3070_);
v___x_3086_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__6));
v___x_3087_ = l_Lean_Name_mkStr4(v___x_2962_, v___y_2989_, v___x_3062_, v___x_3086_);
v___x_3088_ = l_Array_append___redArg(v___x_3068_, v___x_3001_);
lean_dec_ref(v___x_3001_);
v___x_3089_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3089_, 0, v___x_3061_);
lean_ctor_set(v___x_3089_, 1, v___x_3067_);
lean_ctor_set(v___x_3089_, 2, v___x_3088_);
v___x_3090_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__9));
lean_inc_ref(v___y_2991_);
v___x_3091_ = l_Lean_Name_mkStr4(v___x_2962_, v___y_2989_, v___y_2991_, v___x_3090_);
v___x_3092_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__11));
v___x_3093_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3093_, 0, v___x_3061_);
lean_ctor_set(v___x_3093_, 1, v___x_3092_);
v___x_3094_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__7, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__7_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__7);
v___x_3095_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__8));
lean_inc(v_currMacroScope_3059_);
lean_inc(v_quotContext_3058_);
v___x_3096_ = l_Lean_addMacroScope(v_quotContext_3058_, v___x_3095_, v_currMacroScope_3059_);
v___x_3097_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__14));
v___x_3098_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3061_);
lean_ctor_set(v___x_3098_, 1, v___x_3094_);
lean_ctor_set(v___x_3098_, 2, v___x_3096_);
lean_ctor_set(v___x_3098_, 3, v___x_3097_);
v___x_3099_ = l_Lean_Syntax_node2(v___x_3061_, v___x_3091_, v___x_3093_, v___x_3098_);
v___x_3100_ = l_Lean_Syntax_node1(v___x_3061_, v___x_3067_, v___x_3099_);
v___x_3101_ = l_Lean_Syntax_node2(v___x_3061_, v___x_3087_, v___x_3089_, v___x_3100_);
v___x_3102_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__15));
v___x_3103_ = l_Lean_Name_mkStr4(v___x_2962_, v___y_2989_, v___x_3062_, v___x_3102_);
v___x_3104_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__27));
v___x_3105_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3105_, 0, v___x_3061_);
lean_ctor_set(v___x_3105_, 1, v___x_3104_);
v___x_3106_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__16));
v___x_3107_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__17));
v___x_3108_ = l_Lean_Name_mkStr4(v___x_2962_, v___y_2989_, v___x_3106_, v___x_3107_);
v___x_3109_ = l_Lean_Syntax_node2(v___x_3061_, v___x_3108_, v___x_3070_, v___x_3070_);
v___x_3110_ = l_Lean_Syntax_node4(v___x_3061_, v___x_3103_, v___x_3105_, v___y_2990_, v___x_3109_, v___x_3070_);
v___x_3111_ = l_Lean_Syntax_node5(v___x_3061_, v___x_3079_, v___x_3081_, v___x_3085_, v___x_3101_, v___x_3110_, v___x_3070_);
v___x_3112_ = l_Lean_Syntax_node2(v___x_3061_, v___x_3064_, v___x_3077_, v___x_3111_);
if (v_isShared_2979_ == 0)
{
lean_ctor_set(v___x_2978_, 0, v___x_3112_);
v___x_3114_ = v___x_2978_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v___x_3112_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
}
}
}
v___jp_3118_:
{
if (lean_obj_tag(v___y_3124_) == 0)
{
lean_object* v_a_3125_; 
v_a_3125_ = lean_ctor_get(v___y_3124_, 0);
lean_inc(v_a_3125_);
lean_dec_ref_known(v___y_3124_, 1);
v___y_2989_ = v___y_3119_;
v___y_2990_ = v___y_3120_;
v___y_2991_ = v___y_3122_;
v___y_2992_ = v___y_3121_;
v___y_2993_ = v___y_3123_;
v_a_2994_ = v_a_3125_;
goto v___jp_2988_;
}
else
{
lean_dec_ref(v___y_3121_);
lean_dec(v___y_3120_);
lean_dec(v_auxFunName_2987_);
lean_del_object(v___x_2984_);
lean_dec(v_snd_2982_);
lean_del_object(v___x_2978_);
lean_del_object(v___x_2970_);
return v___y_3124_;
}
}
v___jp_3126_:
{
lean_object* v_binders_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; uint8_t v___x_3142_; 
v_binders_3134_ = lean_ctor_get(v_a_2967_, 0);
lean_inc_ref(v_binders_3134_);
lean_dec(v_a_2967_);
v___x_3135_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__1));
v___x_3136_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__2));
v___x_3137_ = lean_box(0);
v___x_3138_ = lean_array_get_size(v_binders_3134_);
v___x_3139_ = lean_nat_sub(v___x_3138_, v___x_2964_);
v___x_3140_ = lean_array_get_borrowed(v___x_3137_, v_binders_3134_, v___x_3139_);
lean_dec(v___x_3139_);
v___x_3141_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__3));
lean_inc(v___x_3140_);
v___x_3142_ = l_Lean_Syntax_isOfKind(v___x_3140_, v___x_3141_);
if (v___x_3142_ == 0)
{
lean_object* v___x_3143_; lean_object* v___x_3144_; 
lean_dec(v_indVal_2961_);
v___x_3143_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20);
v___x_3144_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v___x_3143_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
v___y_3119_ = v___x_3135_;
v___y_3120_ = v_body_3127_;
v___y_3121_ = v_binders_3134_;
v___y_3122_ = v___x_3136_;
v___y_3123_ = v___y_3132_;
v___y_3124_ = v___x_3144_;
goto v___jp_3118_;
}
else
{
lean_object* v___x_3145_; uint8_t v___x_3146_; 
v___x_3145_ = l_Lean_Syntax_getArg(v___x_3140_, v___x_2964_);
lean_inc(v___x_3145_);
v___x_3146_ = l_Lean_Syntax_matchesNull(v___x_3145_, v___x_2964_);
if (v___x_3146_ == 0)
{
lean_object* v___x_3147_; lean_object* v___x_3148_; 
lean_dec(v___x_3145_);
lean_dec(v_indVal_2961_);
v___x_3147_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20);
v___x_3148_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v___x_3147_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
v___y_3119_ = v___x_3135_;
v___y_3120_ = v_body_3127_;
v___y_3121_ = v_binders_3134_;
v___y_3122_ = v___x_3136_;
v___y_3123_ = v___y_3132_;
v___y_3124_ = v___x_3148_;
goto v___jp_3118_;
}
else
{
lean_object* v___x_3149_; lean_object* v___x_3150_; uint8_t v___x_3151_; 
v___x_3149_ = lean_unsigned_to_nat(2u);
v___x_3150_ = l_Lean_Syntax_getArg(v___x_3140_, v___x_3149_);
lean_inc(v___x_3150_);
v___x_3151_ = l_Lean_Syntax_matchesNull(v___x_3150_, v___x_3149_);
if (v___x_3151_ == 0)
{
lean_object* v___x_3152_; lean_object* v___x_3153_; 
lean_dec(v___x_3150_);
lean_dec(v___x_3145_);
lean_dec(v_indVal_2961_);
v___x_3152_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20);
v___x_3153_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v___x_3152_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
v___y_3119_ = v___x_3135_;
v___y_3120_ = v_body_3127_;
v___y_3121_ = v_binders_3134_;
v___y_3122_ = v___x_3136_;
v___y_3123_ = v___y_3132_;
v___y_3124_ = v___x_3153_;
goto v___jp_3118_;
}
else
{
lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; uint8_t v___x_3157_; 
v___x_3154_ = lean_unsigned_to_nat(0u);
v___x_3155_ = lean_unsigned_to_nat(3u);
v___x_3156_ = l_Lean_Syntax_getArg(v___x_3140_, v___x_3155_);
v___x_3157_ = l_Lean_Syntax_matchesNull(v___x_3156_, v___x_3154_);
if (v___x_3157_ == 0)
{
lean_object* v___x_3158_; lean_object* v___x_3159_; 
lean_dec(v___x_3150_);
lean_dec(v___x_3145_);
lean_dec(v_indVal_2961_);
v___x_3158_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20);
v___x_3159_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v___x_3158_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
v___y_3119_ = v___x_3135_;
v___y_3120_ = v_body_3127_;
v___y_3121_ = v_binders_3134_;
v___y_3122_ = v___x_3136_;
v___y_3123_ = v___y_3132_;
v___y_3124_ = v___x_3159_;
goto v___jp_3118_;
}
else
{
lean_object* v___x_3160_; lean_object* v___x_3161_; 
v___x_3160_ = l_Lean_Syntax_getArg(v___x_3150_, v___x_2964_);
lean_dec(v___x_3150_);
v___x_3161_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType(v_indVal_2961_, v___x_3160_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
if (lean_obj_tag(v___x_3161_) == 0)
{
lean_object* v_a_3162_; lean_object* v_ref_3163_; lean_object* v___x_3164_; uint8_t v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; 
v_a_3162_ = lean_ctor_get(v___x_3161_, 0);
lean_inc(v_a_3162_);
lean_dec_ref_known(v___x_3161_, 1);
v_ref_3163_ = lean_ctor_get(v___y_3132_, 5);
v___x_3164_ = l_Lean_Syntax_getArg(v___x_3145_, v___x_3154_);
lean_dec(v___x_3145_);
v___x_3165_ = 0;
v___x_3166_ = l_Lean_SourceInfo_fromRef(v_ref_3163_, v___x_3165_);
v___x_3167_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__4));
lean_inc_n(v___x_3166_, 6);
v___x_3168_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3166_);
lean_ctor_set(v___x_3168_, 1, v___x_3167_);
v___x_3169_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_3170_ = l_Lean_Syntax_node1(v___x_3166_, v___x_3169_, v___x_3164_);
v___x_3171_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__11));
v___x_3172_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3166_);
lean_ctor_set(v___x_3172_, 1, v___x_3171_);
v___x_3173_ = l_Lean_Syntax_node2(v___x_3166_, v___x_3169_, v___x_3172_, v_a_3162_);
v___x_3174_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_3175_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3166_);
lean_ctor_set(v___x_3175_, 1, v___x_3169_);
lean_ctor_set(v___x_3175_, 2, v___x_3174_);
v___x_3176_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__13));
v___x_3177_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3166_);
lean_ctor_set(v___x_3177_, 1, v___x_3176_);
v___x_3178_ = l_Lean_Syntax_node5(v___x_3166_, v___x_3141_, v___x_3168_, v___x_3170_, v___x_3173_, v___x_3175_, v___x_3177_);
v___y_2989_ = v___x_3135_;
v___y_2990_ = v_body_3127_;
v___y_2991_ = v___x_3136_;
v___y_2992_ = v_binders_3134_;
v___y_2993_ = v___y_3132_;
v_a_2994_ = v___x_3178_;
goto v___jp_2988_;
}
else
{
lean_dec(v___x_3145_);
v___y_3119_ = v___x_3135_;
v___y_3120_ = v_body_3127_;
v___y_3121_ = v_binders_3134_;
v___y_3122_ = v___x_3136_;
v___y_3123_ = v___y_3132_;
v___y_3124_ = v___x_3161_;
goto v___jp_3118_;
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
lean_object* v_a_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3206_; 
lean_del_object(v___x_2970_);
lean_dec(v_a_2967_);
lean_dec(v_indVal_2961_);
lean_dec_ref(v_ctx_2948_);
v_a_3199_ = lean_ctor_get(v___x_2975_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3201_ = v___x_2975_;
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_a_3199_);
lean_dec(v___x_2975_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3204_; 
if (v_isShared_3202_ == 0)
{
v___x_3204_ = v___x_3201_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v_a_3199_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
}
}
}
else
{
lean_object* v_a_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3217_; 
lean_dec(v_indVal_2961_);
lean_dec_ref(v_ctx_2948_);
v_a_3210_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3212_ = v___x_2965_;
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_a_3210_);
lean_dec(v___x_2965_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3215_; 
if (v_isShared_3213_ == 0)
{
v___x_3215_ = v___x_3212_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_a_3210_);
v___x_3215_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
return v___x_3215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___boxed(lean_object* v_ctx_3218_, lean_object* v_i_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_){
_start:
{
lean_object* v_res_3227_; 
v_res_3227_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction(v_ctx_3218_, v_i_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_);
lean_dec(v_a_3225_);
lean_dec_ref(v_a_3224_);
lean_dec(v_a_3223_);
lean_dec_ref(v_a_3222_);
lean_dec(v_a_3221_);
lean_dec_ref(v_a_3220_);
lean_dec(v_i_3219_);
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0(size_t v_sz_3228_, size_t v_i_3229_, lean_object* v_bs_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_){
_start:
{
lean_object* v___x_3238_; 
v___x_3238_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg(v_sz_3228_, v_i_3229_, v_bs_3230_, v___y_3235_, v___y_3236_);
return v___x_3238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___boxed(lean_object* v_sz_3239_, lean_object* v_i_3240_, lean_object* v_bs_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_){
_start:
{
size_t v_sz_boxed_3249_; size_t v_i_boxed_3250_; lean_object* v_res_3251_; 
v_sz_boxed_3249_ = lean_unbox_usize(v_sz_3239_);
lean_dec(v_sz_3239_);
v_i_boxed_3250_ = lean_unbox_usize(v_i_3240_);
lean_dec(v_i_3240_);
v_res_3251_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0(v_sz_boxed_3249_, v_i_boxed_3250_, v_bs_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
return v_res_3251_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0___redArg(lean_object* v_upperBound_3252_, lean_object* v_ctx_3253_, lean_object* v_a_3254_, lean_object* v_b_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_){
_start:
{
uint8_t v___x_3263_; 
v___x_3263_ = lean_nat_dec_lt(v_a_3254_, v_upperBound_3252_);
if (v___x_3263_ == 0)
{
lean_object* v___x_3264_; 
lean_dec(v_a_3254_);
lean_dec_ref(v_ctx_3253_);
v___x_3264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3264_, 0, v_b_3255_);
return v___x_3264_;
}
else
{
lean_object* v___x_3265_; 
lean_inc_ref(v_ctx_3253_);
v___x_3265_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction(v_ctx_3253_, v_a_3254_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_);
if (lean_obj_tag(v___x_3265_) == 0)
{
lean_object* v_a_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; 
v_a_3266_ = lean_ctor_get(v___x_3265_, 0);
lean_inc(v_a_3266_);
lean_dec_ref_known(v___x_3265_, 1);
v___x_3267_ = lean_array_push(v_b_3255_, v_a_3266_);
v___x_3268_ = lean_unsigned_to_nat(1u);
v___x_3269_ = lean_nat_add(v_a_3254_, v___x_3268_);
lean_dec(v_a_3254_);
v_a_3254_ = v___x_3269_;
v_b_3255_ = v___x_3267_;
goto _start;
}
else
{
lean_object* v_a_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3278_; 
lean_dec_ref(v_b_3255_);
lean_dec(v_a_3254_);
lean_dec_ref(v_ctx_3253_);
v_a_3271_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3273_ = v___x_3265_;
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_a_3271_);
lean_dec(v___x_3265_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3276_; 
if (v_isShared_3274_ == 0)
{
v___x_3276_ = v___x_3273_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_a_3271_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0___redArg___boxed(lean_object* v_upperBound_3279_, lean_object* v_ctx_3280_, lean_object* v_a_3281_, lean_object* v_b_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_){
_start:
{
lean_object* v_res_3290_; 
v_res_3290_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0___redArg(v_upperBound_3279_, v_ctx_3280_, v_a_3281_, v_b_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_);
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3287_);
lean_dec(v___y_3286_);
lean_dec_ref(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
lean_dec(v_upperBound_3279_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions(lean_object* v_ctx_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_){
_start:
{
lean_object* v_typeInfos_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v_auxDefs_3309_; lean_object* v___x_3310_; 
v_typeInfos_3306_ = lean_ctor_get(v_ctx_3298_, 1);
v___x_3307_ = lean_array_get_size(v_typeInfos_3306_);
v___x_3308_ = lean_unsigned_to_nat(0u);
v_auxDefs_3309_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__0));
v___x_3310_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0___redArg(v___x_3307_, v_ctx_3298_, v___x_3308_, v_auxDefs_3309_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_, v_a_3304_);
if (lean_obj_tag(v___x_3310_) == 0)
{
lean_object* v_a_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3331_; 
v_a_3311_ = lean_ctor_get(v___x_3310_, 0);
v_isSharedCheck_3331_ = !lean_is_exclusive(v___x_3310_);
if (v_isSharedCheck_3331_ == 0)
{
v___x_3313_ = v___x_3310_;
v_isShared_3314_ = v_isSharedCheck_3331_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_a_3311_);
lean_dec(v___x_3310_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3331_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v_ref_3315_; uint8_t v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3329_; 
v_ref_3315_ = lean_ctor_get(v_a_3303_, 5);
v___x_3316_ = 0;
v___x_3317_ = l_Lean_SourceInfo_fromRef(v_ref_3315_, v___x_3316_);
v___x_3318_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions___closed__0));
v___x_3319_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions___closed__1));
lean_inc_n(v___x_3317_, 3);
v___x_3320_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3317_);
lean_ctor_set(v___x_3320_, 1, v___x_3318_);
v___x_3321_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_3322_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_3323_ = l_Array_append___redArg(v___x_3322_, v_a_3311_);
lean_dec(v_a_3311_);
v___x_3324_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3317_);
lean_ctor_set(v___x_3324_, 1, v___x_3321_);
lean_ctor_set(v___x_3324_, 2, v___x_3323_);
v___x_3325_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions___closed__2));
v___x_3326_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3317_);
lean_ctor_set(v___x_3326_, 1, v___x_3325_);
v___x_3327_ = l_Lean_Syntax_node3(v___x_3317_, v___x_3319_, v___x_3320_, v___x_3324_, v___x_3326_);
if (v_isShared_3314_ == 0)
{
lean_ctor_set(v___x_3313_, 0, v___x_3327_);
v___x_3329_ = v___x_3313_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v___x_3327_);
v___x_3329_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
return v___x_3329_;
}
}
}
else
{
lean_object* v_a_3332_; lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3339_; 
v_a_3332_ = lean_ctor_get(v___x_3310_, 0);
v_isSharedCheck_3339_ = !lean_is_exclusive(v___x_3310_);
if (v_isSharedCheck_3339_ == 0)
{
v___x_3334_ = v___x_3310_;
v_isShared_3335_ = v_isSharedCheck_3339_;
goto v_resetjp_3333_;
}
else
{
lean_inc(v_a_3332_);
lean_dec(v___x_3310_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3339_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
lean_object* v___x_3337_; 
if (v_isShared_3335_ == 0)
{
v___x_3337_ = v___x_3334_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v_a_3332_);
v___x_3337_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
return v___x_3337_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions___boxed(lean_object* v_ctx_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_){
_start:
{
lean_object* v_res_3348_; 
v_res_3348_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions(v_ctx_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_);
lean_dec(v_a_3346_);
lean_dec_ref(v_a_3345_);
lean_dec(v_a_3344_);
lean_dec_ref(v_a_3343_);
lean_dec(v_a_3342_);
lean_dec_ref(v_a_3341_);
return v_res_3348_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0(lean_object* v_upperBound_3349_, lean_object* v_ctx_3350_, lean_object* v_inst_3351_, lean_object* v_R_3352_, lean_object* v_a_3353_, lean_object* v_b_3354_, lean_object* v_c_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_){
_start:
{
lean_object* v___x_3363_; 
v___x_3363_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0___redArg(v_upperBound_3349_, v_ctx_3350_, v_a_3353_, v_b_3354_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_);
return v___x_3363_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0___boxed(lean_object* v_upperBound_3364_, lean_object* v_ctx_3365_, lean_object* v_inst_3366_, lean_object* v_R_3367_, lean_object* v_a_3368_, lean_object* v_b_3369_, lean_object* v_c_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_){
_start:
{
lean_object* v_res_3378_; 
v_res_3378_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0(v_upperBound_3364_, v_ctx_3365_, v_inst_3366_, v_R_3367_, v_a_3368_, v_b_3369_, v_c_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_);
lean_dec(v___y_3376_);
lean_dec_ref(v___y_3375_);
lean_dec(v___y_3374_);
lean_dec_ref(v___y_3373_);
lean_dec(v___y_3372_);
lean_dec_ref(v___y_3371_);
lean_dec(v_upperBound_3364_);
return v_res_3378_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0_spec__0(lean_object* v_a_3379_, lean_object* v_as_3380_, size_t v_i_3381_, size_t v_stop_3382_){
_start:
{
uint8_t v___x_3383_; 
v___x_3383_ = lean_usize_dec_eq(v_i_3381_, v_stop_3382_);
if (v___x_3383_ == 0)
{
lean_object* v___x_3384_; uint8_t v___x_3385_; 
v___x_3384_ = lean_array_uget_borrowed(v_as_3380_, v_i_3381_);
v___x_3385_ = lean_name_eq(v_a_3379_, v___x_3384_);
if (v___x_3385_ == 0)
{
size_t v___x_3386_; size_t v___x_3387_; 
v___x_3386_ = ((size_t)1ULL);
v___x_3387_ = lean_usize_add(v_i_3381_, v___x_3386_);
v_i_3381_ = v___x_3387_;
goto _start;
}
else
{
return v___x_3385_;
}
}
else
{
uint8_t v___x_3389_; 
v___x_3389_ = 0;
return v___x_3389_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0_spec__0___boxed(lean_object* v_a_3390_, lean_object* v_as_3391_, lean_object* v_i_3392_, lean_object* v_stop_3393_){
_start:
{
size_t v_i_boxed_3394_; size_t v_stop_boxed_3395_; uint8_t v_res_3396_; lean_object* v_r_3397_; 
v_i_boxed_3394_ = lean_unbox_usize(v_i_3392_);
lean_dec(v_i_3392_);
v_stop_boxed_3395_ = lean_unbox_usize(v_stop_3393_);
lean_dec(v_stop_3393_);
v_res_3396_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0_spec__0(v_a_3390_, v_as_3391_, v_i_boxed_3394_, v_stop_boxed_3395_);
lean_dec_ref(v_as_3391_);
lean_dec(v_a_3390_);
v_r_3397_ = lean_box(v_res_3396_);
return v_r_3397_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0(lean_object* v_as_3398_, lean_object* v_a_3399_){
_start:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; uint8_t v___x_3402_; 
v___x_3400_ = lean_unsigned_to_nat(0u);
v___x_3401_ = lean_array_get_size(v_as_3398_);
v___x_3402_ = lean_nat_dec_lt(v___x_3400_, v___x_3401_);
if (v___x_3402_ == 0)
{
return v___x_3402_;
}
else
{
if (v___x_3402_ == 0)
{
return v___x_3402_;
}
else
{
size_t v___x_3403_; size_t v___x_3404_; uint8_t v___x_3405_; 
v___x_3403_ = ((size_t)0ULL);
v___x_3404_ = lean_usize_of_nat(v___x_3401_);
v___x_3405_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0_spec__0(v_a_3399_, v_as_3398_, v___x_3403_, v___x_3404_);
return v___x_3405_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0___boxed(lean_object* v_as_3406_, lean_object* v_a_3407_){
_start:
{
uint8_t v_res_3408_; lean_object* v_r_3409_; 
v_res_3408_ = l_Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0(v_as_3406_, v_a_3407_);
lean_dec(v_a_3407_);
lean_dec_ref(v_as_3406_);
v_r_3409_ = lean_box(v_res_3408_);
return v_r_3409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg(size_t v_sz_3416_, size_t v_i_3417_, lean_object* v_bs_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_){
_start:
{
uint8_t v___x_3422_; 
v___x_3422_ = lean_usize_dec_lt(v_i_3417_, v_sz_3416_);
if (v___x_3422_ == 0)
{
lean_object* v___x_3423_; 
v___x_3423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3423_, 0, v_bs_3418_);
return v___x_3423_;
}
else
{
lean_object* v___x_3424_; lean_object* v___x_3425_; 
v___x_3424_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__1));
v___x_3425_ = l_Lean_Core_mkFreshUserName(v___x_3424_, v___y_3419_, v___y_3420_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_object* v_a_3426_; lean_object* v_ref_3427_; lean_object* v_quotContext_3428_; lean_object* v_currMacroScope_3429_; lean_object* v_v_3430_; lean_object* v___x_3431_; lean_object* v_bs_x27_3432_; lean_object* v___x_3433_; uint8_t v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; size_t v___x_3460_; size_t v___x_3461_; lean_object* v___x_3462_; 
v_a_3426_ = lean_ctor_get(v___x_3425_, 0);
lean_inc(v_a_3426_);
lean_dec_ref_known(v___x_3425_, 1);
v_ref_3427_ = lean_ctor_get(v___y_3419_, 5);
v_quotContext_3428_ = lean_ctor_get(v___y_3419_, 10);
v_currMacroScope_3429_ = lean_ctor_get(v___y_3419_, 11);
v_v_3430_ = lean_array_uget(v_bs_3418_, v_i_3417_);
v___x_3431_ = lean_unsigned_to_nat(0u);
v_bs_x27_3432_ = lean_array_uset(v_bs_3418_, v_i_3417_, v___x_3431_);
v___x_3433_ = l_Lean_mkIdent(v_a_3426_);
v___x_3434_ = 0;
v___x_3435_ = l_Lean_SourceInfo_fromRef(v_ref_3427_, v___x_3434_);
v___x_3436_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg___closed__1));
v___x_3437_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__13));
lean_inc_n(v___x_3435_, 9);
v___x_3438_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3435_);
lean_ctor_set(v___x_3438_, 1, v___x_3437_);
v___x_3439_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_3440_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__11));
v___x_3441_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3441_, 0, v___x_3435_);
lean_ctor_set(v___x_3441_, 1, v___x_3440_);
lean_inc(v___x_3433_);
v___x_3442_ = l_Lean_Syntax_node2(v___x_3435_, v___x_3439_, v___x_3433_, v___x_3441_);
v___x_3443_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__6));
v___x_3444_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__5);
v___x_3445_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__6));
lean_inc(v_currMacroScope_3429_);
lean_inc(v_quotContext_3428_);
v___x_3446_ = l_Lean_addMacroScope(v_quotContext_3428_, v___x_3445_, v_currMacroScope_3429_);
v___x_3447_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__12));
v___x_3448_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3448_, 0, v___x_3435_);
lean_ctor_set(v___x_3448_, 1, v___x_3444_);
lean_ctor_set(v___x_3448_, 2, v___x_3446_);
lean_ctor_set(v___x_3448_, 3, v___x_3447_);
v___x_3449_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__7));
v___x_3450_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3450_, 0, v___x_3435_);
lean_ctor_set(v___x_3450_, 1, v___x_3449_);
v___x_3451_ = l_Lean_mkIdent(v_v_3430_);
v___x_3452_ = l_Lean_Syntax_node1(v___x_3435_, v___x_3439_, v___x_3451_);
v___x_3453_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__10));
v___x_3454_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3454_, 0, v___x_3435_);
lean_ctor_set(v___x_3454_, 1, v___x_3453_);
v___x_3455_ = l_Lean_Syntax_node4(v___x_3435_, v___x_3443_, v___x_3448_, v___x_3450_, v___x_3452_, v___x_3454_);
v___x_3456_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__14));
v___x_3457_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3435_);
lean_ctor_set(v___x_3457_, 1, v___x_3456_);
v___x_3458_ = l_Lean_Syntax_node4(v___x_3435_, v___x_3436_, v___x_3438_, v___x_3442_, v___x_3455_, v___x_3457_);
v___x_3459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3459_, 0, v___x_3433_);
lean_ctor_set(v___x_3459_, 1, v___x_3458_);
v___x_3460_ = ((size_t)1ULL);
v___x_3461_ = lean_usize_add(v_i_3417_, v___x_3460_);
v___x_3462_ = lean_array_uset(v_bs_x27_3432_, v_i_3417_, v___x_3459_);
v_i_3417_ = v___x_3461_;
v_bs_3418_ = v___x_3462_;
goto _start;
}
else
{
lean_object* v_a_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3471_; 
lean_dec_ref(v_bs_3418_);
v_a_3464_ = lean_ctor_get(v___x_3425_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3466_ = v___x_3425_;
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_a_3464_);
lean_dec(v___x_3425_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3469_; 
if (v_isShared_3467_ == 0)
{
v___x_3469_ = v___x_3466_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_a_3464_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg___boxed(lean_object* v_sz_3472_, lean_object* v_i_3473_, lean_object* v_bs_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_){
_start:
{
size_t v_sz_boxed_3478_; size_t v_i_boxed_3479_; lean_object* v_res_3480_; 
v_sz_boxed_3478_ = lean_unbox_usize(v_sz_3472_);
lean_dec(v_sz_3472_);
v_i_boxed_3479_ = lean_unbox_usize(v_i_3473_);
lean_dec(v_i_3473_);
v_res_3480_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg(v_sz_boxed_3478_, v_i_boxed_3479_, v_bs_3474_, v___y_3475_, v___y_3476_);
lean_dec(v___y_3476_);
lean_dec_ref(v___y_3475_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__2(size_t v_sz_3481_, size_t v_i_3482_, lean_object* v_bs_3483_){
_start:
{
uint8_t v___x_3484_; 
v___x_3484_ = lean_usize_dec_lt(v_i_3482_, v_sz_3481_);
if (v___x_3484_ == 0)
{
return v_bs_3483_;
}
else
{
lean_object* v_v_3485_; lean_object* v___x_3486_; lean_object* v_bs_x27_3487_; size_t v___x_3488_; size_t v___x_3489_; lean_object* v___x_3490_; 
v_v_3485_ = lean_array_uget(v_bs_3483_, v_i_3482_);
v___x_3486_ = lean_unsigned_to_nat(0u);
v_bs_x27_3487_ = lean_array_uset(v_bs_3483_, v_i_3482_, v___x_3486_);
v___x_3488_ = ((size_t)1ULL);
v___x_3489_ = lean_usize_add(v_i_3482_, v___x_3488_);
v___x_3490_ = lean_array_uset(v_bs_x27_3487_, v_i_3482_, v_v_3485_);
v_i_3482_ = v___x_3489_;
v_bs_3483_ = v___x_3490_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__2___boxed(lean_object* v_sz_3492_, lean_object* v_i_3493_, lean_object* v_bs_3494_){
_start:
{
size_t v_sz_boxed_3495_; size_t v_i_boxed_3496_; lean_object* v_res_3497_; 
v_sz_boxed_3495_ = lean_unbox_usize(v_sz_3492_);
lean_dec(v_sz_3492_);
v_i_boxed_3496_ = lean_unbox_usize(v_i_3493_);
lean_dec(v_i_3493_);
v_res_3497_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__2(v_sz_boxed_3495_, v_i_boxed_3496_, v_bs_3494_);
return v_res_3497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3(lean_object* v_typeNames_3538_, lean_object* v_as_3539_, size_t v_sz_3540_, size_t v_i_3541_, lean_object* v_b_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_){
_start:
{
lean_object* v_a_3551_; uint8_t v___x_3555_; 
v___x_3555_ = lean_usize_dec_lt(v_i_3541_, v_sz_3540_);
if (v___x_3555_ == 0)
{
lean_object* v___x_3556_; 
v___x_3556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3556_, 0, v_b_3542_);
return v___x_3556_;
}
else
{
lean_object* v_snd_3557_; lean_object* v_fst_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3769_; 
v_snd_3557_ = lean_ctor_get(v_b_3542_, 1);
v_fst_3558_ = lean_ctor_get(v_b_3542_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v_b_3542_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3560_ = v_b_3542_;
v_isShared_3561_ = v_isSharedCheck_3769_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_snd_3557_);
lean_inc(v_fst_3558_);
lean_dec(v_b_3542_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3769_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v_array_3562_; lean_object* v_start_3563_; lean_object* v_stop_3564_; uint8_t v___x_3565_; 
v_array_3562_ = lean_ctor_get(v_snd_3557_, 0);
v_start_3563_ = lean_ctor_get(v_snd_3557_, 1);
v_stop_3564_ = lean_ctor_get(v_snd_3557_, 2);
v___x_3565_ = lean_nat_dec_lt(v_start_3563_, v_stop_3564_);
if (v___x_3565_ == 0)
{
lean_object* v___x_3567_; 
if (v_isShared_3561_ == 0)
{
v___x_3567_ = v___x_3560_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_fst_3558_);
lean_ctor_set(v_reuseFailAlloc_3569_, 1, v_snd_3557_);
v___x_3567_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
lean_object* v___x_3568_; 
v___x_3568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3567_);
return v___x_3568_;
}
}
else
{
lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3765_; 
lean_inc(v_stop_3564_);
lean_inc(v_start_3563_);
lean_inc_ref(v_array_3562_);
v_isSharedCheck_3765_ = !lean_is_exclusive(v_snd_3557_);
if (v_isSharedCheck_3765_ == 0)
{
lean_object* v_unused_3766_; lean_object* v_unused_3767_; lean_object* v_unused_3768_; 
v_unused_3766_ = lean_ctor_get(v_snd_3557_, 2);
lean_dec(v_unused_3766_);
v_unused_3767_ = lean_ctor_get(v_snd_3557_, 1);
lean_dec(v_unused_3767_);
v_unused_3768_ = lean_ctor_get(v_snd_3557_, 0);
lean_dec(v_unused_3768_);
v___x_3571_ = v_snd_3557_;
v_isShared_3572_ = v_isSharedCheck_3765_;
goto v_resetjp_3570_;
}
else
{
lean_dec(v_snd_3557_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3765_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v_a_3573_; lean_object* v_toConstantVal_3574_; lean_object* v_name_3575_; lean_object* v_levelParams_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3763_; 
v_a_3573_ = lean_array_uget_borrowed(v_as_3539_, v_i_3541_);
v_toConstantVal_3574_ = lean_ctor_get(v_a_3573_, 0);
lean_inc_ref(v_toConstantVal_3574_);
v_name_3575_ = lean_ctor_get(v_toConstantVal_3574_, 0);
v_levelParams_3576_ = lean_ctor_get(v_toConstantVal_3574_, 1);
v_isSharedCheck_3763_ = !lean_is_exclusive(v_toConstantVal_3574_);
if (v_isSharedCheck_3763_ == 0)
{
lean_object* v_unused_3764_; 
v_unused_3764_ = lean_ctor_get(v_toConstantVal_3574_, 2);
lean_dec(v_unused_3764_);
v___x_3578_ = v_toConstantVal_3574_;
v_isShared_3579_ = v_isSharedCheck_3763_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_levelParams_3576_);
lean_inc(v_name_3575_);
lean_dec(v_toConstantVal_3574_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3763_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3584_; 
v___x_3580_ = lean_array_fget(v_array_3562_, v_start_3563_);
v___x_3581_ = lean_unsigned_to_nat(1u);
v___x_3582_ = lean_nat_add(v_start_3563_, v___x_3581_);
lean_dec(v_start_3563_);
if (v_isShared_3572_ == 0)
{
lean_ctor_set(v___x_3571_, 1, v___x_3582_);
v___x_3584_ = v___x_3571_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v_array_3562_);
lean_ctor_set(v_reuseFailAlloc_3762_, 1, v___x_3582_);
lean_ctor_set(v_reuseFailAlloc_3762_, 2, v_stop_3564_);
v___x_3584_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
uint8_t v___x_3585_; 
v___x_3585_ = l_Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0(v_typeNames_3538_, v_name_3575_);
if (v___x_3585_ == 0)
{
lean_object* v___x_3587_; 
lean_dec(v___x_3580_);
lean_del_object(v___x_3578_);
lean_dec(v_levelParams_3576_);
lean_dec(v_name_3575_);
if (v_isShared_3561_ == 0)
{
lean_ctor_set(v___x_3560_, 1, v___x_3584_);
v___x_3587_ = v___x_3560_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_fst_3558_);
lean_ctor_set(v_reuseFailAlloc_3588_, 1, v___x_3584_);
v___x_3587_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
v_a_3551_ = v___x_3587_;
goto v___jp_3550_;
}
}
else
{
lean_object* v___x_3589_; 
lean_del_object(v___x_3560_);
lean_inc(v_a_3573_);
v___x_3589_ = l_Lean_Elab_Deriving_mkInductArgNames(v_a_3573_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
if (lean_obj_tag(v___x_3589_) == 0)
{
lean_object* v_a_3590_; lean_object* v___x_3591_; 
v_a_3590_ = lean_ctor_get(v___x_3589_, 0);
lean_inc_n(v_a_3590_, 2);
lean_dec_ref_known(v___x_3589_, 1);
v___x_3591_ = l_Lean_Elab_Deriving_mkImplicitBinders(v_a_3590_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
if (lean_obj_tag(v___x_3591_) == 0)
{
lean_object* v_a_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; 
v_a_3592_ = lean_ctor_get(v___x_3591_, 0);
lean_inc(v_a_3592_);
lean_dec_ref_known(v___x_3591_, 1);
v___x_3593_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__14));
lean_inc(v_a_3590_);
lean_inc(v_a_3573_);
v___x_3594_ = l_Lean_Elab_Deriving_mkInstImplicitBinders(v___x_3593_, v_a_3573_, v_a_3590_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
if (lean_obj_tag(v___x_3594_) == 0)
{
lean_object* v_a_3595_; lean_object* v___x_3596_; size_t v_sz_3597_; size_t v___x_3598_; lean_object* v___x_3599_; 
v_a_3595_ = lean_ctor_get(v___x_3594_, 0);
lean_inc(v_a_3595_);
lean_dec_ref_known(v___x_3594_, 1);
v___x_3596_ = lean_array_mk(v_levelParams_3576_);
v_sz_3597_ = lean_array_size(v___x_3596_);
v___x_3598_ = ((size_t)0ULL);
v___x_3599_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg(v_sz_3597_, v___x_3598_, v___x_3596_, v___y_3547_, v___y_3548_);
if (lean_obj_tag(v___x_3599_) == 0)
{
lean_object* v_a_3600_; lean_object* v___x_3601_; lean_object* v_fst_3602_; lean_object* v_snd_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3729_; 
v_a_3600_ = lean_ctor_get(v___x_3599_, 0);
lean_inc(v_a_3600_);
lean_dec_ref_known(v___x_3599_, 1);
v___x_3601_ = l_Array_unzip___redArg(v_a_3600_);
lean_dec(v_a_3600_);
v_fst_3602_ = lean_ctor_get(v___x_3601_, 0);
v_snd_3603_ = lean_ctor_get(v___x_3601_, 1);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3605_ = v___x_3601_;
v_isShared_3606_ = v_isSharedCheck_3729_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_snd_3603_);
lean_inc(v_fst_3602_);
lean_dec(v___x_3601_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3729_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___x_3607_; 
lean_inc(v_a_3590_);
lean_inc(v_a_3573_);
v___x_3607_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v_a_3573_, v_a_3590_, v___y_3547_);
if (lean_obj_tag(v___x_3607_) == 0)
{
lean_object* v_a_3608_; lean_object* v___x_3609_; 
v_a_3608_ = lean_ctor_get(v___x_3607_, 0);
lean_inc(v_a_3608_);
lean_dec_ref_known(v___x_3607_, 1);
lean_inc(v_a_3573_);
v___x_3609_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType(v_a_3573_, v_a_3608_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
if (lean_obj_tag(v___x_3609_) == 0)
{
lean_object* v_a_3610_; lean_object* v___x_3611_; 
v_a_3610_ = lean_ctor_get(v___x_3609_, 0);
lean_inc(v_a_3610_);
lean_dec_ref_known(v___x_3609_, 1);
lean_inc(v_a_3573_);
v___x_3611_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr(v_a_3573_, v_a_3590_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
if (lean_obj_tag(v___x_3611_) == 0)
{
lean_object* v_a_3612_; lean_object* v___x_3613_; 
v_a_3612_ = lean_ctor_get(v___x_3611_, 0);
lean_inc(v_a_3612_);
lean_dec_ref_known(v___x_3611_, 1);
v___x_3613_ = l_Lean_Elab_Deriving_mkInstName(v___x_3593_, v_name_3575_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_object* v_a_3614_; lean_object* v_ref_3615_; lean_object* v_quotContext_3616_; lean_object* v_currMacroScope_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; uint8_t v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3627_; 
v_a_3614_ = lean_ctor_get(v___x_3613_, 0);
lean_inc(v_a_3614_);
lean_dec_ref_known(v___x_3613_, 1);
v_ref_3615_ = lean_ctor_get(v___y_3547_, 5);
v_quotContext_3616_ = lean_ctor_get(v___y_3547_, 10);
v_currMacroScope_3617_ = lean_ctor_get(v___y_3547_, 11);
v___x_3618_ = l_Array_append___redArg(v_a_3592_, v_a_3595_);
lean_dec(v_a_3595_);
v___x_3619_ = l_Array_append___redArg(v___x_3618_, v_snd_3603_);
lean_dec(v_snd_3603_);
v___x_3620_ = 0;
v___x_3621_ = l_Lean_SourceInfo_fromRef(v_ref_3615_, v___x_3620_);
v___x_3622_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__0));
v___x_3623_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__1));
v___x_3624_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_3625_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
lean_inc(v___x_3621_);
if (v_isShared_3579_ == 0)
{
lean_ctor_set_tag(v___x_3578_, 1);
lean_ctor_set(v___x_3578_, 2, v___x_3625_);
lean_ctor_set(v___x_3578_, 1, v___x_3624_);
lean_ctor_set(v___x_3578_, 0, v___x_3621_);
v___x_3627_ = v___x_3578_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v___x_3621_);
lean_ctor_set(v_reuseFailAlloc_3696_, 1, v___x_3624_);
lean_ctor_set(v_reuseFailAlloc_3696_, 2, v___x_3625_);
v___x_3627_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3626_;
}
v_reusejp_3626_:
{
lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; size_t v_sz_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3694_; 
lean_inc_ref_n(v___x_3627_, 19);
lean_inc_n(v___x_3621_, 30);
v___x_3628_ = l_Lean_Syntax_node7(v___x_3621_, v___x_3623_, v___x_3627_, v___x_3627_, v___x_3627_, v___x_3627_, v___x_3627_, v___x_3627_, v___x_3627_);
v___x_3629_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__2));
v___x_3630_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__3));
v___x_3631_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__5));
v___x_3632_ = l_Lean_Syntax_node1(v___x_3621_, v___x_3631_, v___x_3627_);
v___x_3633_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3633_, 0, v___x_3621_);
lean_ctor_set(v___x_3633_, 1, v___x_3629_);
v___x_3634_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__6));
v___x_3635_ = l_Lean_mkIdent(v_a_3614_);
v___x_3636_ = l_Lean_Syntax_node2(v___x_3621_, v___x_3634_, v___x_3635_, v___x_3627_);
v___x_3637_ = l_Lean_Syntax_node1(v___x_3621_, v___x_3624_, v___x_3636_);
v___x_3638_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__8));
v___x_3639_ = l_Array_append___redArg(v___x_3625_, v___x_3619_);
lean_dec_ref(v___x_3619_);
v___x_3640_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3640_, 0, v___x_3621_);
lean_ctor_set(v___x_3640_, 1, v___x_3624_);
lean_ctor_set(v___x_3640_, 2, v___x_3639_);
v___x_3641_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__10));
v___x_3642_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__11));
v___x_3643_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3643_, 0, v___x_3621_);
lean_ctor_set(v___x_3643_, 1, v___x_3642_);
v___x_3644_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_3645_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__12);
v___x_3646_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__13));
lean_inc_n(v_currMacroScope_3617_, 3);
lean_inc_n(v_quotContext_3616_, 3);
v___x_3647_ = l_Lean_addMacroScope(v_quotContext_3616_, v___x_3646_, v_currMacroScope_3617_);
v___x_3648_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__26));
v___x_3649_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3649_, 0, v___x_3621_);
lean_ctor_set(v___x_3649_, 1, v___x_3645_);
lean_ctor_set(v___x_3649_, 2, v___x_3647_);
lean_ctor_set(v___x_3649_, 3, v___x_3648_);
v___x_3650_ = l_Lean_Syntax_node1(v___x_3621_, v___x_3624_, v_a_3610_);
v___x_3651_ = l_Lean_Syntax_node2(v___x_3621_, v___x_3644_, v___x_3649_, v___x_3650_);
v___x_3652_ = l_Lean_Syntax_node2(v___x_3621_, v___x_3641_, v___x_3643_, v___x_3651_);
v___x_3653_ = l_Lean_Syntax_node2(v___x_3621_, v___x_3638_, v___x_3640_, v___x_3652_);
v___x_3654_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__10));
v___x_3655_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__11));
v___x_3656_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3656_, 0, v___x_3621_);
lean_ctor_set(v___x_3656_, 1, v___x_3655_);
v___x_3657_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__32));
v___x_3658_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__34));
v___x_3659_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__36));
v___x_3660_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1);
v___x_3661_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__2));
v___x_3662_ = l_Lean_addMacroScope(v_quotContext_3616_, v___x_3661_, v_currMacroScope_3617_);
v___x_3663_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__6));
v___x_3664_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3621_);
lean_ctor_set(v___x_3664_, 1, v___x_3660_);
lean_ctor_set(v___x_3664_, 2, v___x_3662_);
lean_ctor_set(v___x_3664_, 3, v___x_3663_);
v___x_3665_ = l_Lean_Syntax_node2(v___x_3621_, v___x_3659_, v___x_3664_, v___x_3627_);
v___x_3666_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__38));
v___x_3667_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__27));
v___x_3668_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3668_, 0, v___x_3621_);
lean_ctor_set(v___x_3668_, 1, v___x_3667_);
v___x_3669_ = l_Lean_mkIdent(v___x_3580_);
v_sz_3670_ = lean_array_size(v_fst_3602_);
v___x_3671_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__2(v_sz_3670_, v___x_3598_, v_fst_3602_);
v___x_3672_ = l_Array_append___redArg(v___x_3625_, v___x_3671_);
lean_dec_ref(v___x_3671_);
v___x_3673_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3673_, 0, v___x_3621_);
lean_ctor_set(v___x_3673_, 1, v___x_3624_);
lean_ctor_set(v___x_3673_, 2, v___x_3672_);
v___x_3674_ = l_Lean_Syntax_node2(v___x_3621_, v___x_3644_, v___x_3669_, v___x_3673_);
lean_inc_ref(v___x_3668_);
v___x_3675_ = l_Lean_Syntax_node3(v___x_3621_, v___x_3666_, v___x_3668_, v___x_3627_, v___x_3674_);
v___x_3676_ = l_Lean_Syntax_node3(v___x_3621_, v___x_3624_, v___x_3627_, v___x_3627_, v___x_3675_);
v___x_3677_ = l_Lean_Syntax_node2(v___x_3621_, v___x_3658_, v___x_3665_, v___x_3676_);
v___x_3678_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8);
v___x_3679_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__9));
v___x_3680_ = l_Lean_addMacroScope(v_quotContext_3616_, v___x_3679_, v_currMacroScope_3617_);
v___x_3681_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__12));
v___x_3682_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3682_, 0, v___x_3621_);
lean_ctor_set(v___x_3682_, 1, v___x_3678_);
lean_ctor_set(v___x_3682_, 2, v___x_3680_);
lean_ctor_set(v___x_3682_, 3, v___x_3681_);
v___x_3683_ = l_Lean_Syntax_node2(v___x_3621_, v___x_3659_, v___x_3682_, v___x_3627_);
v___x_3684_ = l_Lean_Syntax_node3(v___x_3621_, v___x_3666_, v___x_3668_, v___x_3627_, v_a_3612_);
v___x_3685_ = l_Lean_Syntax_node3(v___x_3621_, v___x_3624_, v___x_3627_, v___x_3627_, v___x_3684_);
v___x_3686_ = l_Lean_Syntax_node2(v___x_3621_, v___x_3658_, v___x_3683_, v___x_3685_);
v___x_3687_ = l_Lean_Syntax_node3(v___x_3621_, v___x_3624_, v___x_3677_, v___x_3627_, v___x_3686_);
v___x_3688_ = l_Lean_Syntax_node1(v___x_3621_, v___x_3657_, v___x_3687_);
v___x_3689_ = l_Lean_Syntax_node3(v___x_3621_, v___x_3654_, v___x_3656_, v___x_3688_, v___x_3627_);
v___x_3690_ = l_Lean_Syntax_node6(v___x_3621_, v___x_3630_, v___x_3632_, v___x_3633_, v___x_3627_, v___x_3637_, v___x_3653_, v___x_3689_);
v___x_3691_ = l_Lean_Syntax_node2(v___x_3621_, v___x_3622_, v___x_3628_, v___x_3690_);
v___x_3692_ = lean_array_push(v_fst_3558_, v___x_3691_);
if (v_isShared_3606_ == 0)
{
lean_ctor_set(v___x_3605_, 1, v___x_3584_);
lean_ctor_set(v___x_3605_, 0, v___x_3692_);
v___x_3694_ = v___x_3605_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v___x_3692_);
lean_ctor_set(v_reuseFailAlloc_3695_, 1, v___x_3584_);
v___x_3694_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
v_a_3551_ = v___x_3694_;
goto v___jp_3550_;
}
}
}
else
{
lean_object* v_a_3697_; lean_object* v___x_3699_; uint8_t v_isShared_3700_; uint8_t v_isSharedCheck_3704_; 
lean_dec(v_a_3612_);
lean_dec(v_a_3610_);
lean_del_object(v___x_3605_);
lean_dec(v_snd_3603_);
lean_dec(v_fst_3602_);
lean_dec(v_a_3595_);
lean_dec(v_a_3592_);
lean_dec_ref(v___x_3584_);
lean_dec(v___x_3580_);
lean_del_object(v___x_3578_);
lean_dec(v_fst_3558_);
v_a_3697_ = lean_ctor_get(v___x_3613_, 0);
v_isSharedCheck_3704_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3704_ == 0)
{
v___x_3699_ = v___x_3613_;
v_isShared_3700_ = v_isSharedCheck_3704_;
goto v_resetjp_3698_;
}
else
{
lean_inc(v_a_3697_);
lean_dec(v___x_3613_);
v___x_3699_ = lean_box(0);
v_isShared_3700_ = v_isSharedCheck_3704_;
goto v_resetjp_3698_;
}
v_resetjp_3698_:
{
lean_object* v___x_3702_; 
if (v_isShared_3700_ == 0)
{
v___x_3702_ = v___x_3699_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3703_; 
v_reuseFailAlloc_3703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3703_, 0, v_a_3697_);
v___x_3702_ = v_reuseFailAlloc_3703_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
return v___x_3702_;
}
}
}
}
else
{
lean_object* v_a_3705_; lean_object* v___x_3707_; uint8_t v_isShared_3708_; uint8_t v_isSharedCheck_3712_; 
lean_dec(v_a_3610_);
lean_del_object(v___x_3605_);
lean_dec(v_snd_3603_);
lean_dec(v_fst_3602_);
lean_dec(v_a_3595_);
lean_dec(v_a_3592_);
lean_dec_ref(v___x_3584_);
lean_dec(v___x_3580_);
lean_del_object(v___x_3578_);
lean_dec(v_name_3575_);
lean_dec(v_fst_3558_);
v_a_3705_ = lean_ctor_get(v___x_3611_, 0);
v_isSharedCheck_3712_ = !lean_is_exclusive(v___x_3611_);
if (v_isSharedCheck_3712_ == 0)
{
v___x_3707_ = v___x_3611_;
v_isShared_3708_ = v_isSharedCheck_3712_;
goto v_resetjp_3706_;
}
else
{
lean_inc(v_a_3705_);
lean_dec(v___x_3611_);
v___x_3707_ = lean_box(0);
v_isShared_3708_ = v_isSharedCheck_3712_;
goto v_resetjp_3706_;
}
v_resetjp_3706_:
{
lean_object* v___x_3710_; 
if (v_isShared_3708_ == 0)
{
v___x_3710_ = v___x_3707_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v_a_3705_);
v___x_3710_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
return v___x_3710_;
}
}
}
}
else
{
lean_object* v_a_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3720_; 
lean_del_object(v___x_3605_);
lean_dec(v_snd_3603_);
lean_dec(v_fst_3602_);
lean_dec(v_a_3595_);
lean_dec(v_a_3592_);
lean_dec(v_a_3590_);
lean_dec_ref(v___x_3584_);
lean_dec(v___x_3580_);
lean_del_object(v___x_3578_);
lean_dec(v_name_3575_);
lean_dec(v_fst_3558_);
v_a_3713_ = lean_ctor_get(v___x_3609_, 0);
v_isSharedCheck_3720_ = !lean_is_exclusive(v___x_3609_);
if (v_isSharedCheck_3720_ == 0)
{
v___x_3715_ = v___x_3609_;
v_isShared_3716_ = v_isSharedCheck_3720_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_a_3713_);
lean_dec(v___x_3609_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3720_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v___x_3718_; 
if (v_isShared_3716_ == 0)
{
v___x_3718_ = v___x_3715_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v_a_3713_);
v___x_3718_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
return v___x_3718_;
}
}
}
}
else
{
lean_object* v_a_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3728_; 
lean_del_object(v___x_3605_);
lean_dec(v_snd_3603_);
lean_dec(v_fst_3602_);
lean_dec(v_a_3595_);
lean_dec(v_a_3592_);
lean_dec(v_a_3590_);
lean_dec_ref(v___x_3584_);
lean_dec(v___x_3580_);
lean_del_object(v___x_3578_);
lean_dec(v_name_3575_);
lean_dec(v_fst_3558_);
v_a_3721_ = lean_ctor_get(v___x_3607_, 0);
v_isSharedCheck_3728_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3723_ = v___x_3607_;
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_a_3721_);
lean_dec(v___x_3607_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v___x_3726_; 
if (v_isShared_3724_ == 0)
{
v___x_3726_ = v___x_3723_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_a_3721_);
v___x_3726_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
return v___x_3726_;
}
}
}
}
}
else
{
lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3737_; 
lean_dec(v_a_3595_);
lean_dec(v_a_3592_);
lean_dec(v_a_3590_);
lean_dec_ref(v___x_3584_);
lean_dec(v___x_3580_);
lean_del_object(v___x_3578_);
lean_dec(v_name_3575_);
lean_dec(v_fst_3558_);
v_a_3730_ = lean_ctor_get(v___x_3599_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3732_ = v___x_3599_;
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
lean_dec(v___x_3599_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v___x_3735_; 
if (v_isShared_3733_ == 0)
{
v___x_3735_ = v___x_3732_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_a_3730_);
v___x_3735_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
return v___x_3735_;
}
}
}
}
else
{
lean_object* v_a_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3745_; 
lean_dec(v_a_3592_);
lean_dec(v_a_3590_);
lean_dec_ref(v___x_3584_);
lean_dec(v___x_3580_);
lean_del_object(v___x_3578_);
lean_dec(v_levelParams_3576_);
lean_dec(v_name_3575_);
lean_dec(v_fst_3558_);
v_a_3738_ = lean_ctor_get(v___x_3594_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v___x_3594_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3740_ = v___x_3594_;
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
else
{
lean_inc(v_a_3738_);
lean_dec(v___x_3594_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
lean_object* v___x_3743_; 
if (v_isShared_3741_ == 0)
{
v___x_3743_ = v___x_3740_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_a_3738_);
v___x_3743_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
return v___x_3743_;
}
}
}
}
else
{
lean_object* v_a_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3753_; 
lean_dec(v_a_3590_);
lean_dec_ref(v___x_3584_);
lean_dec(v___x_3580_);
lean_del_object(v___x_3578_);
lean_dec(v_levelParams_3576_);
lean_dec(v_name_3575_);
lean_dec(v_fst_3558_);
v_a_3746_ = lean_ctor_get(v___x_3591_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3591_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3748_ = v___x_3591_;
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_a_3746_);
lean_dec(v___x_3591_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3751_; 
if (v_isShared_3749_ == 0)
{
v___x_3751_ = v___x_3748_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_a_3746_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
}
}
else
{
lean_object* v_a_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3761_; 
lean_dec_ref(v___x_3584_);
lean_dec(v___x_3580_);
lean_del_object(v___x_3578_);
lean_dec(v_levelParams_3576_);
lean_dec(v_name_3575_);
lean_dec(v_fst_3558_);
v_a_3754_ = lean_ctor_get(v___x_3589_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3589_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3756_ = v___x_3589_;
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_a_3754_);
lean_dec(v___x_3589_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v___x_3759_; 
if (v_isShared_3757_ == 0)
{
v___x_3759_ = v___x_3756_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_a_3754_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
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
v___jp_3550_:
{
size_t v___x_3552_; size_t v___x_3553_; 
v___x_3552_ = ((size_t)1ULL);
v___x_3553_ = lean_usize_add(v_i_3541_, v___x_3552_);
v_i_3541_ = v___x_3553_;
v_b_3542_ = v_a_3551_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___boxed(lean_object* v_typeNames_3770_, lean_object* v_as_3771_, lean_object* v_sz_3772_, lean_object* v_i_3773_, lean_object* v_b_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_){
_start:
{
size_t v_sz_boxed_3782_; size_t v_i_boxed_3783_; lean_object* v_res_3784_; 
v_sz_boxed_3782_ = lean_unbox_usize(v_sz_3772_);
lean_dec(v_sz_3772_);
v_i_boxed_3783_ = lean_unbox_usize(v_i_3773_);
lean_dec(v_i_3773_);
v_res_3784_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3(v_typeNames_3770_, v_as_3771_, v_sz_boxed_3782_, v_i_boxed_3783_, v_b_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_);
lean_dec(v___y_3780_);
lean_dec_ref(v___y_3779_);
lean_dec(v___y_3778_);
lean_dec_ref(v___y_3777_);
lean_dec(v___y_3776_);
lean_dec_ref(v___y_3775_);
lean_dec_ref(v_as_3771_);
lean_dec_ref(v_typeNames_3770_);
return v_res_3784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds(lean_object* v_ctx_3785_, lean_object* v_typeNames_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_){
_start:
{
lean_object* v_typeInfos_3794_; lean_object* v_auxFunNames_3795_; lean_object* v___x_3796_; lean_object* v_instances_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; size_t v_sz_3801_; size_t v___x_3802_; lean_object* v___x_3803_; 
v_typeInfos_3794_ = lean_ctor_get(v_ctx_3785_, 1);
lean_inc_ref(v_typeInfos_3794_);
v_auxFunNames_3795_ = lean_ctor_get(v_ctx_3785_, 2);
lean_inc_ref(v_auxFunNames_3795_);
lean_dec_ref(v_ctx_3785_);
v___x_3796_ = lean_unsigned_to_nat(0u);
v_instances_3797_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__0));
v___x_3798_ = lean_array_get_size(v_auxFunNames_3795_);
v___x_3799_ = l_Array_toSubarray___redArg(v_auxFunNames_3795_, v___x_3796_, v___x_3798_);
v___x_3800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3800_, 0, v_instances_3797_);
lean_ctor_set(v___x_3800_, 1, v___x_3799_);
v_sz_3801_ = lean_array_size(v_typeInfos_3794_);
v___x_3802_ = ((size_t)0ULL);
v___x_3803_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3(v_typeNames_3786_, v_typeInfos_3794_, v_sz_3801_, v___x_3802_, v___x_3800_, v_a_3787_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_, v_a_3792_);
lean_dec_ref(v_typeInfos_3794_);
if (lean_obj_tag(v___x_3803_) == 0)
{
lean_object* v_a_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3812_; 
v_a_3804_ = lean_ctor_get(v___x_3803_, 0);
v_isSharedCheck_3812_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3812_ == 0)
{
v___x_3806_ = v___x_3803_;
v_isShared_3807_ = v_isSharedCheck_3812_;
goto v_resetjp_3805_;
}
else
{
lean_inc(v_a_3804_);
lean_dec(v___x_3803_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3812_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
lean_object* v_fst_3808_; lean_object* v___x_3810_; 
v_fst_3808_ = lean_ctor_get(v_a_3804_, 0);
lean_inc(v_fst_3808_);
lean_dec(v_a_3804_);
if (v_isShared_3807_ == 0)
{
lean_ctor_set(v___x_3806_, 0, v_fst_3808_);
v___x_3810_ = v___x_3806_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v_fst_3808_);
v___x_3810_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
return v___x_3810_;
}
}
}
else
{
lean_object* v_a_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3820_; 
v_a_3813_ = lean_ctor_get(v___x_3803_, 0);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3815_ = v___x_3803_;
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_a_3813_);
lean_dec(v___x_3803_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v___x_3818_; 
if (v_isShared_3816_ == 0)
{
v___x_3818_ = v___x_3815_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_a_3813_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds___boxed(lean_object* v_ctx_3821_, lean_object* v_typeNames_3822_, lean_object* v_a_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_, lean_object* v_a_3828_, lean_object* v_a_3829_){
_start:
{
lean_object* v_res_3830_; 
v_res_3830_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds(v_ctx_3821_, v_typeNames_3822_, v_a_3823_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_);
lean_dec(v_a_3828_);
lean_dec_ref(v_a_3827_);
lean_dec(v_a_3826_);
lean_dec_ref(v_a_3825_);
lean_dec(v_a_3824_);
lean_dec_ref(v_a_3823_);
lean_dec_ref(v_typeNames_3822_);
return v_res_3830_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1(size_t v_sz_3831_, size_t v_i_3832_, lean_object* v_bs_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_){
_start:
{
lean_object* v___x_3841_; 
v___x_3841_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg(v_sz_3831_, v_i_3832_, v_bs_3833_, v___y_3838_, v___y_3839_);
return v___x_3841_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___boxed(lean_object* v_sz_3842_, lean_object* v_i_3843_, lean_object* v_bs_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_){
_start:
{
size_t v_sz_boxed_3852_; size_t v_i_boxed_3853_; lean_object* v_res_3854_; 
v_sz_boxed_3852_ = lean_unbox_usize(v_sz_3842_);
lean_dec(v_sz_3842_);
v_i_boxed_3853_ = lean_unbox_usize(v_i_3843_);
lean_dec(v_i_3843_);
v_res_3854_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1(v_sz_boxed_3852_, v_i_boxed_3853_, v_bs_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_);
lean_dec(v___y_3850_);
lean_dec_ref(v___y_3849_);
lean_dec(v___y_3848_);
lean_dec_ref(v___y_3847_);
lean_dec(v___y_3846_);
lean_dec_ref(v___y_3845_);
return v_res_3854_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__0(lean_object* v_a_3855_, lean_object* v_a_3856_){
_start:
{
if (lean_obj_tag(v_a_3855_) == 0)
{
lean_object* v___x_3857_; 
v___x_3857_ = l_List_reverse___redArg(v_a_3856_);
return v___x_3857_;
}
else
{
lean_object* v_head_3858_; lean_object* v_tail_3859_; lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3868_; 
v_head_3858_ = lean_ctor_get(v_a_3855_, 0);
v_tail_3859_ = lean_ctor_get(v_a_3855_, 1);
v_isSharedCheck_3868_ = !lean_is_exclusive(v_a_3855_);
if (v_isSharedCheck_3868_ == 0)
{
v___x_3861_ = v_a_3855_;
v_isShared_3862_ = v_isSharedCheck_3868_;
goto v_resetjp_3860_;
}
else
{
lean_inc(v_tail_3859_);
lean_inc(v_head_3858_);
lean_dec(v_a_3855_);
v___x_3861_ = lean_box(0);
v_isShared_3862_ = v_isSharedCheck_3868_;
goto v_resetjp_3860_;
}
v_resetjp_3860_:
{
lean_object* v___x_3863_; lean_object* v___x_3865_; 
v___x_3863_ = l_Lean_MessageData_ofSyntax(v_head_3858_);
if (v_isShared_3862_ == 0)
{
lean_ctor_set(v___x_3861_, 1, v_a_3856_);
lean_ctor_set(v___x_3861_, 0, v___x_3863_);
v___x_3865_ = v___x_3861_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v___x_3863_);
lean_ctor_set(v_reuseFailAlloc_3867_, 1, v_a_3856_);
v___x_3865_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
v_a_3855_ = v_tail_3859_;
v_a_3856_ = v___x_3865_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3869_; double v___x_3870_; 
v___x_3869_ = lean_unsigned_to_nat(0u);
v___x_3870_ = lean_float_of_nat(v___x_3869_);
return v___x_3870_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg(lean_object* v_cls_3874_, lean_object* v_msg_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_){
_start:
{
lean_object* v_ref_3881_; lean_object* v___x_3882_; lean_object* v_a_3883_; lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3927_; 
v_ref_3881_ = lean_ctor_get(v___y_3878_, 5);
v___x_3882_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__0(v_msg_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_);
v_a_3883_ = lean_ctor_get(v___x_3882_, 0);
v_isSharedCheck_3927_ = !lean_is_exclusive(v___x_3882_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3885_ = v___x_3882_;
v_isShared_3886_ = v_isSharedCheck_3927_;
goto v_resetjp_3884_;
}
else
{
lean_inc(v_a_3883_);
lean_dec(v___x_3882_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3927_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v___x_3887_; lean_object* v_traceState_3888_; lean_object* v_env_3889_; lean_object* v_nextMacroScope_3890_; lean_object* v_ngen_3891_; lean_object* v_auxDeclNGen_3892_; lean_object* v_cache_3893_; lean_object* v_messages_3894_; lean_object* v_infoState_3895_; lean_object* v_snapshotTasks_3896_; lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_3926_; 
v___x_3887_ = lean_st_ref_take(v___y_3879_);
v_traceState_3888_ = lean_ctor_get(v___x_3887_, 4);
v_env_3889_ = lean_ctor_get(v___x_3887_, 0);
v_nextMacroScope_3890_ = lean_ctor_get(v___x_3887_, 1);
v_ngen_3891_ = lean_ctor_get(v___x_3887_, 2);
v_auxDeclNGen_3892_ = lean_ctor_get(v___x_3887_, 3);
v_cache_3893_ = lean_ctor_get(v___x_3887_, 5);
v_messages_3894_ = lean_ctor_get(v___x_3887_, 6);
v_infoState_3895_ = lean_ctor_get(v___x_3887_, 7);
v_snapshotTasks_3896_ = lean_ctor_get(v___x_3887_, 8);
v_isSharedCheck_3926_ = !lean_is_exclusive(v___x_3887_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3898_ = v___x_3887_;
v_isShared_3899_ = v_isSharedCheck_3926_;
goto v_resetjp_3897_;
}
else
{
lean_inc(v_snapshotTasks_3896_);
lean_inc(v_infoState_3895_);
lean_inc(v_messages_3894_);
lean_inc(v_cache_3893_);
lean_inc(v_traceState_3888_);
lean_inc(v_auxDeclNGen_3892_);
lean_inc(v_ngen_3891_);
lean_inc(v_nextMacroScope_3890_);
lean_inc(v_env_3889_);
lean_dec(v___x_3887_);
v___x_3898_ = lean_box(0);
v_isShared_3899_ = v_isSharedCheck_3926_;
goto v_resetjp_3897_;
}
v_resetjp_3897_:
{
uint64_t v_tid_3900_; lean_object* v_traces_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3925_; 
v_tid_3900_ = lean_ctor_get_uint64(v_traceState_3888_, sizeof(void*)*1);
v_traces_3901_ = lean_ctor_get(v_traceState_3888_, 0);
v_isSharedCheck_3925_ = !lean_is_exclusive(v_traceState_3888_);
if (v_isSharedCheck_3925_ == 0)
{
v___x_3903_ = v_traceState_3888_;
v_isShared_3904_ = v_isSharedCheck_3925_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_traces_3901_);
lean_dec(v_traceState_3888_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3925_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3905_; double v___x_3906_; uint8_t v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3915_; 
v___x_3905_ = lean_box(0);
v___x_3906_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg___closed__0);
v___x_3907_ = 0;
v___x_3908_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg___closed__1));
v___x_3909_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3909_, 0, v_cls_3874_);
lean_ctor_set(v___x_3909_, 1, v___x_3905_);
lean_ctor_set(v___x_3909_, 2, v___x_3908_);
lean_ctor_set_float(v___x_3909_, sizeof(void*)*3, v___x_3906_);
lean_ctor_set_float(v___x_3909_, sizeof(void*)*3 + 8, v___x_3906_);
lean_ctor_set_uint8(v___x_3909_, sizeof(void*)*3 + 16, v___x_3907_);
v___x_3910_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg___closed__2));
v___x_3911_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3911_, 0, v___x_3909_);
lean_ctor_set(v___x_3911_, 1, v_a_3883_);
lean_ctor_set(v___x_3911_, 2, v___x_3910_);
lean_inc(v_ref_3881_);
v___x_3912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3912_, 0, v_ref_3881_);
lean_ctor_set(v___x_3912_, 1, v___x_3911_);
v___x_3913_ = l_Lean_PersistentArray_push___redArg(v_traces_3901_, v___x_3912_);
if (v_isShared_3904_ == 0)
{
lean_ctor_set(v___x_3903_, 0, v___x_3913_);
v___x_3915_ = v___x_3903_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v___x_3913_);
lean_ctor_set_uint64(v_reuseFailAlloc_3924_, sizeof(void*)*1, v_tid_3900_);
v___x_3915_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
lean_object* v___x_3917_; 
if (v_isShared_3899_ == 0)
{
lean_ctor_set(v___x_3898_, 4, v___x_3915_);
v___x_3917_ = v___x_3898_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_env_3889_);
lean_ctor_set(v_reuseFailAlloc_3923_, 1, v_nextMacroScope_3890_);
lean_ctor_set(v_reuseFailAlloc_3923_, 2, v_ngen_3891_);
lean_ctor_set(v_reuseFailAlloc_3923_, 3, v_auxDeclNGen_3892_);
lean_ctor_set(v_reuseFailAlloc_3923_, 4, v___x_3915_);
lean_ctor_set(v_reuseFailAlloc_3923_, 5, v_cache_3893_);
lean_ctor_set(v_reuseFailAlloc_3923_, 6, v_messages_3894_);
lean_ctor_set(v_reuseFailAlloc_3923_, 7, v_infoState_3895_);
lean_ctor_set(v_reuseFailAlloc_3923_, 8, v_snapshotTasks_3896_);
v___x_3917_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3921_; 
v___x_3918_ = lean_st_ref_set(v___y_3879_, v___x_3917_);
v___x_3919_ = lean_box(0);
if (v_isShared_3886_ == 0)
{
lean_ctor_set(v___x_3885_, 0, v___x_3919_);
v___x_3921_ = v___x_3885_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v___x_3919_);
v___x_3921_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
return v___x_3921_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg___boxed(lean_object* v_cls_3928_, lean_object* v_msg_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_){
_start:
{
lean_object* v_res_3935_; 
v_res_3935_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg(v_cls_3928_, v_msg_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_);
lean_dec(v___y_3933_);
lean_dec_ref(v___y_3932_);
lean_dec(v___y_3931_);
lean_dec_ref(v___y_3930_);
return v_res_3935_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__3(void){
_start:
{
lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; 
v___x_3943_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__0));
v___x_3944_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__2));
v___x_3945_ = l_Lean_Name_append(v___x_3944_, v___x_3943_);
return v___x_3945_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__5(void){
_start:
{
lean_object* v___x_3947_; lean_object* v___x_3948_; 
v___x_3947_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__4));
v___x_3948_ = l_Lean_stringToMessageData(v___x_3947_);
return v___x_3948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds(lean_object* v_declNames_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_){
_start:
{
lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; uint8_t v___x_3962_; lean_object* v___x_3963_; 
v___x_3957_ = lean_box(0);
v___x_3958_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__14));
v___x_3959_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__0));
v___x_3960_ = lean_unsigned_to_nat(0u);
v___x_3961_ = lean_array_get_borrowed(v___x_3957_, v_declNames_3949_, v___x_3960_);
v___x_3962_ = 1;
lean_inc(v___x_3961_);
v___x_3963_ = l_Lean_Elab_Deriving_mkContext(v___x_3958_, v___x_3959_, v___x_3961_, v___x_3962_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_);
if (lean_obj_tag(v___x_3963_) == 0)
{
lean_object* v_a_3964_; lean_object* v___x_3965_; 
v_a_3964_ = lean_ctor_get(v___x_3963_, 0);
lean_inc_n(v_a_3964_, 2);
lean_dec_ref_known(v___x_3963_, 1);
v___x_3965_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions(v_a_3964_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_);
if (lean_obj_tag(v___x_3965_) == 0)
{
lean_object* v_a_3966_; lean_object* v___x_3967_; 
v_a_3966_ = lean_ctor_get(v___x_3965_, 0);
lean_inc(v_a_3966_);
lean_dec_ref_known(v___x_3965_, 1);
v___x_3967_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds(v_a_3964_, v_declNames_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_);
if (lean_obj_tag(v___x_3967_) == 0)
{
lean_object* v_options_3968_; lean_object* v_a_3969_; lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_4011_; 
v_options_3968_ = lean_ctor_get(v_a_3954_, 2);
v_a_3969_ = lean_ctor_get(v___x_3967_, 0);
v_isSharedCheck_4011_ = !lean_is_exclusive(v___x_3967_);
if (v_isSharedCheck_4011_ == 0)
{
v___x_3971_ = v___x_3967_;
v_isShared_3972_ = v_isSharedCheck_4011_;
goto v_resetjp_3970_;
}
else
{
lean_inc(v_a_3969_);
lean_dec(v___x_3967_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_4011_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
lean_object* v_inheritedTraceOptions_3973_; uint8_t v_hasTrace_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; 
v_inheritedTraceOptions_3973_ = lean_ctor_get(v_a_3954_, 13);
v_hasTrace_3974_ = lean_ctor_get_uint8(v_options_3968_, sizeof(void*)*1);
v___x_3975_ = lean_unsigned_to_nat(1u);
v___x_3976_ = lean_mk_empty_array_with_capacity(v___x_3975_);
v___x_3977_ = lean_array_push(v___x_3976_, v_a_3966_);
v___x_3978_ = l_Array_append___redArg(v___x_3977_, v_a_3969_);
lean_dec(v_a_3969_);
if (v_hasTrace_3974_ == 0)
{
lean_object* v___x_3980_; 
if (v_isShared_3972_ == 0)
{
lean_ctor_set(v___x_3971_, 0, v___x_3978_);
v___x_3980_ = v___x_3971_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v___x_3978_);
v___x_3980_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
return v___x_3980_;
}
}
else
{
lean_object* v___x_3982_; lean_object* v___x_3983_; uint8_t v___x_3984_; 
v___x_3982_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__0));
v___x_3983_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__3, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__3_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__3);
v___x_3984_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3973_, v_options_3968_, v___x_3983_);
if (v___x_3984_ == 0)
{
lean_object* v___x_3986_; 
if (v_isShared_3972_ == 0)
{
lean_ctor_set(v___x_3971_, 0, v___x_3978_);
v___x_3986_ = v___x_3971_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v___x_3978_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
return v___x_3986_;
}
}
else
{
lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; 
lean_del_object(v___x_3971_);
v___x_3988_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__5, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__5_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__5);
lean_inc_ref(v___x_3978_);
v___x_3989_ = lean_array_to_list(v___x_3978_);
v___x_3990_ = lean_box(0);
v___x_3991_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__0(v___x_3989_, v___x_3990_);
v___x_3992_ = l_Lean_MessageData_ofList(v___x_3991_);
v___x_3993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3993_, 0, v___x_3988_);
lean_ctor_set(v___x_3993_, 1, v___x_3992_);
v___x_3994_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg(v___x_3982_, v___x_3993_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_);
if (lean_obj_tag(v___x_3994_) == 0)
{
lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4001_; 
v_isSharedCheck_4001_ = !lean_is_exclusive(v___x_3994_);
if (v_isSharedCheck_4001_ == 0)
{
lean_object* v_unused_4002_; 
v_unused_4002_ = lean_ctor_get(v___x_3994_, 0);
lean_dec(v_unused_4002_);
v___x_3996_ = v___x_3994_;
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
else
{
lean_dec(v___x_3994_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
lean_object* v___x_3999_; 
if (v_isShared_3997_ == 0)
{
lean_ctor_set(v___x_3996_, 0, v___x_3978_);
v___x_3999_ = v___x_3996_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v___x_3978_);
v___x_3999_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
return v___x_3999_;
}
}
}
else
{
lean_object* v_a_4003_; lean_object* v___x_4005_; uint8_t v_isShared_4006_; uint8_t v_isSharedCheck_4010_; 
lean_dec_ref(v___x_3978_);
v_a_4003_ = lean_ctor_get(v___x_3994_, 0);
v_isSharedCheck_4010_ = !lean_is_exclusive(v___x_3994_);
if (v_isSharedCheck_4010_ == 0)
{
v___x_4005_ = v___x_3994_;
v_isShared_4006_ = v_isSharedCheck_4010_;
goto v_resetjp_4004_;
}
else
{
lean_inc(v_a_4003_);
lean_dec(v___x_3994_);
v___x_4005_ = lean_box(0);
v_isShared_4006_ = v_isSharedCheck_4010_;
goto v_resetjp_4004_;
}
v_resetjp_4004_:
{
lean_object* v___x_4008_; 
if (v_isShared_4006_ == 0)
{
v___x_4008_ = v___x_4005_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v_a_4003_);
v___x_4008_ = v_reuseFailAlloc_4009_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
return v___x_4008_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4012_; lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4019_; 
lean_dec(v_a_3966_);
v_a_4012_ = lean_ctor_get(v___x_3967_, 0);
v_isSharedCheck_4019_ = !lean_is_exclusive(v___x_3967_);
if (v_isSharedCheck_4019_ == 0)
{
v___x_4014_ = v___x_3967_;
v_isShared_4015_ = v_isSharedCheck_4019_;
goto v_resetjp_4013_;
}
else
{
lean_inc(v_a_4012_);
lean_dec(v___x_3967_);
v___x_4014_ = lean_box(0);
v_isShared_4015_ = v_isSharedCheck_4019_;
goto v_resetjp_4013_;
}
v_resetjp_4013_:
{
lean_object* v___x_4017_; 
if (v_isShared_4015_ == 0)
{
v___x_4017_ = v___x_4014_;
goto v_reusejp_4016_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_a_4012_);
v___x_4017_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4016_;
}
v_reusejp_4016_:
{
return v___x_4017_;
}
}
}
}
else
{
lean_object* v_a_4020_; lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4027_; 
lean_dec(v_a_3964_);
v_a_4020_ = lean_ctor_get(v___x_3965_, 0);
v_isSharedCheck_4027_ = !lean_is_exclusive(v___x_3965_);
if (v_isSharedCheck_4027_ == 0)
{
v___x_4022_ = v___x_3965_;
v_isShared_4023_ = v_isSharedCheck_4027_;
goto v_resetjp_4021_;
}
else
{
lean_inc(v_a_4020_);
lean_dec(v___x_3965_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4027_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
lean_object* v___x_4025_; 
if (v_isShared_4023_ == 0)
{
v___x_4025_ = v___x_4022_;
goto v_reusejp_4024_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v_a_4020_);
v___x_4025_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4024_;
}
v_reusejp_4024_:
{
return v___x_4025_;
}
}
}
}
else
{
lean_object* v_a_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4035_; 
v_a_4028_ = lean_ctor_get(v___x_3963_, 0);
v_isSharedCheck_4035_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_4035_ == 0)
{
v___x_4030_ = v___x_3963_;
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_a_4028_);
lean_dec(v___x_3963_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v___x_4033_; 
if (v_isShared_4031_ == 0)
{
v___x_4033_ = v___x_4030_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v_a_4028_);
v___x_4033_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
return v___x_4033_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___boxed(lean_object* v_declNames_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_){
_start:
{
lean_object* v_res_4044_; 
v_res_4044_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds(v_declNames_4036_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_);
lean_dec(v_a_4042_);
lean_dec_ref(v_a_4041_);
lean_dec(v_a_4040_);
lean_dec_ref(v_a_4039_);
lean_dec(v_a_4038_);
lean_dec_ref(v_a_4037_);
lean_dec_ref(v_declNames_4036_);
return v_res_4044_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1(lean_object* v_cls_4045_, lean_object* v_msg_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_){
_start:
{
lean_object* v___x_4054_; 
v___x_4054_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg(v_cls_4045_, v_msg_4046_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_);
return v___x_4054_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___boxed(lean_object* v_cls_4055_, lean_object* v_msg_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_){
_start:
{
lean_object* v_res_4064_; 
v_res_4064_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1(v_cls_4055_, v_msg_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_);
lean_dec(v___y_4062_);
lean_dec_ref(v___y_4061_);
lean_dec(v___y_4060_);
lean_dec_ref(v___y_4059_);
lean_dec(v___y_4058_);
lean_dec_ref(v___y_4057_);
return v_res_4064_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0___redArg(lean_object* v_declName_4065_, lean_object* v___y_4066_){
_start:
{
lean_object* v___x_4068_; lean_object* v_env_4069_; uint8_t v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; 
v___x_4068_ = lean_st_ref_get(v___y_4066_);
v_env_4069_ = lean_ctor_get(v___x_4068_, 0);
lean_inc_ref(v_env_4069_);
lean_dec(v___x_4068_);
v___x_4070_ = l_Lean_isInductiveCore(v_env_4069_, v_declName_4065_);
v___x_4071_ = lean_box(v___x_4070_);
v___x_4072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4072_, 0, v___x_4071_);
return v___x_4072_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0___redArg___boxed(lean_object* v_declName_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_){
_start:
{
lean_object* v_res_4076_; 
v_res_4076_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0___redArg(v_declName_4073_, v___y_4074_);
lean_dec(v___y_4074_);
return v_res_4076_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0(lean_object* v_declName_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_){
_start:
{
lean_object* v___x_4081_; 
v___x_4081_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0___redArg(v_declName_4077_, v___y_4079_);
return v___x_4081_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0___boxed(lean_object* v_declName_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_){
_start:
{
lean_object* v_res_4086_; 
v_res_4086_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0(v_declName_4082_, v___y_4083_, v___y_4084_);
lean_dec(v___y_4084_);
lean_dec_ref(v___y_4083_);
return v_res_4086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__0(uint8_t v_____do__lift_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_){
_start:
{
uint8_t v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; 
v___x_4091_ = lean_bool_not(v_____do__lift_4087_);
v___x_4092_ = lean_box(v___x_4091_);
v___x_4093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4093_, 0, v___x_4092_);
return v___x_4093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__0___boxed(lean_object* v_____do__lift_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_){
_start:
{
uint8_t v_____do__lift_1541__boxed_4098_; lean_object* v_res_4099_; 
v_____do__lift_1541__boxed_4098_ = lean_unbox(v_____do__lift_4094_);
v_res_4099_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__0(v_____do__lift_1541__boxed_4098_, v___y_4095_, v___y_4096_);
lean_dec(v___y_4096_);
lean_dec_ref(v___y_4095_);
return v_res_4099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1_spec__1(lean_object* v_o_4100_, lean_object* v_k_4101_, uint8_t v_v_4102_){
_start:
{
lean_object* v_map_4103_; uint8_t v_hasTrace_4104_; lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4118_; 
v_map_4103_ = lean_ctor_get(v_o_4100_, 0);
v_hasTrace_4104_ = lean_ctor_get_uint8(v_o_4100_, sizeof(void*)*1);
v_isSharedCheck_4118_ = !lean_is_exclusive(v_o_4100_);
if (v_isSharedCheck_4118_ == 0)
{
v___x_4106_ = v_o_4100_;
v_isShared_4107_ = v_isSharedCheck_4118_;
goto v_resetjp_4105_;
}
else
{
lean_inc(v_map_4103_);
lean_dec(v_o_4100_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4118_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
lean_object* v___x_4108_; lean_object* v___x_4109_; 
v___x_4108_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4108_, 0, v_v_4102_);
lean_inc(v_k_4101_);
v___x_4109_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4101_, v___x_4108_, v_map_4103_);
if (v_hasTrace_4104_ == 0)
{
lean_object* v___x_4110_; uint8_t v___x_4111_; lean_object* v___x_4113_; 
v___x_4110_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__2));
v___x_4111_ = l_Lean_Name_isPrefixOf(v___x_4110_, v_k_4101_);
lean_dec(v_k_4101_);
if (v_isShared_4107_ == 0)
{
lean_ctor_set(v___x_4106_, 0, v___x_4109_);
v___x_4113_ = v___x_4106_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v___x_4109_);
v___x_4113_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
lean_ctor_set_uint8(v___x_4113_, sizeof(void*)*1, v___x_4111_);
return v___x_4113_;
}
}
else
{
lean_object* v___x_4116_; 
lean_dec(v_k_4101_);
if (v_isShared_4107_ == 0)
{
lean_ctor_set(v___x_4106_, 0, v___x_4109_);
v___x_4116_ = v___x_4106_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v___x_4109_);
lean_ctor_set_uint8(v_reuseFailAlloc_4117_, sizeof(void*)*1, v_hasTrace_4104_);
v___x_4116_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
return v___x_4116_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1_spec__1___boxed(lean_object* v_o_4119_, lean_object* v_k_4120_, lean_object* v_v_4121_){
_start:
{
uint8_t v_v_boxed_4122_; lean_object* v_res_4123_; 
v_v_boxed_4122_ = lean_unbox(v_v_4121_);
v_res_4123_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1_spec__1(v_o_4119_, v_k_4120_, v_v_boxed_4122_);
return v_res_4123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1(lean_object* v_opts_4124_, lean_object* v_opt_4125_, uint8_t v_val_4126_){
_start:
{
lean_object* v_name_4127_; lean_object* v___x_4128_; 
v_name_4127_ = lean_ctor_get(v_opt_4125_, 0);
lean_inc(v_name_4127_);
lean_dec_ref(v_opt_4125_);
v___x_4128_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1_spec__1(v_opts_4124_, v_name_4127_, v_val_4126_);
return v___x_4128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1___boxed(lean_object* v_opts_4129_, lean_object* v_opt_4130_, lean_object* v_val_4131_){
_start:
{
uint8_t v_val_boxed_4132_; lean_object* v_res_4133_; 
v_val_boxed_4132_ = lean_unbox(v_val_4131_);
v_res_4133_ = l_Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1(v_opts_4129_, v_opt_4130_, v_val_boxed_4132_);
return v_res_4133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__1(uint8_t v_a_4134_, lean_object* v_scope_4135_){
_start:
{
lean_object* v_header_4136_; lean_object* v_opts_4137_; lean_object* v_currNamespace_4138_; lean_object* v_openDecls_4139_; lean_object* v_levelNames_4140_; lean_object* v_varDecls_4141_; lean_object* v_varUIds_4142_; lean_object* v_includedVars_4143_; lean_object* v_omittedVars_4144_; uint8_t v_isNoncomputable_4145_; uint8_t v_isPublic_4146_; uint8_t v_isMeta_4147_; lean_object* v_attrs_4148_; lean_object* v___x_4150_; uint8_t v_isShared_4151_; uint8_t v_isSharedCheck_4157_; 
v_header_4136_ = lean_ctor_get(v_scope_4135_, 0);
v_opts_4137_ = lean_ctor_get(v_scope_4135_, 1);
v_currNamespace_4138_ = lean_ctor_get(v_scope_4135_, 2);
v_openDecls_4139_ = lean_ctor_get(v_scope_4135_, 3);
v_levelNames_4140_ = lean_ctor_get(v_scope_4135_, 4);
v_varDecls_4141_ = lean_ctor_get(v_scope_4135_, 5);
v_varUIds_4142_ = lean_ctor_get(v_scope_4135_, 6);
v_includedVars_4143_ = lean_ctor_get(v_scope_4135_, 7);
v_omittedVars_4144_ = lean_ctor_get(v_scope_4135_, 8);
v_isNoncomputable_4145_ = lean_ctor_get_uint8(v_scope_4135_, sizeof(void*)*10);
v_isPublic_4146_ = lean_ctor_get_uint8(v_scope_4135_, sizeof(void*)*10 + 1);
v_isMeta_4147_ = lean_ctor_get_uint8(v_scope_4135_, sizeof(void*)*10 + 2);
v_attrs_4148_ = lean_ctor_get(v_scope_4135_, 9);
v_isSharedCheck_4157_ = !lean_is_exclusive(v_scope_4135_);
if (v_isSharedCheck_4157_ == 0)
{
v___x_4150_ = v_scope_4135_;
v_isShared_4151_ = v_isSharedCheck_4157_;
goto v_resetjp_4149_;
}
else
{
lean_inc(v_attrs_4148_);
lean_inc(v_omittedVars_4144_);
lean_inc(v_includedVars_4143_);
lean_inc(v_varUIds_4142_);
lean_inc(v_varDecls_4141_);
lean_inc(v_levelNames_4140_);
lean_inc(v_openDecls_4139_);
lean_inc(v_currNamespace_4138_);
lean_inc(v_opts_4137_);
lean_inc(v_header_4136_);
lean_dec(v_scope_4135_);
v___x_4150_ = lean_box(0);
v_isShared_4151_ = v_isSharedCheck_4157_;
goto v_resetjp_4149_;
}
v_resetjp_4149_:
{
lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4155_; 
v___x_4152_ = l_Lean_Elab_autoImplicit;
v___x_4153_ = l_Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1(v_opts_4137_, v___x_4152_, v_a_4134_);
if (v_isShared_4151_ == 0)
{
lean_ctor_set(v___x_4150_, 1, v___x_4153_);
v___x_4155_ = v___x_4150_;
goto v_reusejp_4154_;
}
else
{
lean_object* v_reuseFailAlloc_4156_; 
v_reuseFailAlloc_4156_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v_reuseFailAlloc_4156_, 0, v_header_4136_);
lean_ctor_set(v_reuseFailAlloc_4156_, 1, v___x_4153_);
lean_ctor_set(v_reuseFailAlloc_4156_, 2, v_currNamespace_4138_);
lean_ctor_set(v_reuseFailAlloc_4156_, 3, v_openDecls_4139_);
lean_ctor_set(v_reuseFailAlloc_4156_, 4, v_levelNames_4140_);
lean_ctor_set(v_reuseFailAlloc_4156_, 5, v_varDecls_4141_);
lean_ctor_set(v_reuseFailAlloc_4156_, 6, v_varUIds_4142_);
lean_ctor_set(v_reuseFailAlloc_4156_, 7, v_includedVars_4143_);
lean_ctor_set(v_reuseFailAlloc_4156_, 8, v_omittedVars_4144_);
lean_ctor_set(v_reuseFailAlloc_4156_, 9, v_attrs_4148_);
lean_ctor_set_uint8(v_reuseFailAlloc_4156_, sizeof(void*)*10, v_isNoncomputable_4145_);
lean_ctor_set_uint8(v_reuseFailAlloc_4156_, sizeof(void*)*10 + 1, v_isPublic_4146_);
lean_ctor_set_uint8(v_reuseFailAlloc_4156_, sizeof(void*)*10 + 2, v_isMeta_4147_);
v___x_4155_ = v_reuseFailAlloc_4156_;
goto v_reusejp_4154_;
}
v_reusejp_4154_:
{
return v___x_4155_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__1___boxed(lean_object* v_a_4158_, lean_object* v_scope_4159_){
_start:
{
uint8_t v_a_1593__boxed_4160_; lean_object* v_res_4161_; 
v_a_1593__boxed_4160_ = lean_unbox(v_a_4158_);
v_res_4161_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__1(v_a_1593__boxed_4160_, v_scope_4159_);
return v_res_4161_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__2(lean_object* v_as_4162_, size_t v_i_4163_, size_t v_stop_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_){
_start:
{
uint8_t v___x_4168_; 
v___x_4168_ = lean_usize_dec_eq(v_i_4163_, v_stop_4164_);
if (v___x_4168_ == 0)
{
uint8_t v___x_4169_; uint8_t v_a_4171_; lean_object* v___x_4177_; lean_object* v___x_4178_; 
v___x_4169_ = 1;
v___x_4177_ = lean_array_uget_borrowed(v_as_4162_, v_i_4163_);
lean_inc(v___x_4177_);
v___x_4178_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0___redArg(v___x_4177_, v___y_4166_);
if (lean_obj_tag(v___x_4178_) == 0)
{
lean_object* v_a_4179_; uint8_t v___x_4180_; uint8_t v___x_4181_; 
v_a_4179_ = lean_ctor_get(v___x_4178_, 0);
lean_inc(v_a_4179_);
lean_dec_ref_known(v___x_4178_, 1);
v___x_4180_ = lean_unbox(v_a_4179_);
lean_dec(v_a_4179_);
v___x_4181_ = lean_bool_not(v___x_4180_);
v_a_4171_ = v___x_4181_;
goto v___jp_4170_;
}
else
{
if (lean_obj_tag(v___x_4178_) == 0)
{
lean_object* v_a_4182_; uint8_t v___x_4183_; 
v_a_4182_ = lean_ctor_get(v___x_4178_, 0);
lean_inc(v_a_4182_);
lean_dec_ref_known(v___x_4178_, 1);
v___x_4183_ = lean_unbox(v_a_4182_);
lean_dec(v_a_4182_);
v_a_4171_ = v___x_4183_;
goto v___jp_4170_;
}
else
{
return v___x_4178_;
}
}
v___jp_4170_:
{
if (v_a_4171_ == 0)
{
size_t v___x_4172_; size_t v___x_4173_; 
v___x_4172_ = ((size_t)1ULL);
v___x_4173_ = lean_usize_add(v_i_4163_, v___x_4172_);
v_i_4163_ = v___x_4173_;
goto _start;
}
else
{
lean_object* v___x_4175_; lean_object* v___x_4176_; 
v___x_4175_ = lean_box(v___x_4169_);
v___x_4176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4176_, 0, v___x_4175_);
return v___x_4176_;
}
}
}
else
{
uint8_t v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; 
v___x_4184_ = 0;
v___x_4185_ = lean_box(v___x_4184_);
v___x_4186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4186_, 0, v___x_4185_);
return v___x_4186_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__2___boxed(lean_object* v_as_4187_, lean_object* v_i_4188_, lean_object* v_stop_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_){
_start:
{
size_t v_i_boxed_4193_; size_t v_stop_boxed_4194_; lean_object* v_res_4195_; 
v_i_boxed_4193_ = lean_unbox_usize(v_i_4188_);
lean_dec(v_i_4188_);
v_stop_boxed_4194_ = lean_unbox_usize(v_stop_4189_);
lean_dec(v_stop_4189_);
v_res_4195_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__2(v_as_4187_, v_i_boxed_4193_, v_stop_boxed_4194_, v___y_4190_, v___y_4191_);
lean_dec(v___y_4191_);
lean_dec_ref(v___y_4190_);
lean_dec_ref(v_as_4187_);
return v_res_4195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler(lean_object* v_declNames_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_){
_start:
{
lean_object* v___x_4200_; lean_object* v___x_4201_; uint8_t v___x_4202_; uint8_t v_a_4204_; lean_object* v___y_4246_; 
v___x_4200_ = lean_unsigned_to_nat(0u);
v___x_4201_ = lean_array_get_size(v_declNames_4196_);
v___x_4202_ = lean_nat_dec_lt(v___x_4200_, v___x_4201_);
if (v___x_4202_ == 0)
{
lean_object* v___x_4249_; 
v___x_4249_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__0(v___x_4202_, v_a_4197_, v_a_4198_);
v___y_4246_ = v___x_4249_;
goto v___jp_4245_;
}
else
{
if (v___x_4202_ == 0)
{
uint8_t v___x_4250_; 
v___x_4250_ = lean_bool_not(v___x_4202_);
v_a_4204_ = v___x_4250_;
goto v___jp_4203_;
}
else
{
size_t v___x_4251_; size_t v___x_4252_; lean_object* v___x_4253_; 
v___x_4251_ = ((size_t)0ULL);
v___x_4252_ = lean_usize_of_nat(v___x_4201_);
v___x_4253_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__2(v_declNames_4196_, v___x_4251_, v___x_4252_, v_a_4197_, v_a_4198_);
if (lean_obj_tag(v___x_4253_) == 0)
{
lean_object* v_a_4254_; uint8_t v___x_4255_; lean_object* v___x_4256_; 
v_a_4254_ = lean_ctor_get(v___x_4253_, 0);
lean_inc(v_a_4254_);
lean_dec_ref_known(v___x_4253_, 1);
v___x_4255_ = lean_unbox(v_a_4254_);
lean_dec(v_a_4254_);
v___x_4256_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__0(v___x_4255_, v_a_4197_, v_a_4198_);
v___y_4246_ = v___x_4256_;
goto v___jp_4245_;
}
else
{
v___y_4246_ = v___x_4253_;
goto v___jp_4245_;
}
}
}
v___jp_4203_:
{
if (v_a_4204_ == 0)
{
lean_object* v___x_4205_; lean_object* v___x_4206_; 
lean_dec_ref(v_declNames_4196_);
v___x_4205_ = lean_box(v_a_4204_);
v___x_4206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4206_, 0, v___x_4205_);
return v___x_4206_;
}
else
{
if (v___x_4202_ == 0)
{
lean_object* v___x_4207_; lean_object* v___x_4208_; 
lean_dec_ref(v_declNames_4196_);
v___x_4207_ = lean_box(v___x_4202_);
v___x_4208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4208_, 0, v___x_4207_);
return v___x_4208_;
}
else
{
lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; 
v___x_4209_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___boxed), 8, 1);
lean_closure_set(v___x_4209_, 0, v_declNames_4196_);
v___x_4210_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftTermElabM___boxed), 5, 2);
lean_closure_set(v___x_4210_, 0, lean_box(0));
lean_closure_set(v___x_4210_, 1, v___x_4209_);
v___x_4211_ = l_Lean_Elab_Command_withFreshMacroScope___redArg(v___x_4210_, v_a_4197_, v_a_4198_);
if (lean_obj_tag(v___x_4211_) == 0)
{
lean_object* v_a_4212_; lean_object* v___x_4213_; lean_object* v___f_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; 
v_a_4212_ = lean_ctor_get(v___x_4211_, 0);
lean_inc(v_a_4212_);
lean_dec_ref_known(v___x_4211_, 1);
v___x_4213_ = lean_box(v_a_4204_);
v___f_4214_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__1___boxed), 2, 1);
lean_closure_set(v___f_4214_, 0, v___x_4213_);
v___x_4215_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_4216_ = lean_box(2);
v___x_4217_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4217_, 0, v___x_4216_);
lean_ctor_set(v___x_4217_, 1, v___x_4215_);
lean_ctor_set(v___x_4217_, 2, v_a_4212_);
v___x_4218_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(v___x_4218_, 0, v___x_4217_);
v___x_4219_ = l_Lean_Elab_Command_withScope___redArg(v___f_4214_, v___x_4218_, v_a_4197_, v_a_4198_);
if (lean_obj_tag(v___x_4219_) == 0)
{
lean_object* v___x_4221_; uint8_t v_isShared_4222_; uint8_t v_isSharedCheck_4227_; 
v_isSharedCheck_4227_ = !lean_is_exclusive(v___x_4219_);
if (v_isSharedCheck_4227_ == 0)
{
lean_object* v_unused_4228_; 
v_unused_4228_ = lean_ctor_get(v___x_4219_, 0);
lean_dec(v_unused_4228_);
v___x_4221_ = v___x_4219_;
v_isShared_4222_ = v_isSharedCheck_4227_;
goto v_resetjp_4220_;
}
else
{
lean_dec(v___x_4219_);
v___x_4221_ = lean_box(0);
v_isShared_4222_ = v_isSharedCheck_4227_;
goto v_resetjp_4220_;
}
v_resetjp_4220_:
{
lean_object* v___x_4223_; lean_object* v___x_4225_; 
v___x_4223_ = lean_box(v_a_4204_);
if (v_isShared_4222_ == 0)
{
lean_ctor_set(v___x_4221_, 0, v___x_4223_);
v___x_4225_ = v___x_4221_;
goto v_reusejp_4224_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v___x_4223_);
v___x_4225_ = v_reuseFailAlloc_4226_;
goto v_reusejp_4224_;
}
v_reusejp_4224_:
{
return v___x_4225_;
}
}
}
else
{
lean_object* v_a_4229_; lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4236_; 
v_a_4229_ = lean_ctor_get(v___x_4219_, 0);
v_isSharedCheck_4236_ = !lean_is_exclusive(v___x_4219_);
if (v_isSharedCheck_4236_ == 0)
{
v___x_4231_ = v___x_4219_;
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
else
{
lean_inc(v_a_4229_);
lean_dec(v___x_4219_);
v___x_4231_ = lean_box(0);
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
v_resetjp_4230_:
{
lean_object* v___x_4234_; 
if (v_isShared_4232_ == 0)
{
v___x_4234_ = v___x_4231_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v_a_4229_);
v___x_4234_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
return v___x_4234_;
}
}
}
}
else
{
lean_object* v_a_4237_; lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4244_; 
v_a_4237_ = lean_ctor_get(v___x_4211_, 0);
v_isSharedCheck_4244_ = !lean_is_exclusive(v___x_4211_);
if (v_isSharedCheck_4244_ == 0)
{
v___x_4239_ = v___x_4211_;
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
else
{
lean_inc(v_a_4237_);
lean_dec(v___x_4211_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
lean_object* v___x_4242_; 
if (v_isShared_4240_ == 0)
{
v___x_4242_ = v___x_4239_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4243_; 
v_reuseFailAlloc_4243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4243_, 0, v_a_4237_);
v___x_4242_ = v_reuseFailAlloc_4243_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
return v___x_4242_;
}
}
}
}
}
}
v___jp_4245_:
{
if (lean_obj_tag(v___y_4246_) == 0)
{
lean_object* v_a_4247_; uint8_t v___x_4248_; 
v_a_4247_ = lean_ctor_get(v___y_4246_, 0);
lean_inc(v_a_4247_);
lean_dec_ref_known(v___y_4246_, 1);
v___x_4248_ = lean_unbox(v_a_4247_);
lean_dec(v_a_4247_);
v_a_4204_ = v___x_4248_;
goto v___jp_4203_;
}
else
{
lean_dec_ref(v_declNames_4196_);
return v___y_4246_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___boxed(lean_object* v_declNames_4257_, lean_object* v_a_4258_, lean_object* v_a_4259_, lean_object* v_a_4260_){
_start:
{
lean_object* v_res_4261_; 
v_res_4261_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler(v_declNames_4257_, v_a_4258_, v_a_4259_);
lean_dec(v_a_4259_);
lean_dec_ref(v_a_4258_);
return v_res_4261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; 
v___x_4329_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__14));
v___x_4330_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__0_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_));
v___x_4331_ = l_Lean_Elab_registerDerivingHandler(v___x_4329_, v___x_4330_);
if (lean_obj_tag(v___x_4331_) == 0)
{
lean_object* v___x_4332_; uint8_t v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; 
lean_dec_ref_known(v___x_4331_, 1);
v___x_4332_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__0));
v___x_4333_ = 0;
v___x_4334_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__25_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_));
v___x_4335_ = l_Lean_registerTraceClass(v___x_4332_, v___x_4333_, v___x_4334_);
return v___x_4335_;
}
else
{
return v___x_4331_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2____boxed(lean_object* v_a_4336_){
_start:
{
lean_object* v_res_4337_; 
v_res_4337_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_();
return v_res_4337_;
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
