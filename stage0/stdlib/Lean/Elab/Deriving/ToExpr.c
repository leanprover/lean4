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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg(lean_object* v_as_38_, size_t v_i_39_, size_t v_stop_40_, lean_object* v_b_41_, lean_object* v___y_42_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_38_ = stack[0].m_obj;
size_t v_i_39_ = stack[1].m_num;
size_t v_stop_40_ = stack[2].m_num;
lean_object* v_b_41_ = stack[3].m_obj;
lean_object* v___y_42_ = stack[4].m_obj;
lean_object* v_res_64_;
v_res_64_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg(v_as_38_, v_i_39_, v_stop_40_, v_b_41_, v___y_42_);
stack->m_obj
 = v_res_64_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___boxed(lean_object* v_as_65_, lean_object* v_i_66_, lean_object* v_stop_67_, lean_object* v_b_68_, lean_object* v___y_69_, lean_object* v___y_70_){
_start:
{
size_t v_i_boxed_71_; size_t v_stop_boxed_72_; lean_object* v_res_73_; 
v_i_boxed_71_ = lean_unbox_usize(v_i_66_);
lean_dec(v_i_66_);
v_stop_boxed_72_ = lean_unbox_usize(v_stop_67_);
lean_dec(v_stop_67_);
v_res_73_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg(v_as_65_, v_i_boxed_71_, v_stop_boxed_72_, v_b_68_, v___y_69_);
lean_dec_ref(v___y_69_);
lean_dec_ref(v_as_65_);
return v_res_73_;
}
}
lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm(lean_object* v_f_74_, lean_object* v_args_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_81_ = lean_unsigned_to_nat(0u);
v___x_82_ = lean_array_get_size(v_args_75_);
v___x_83_ = lean_nat_dec_lt(v___x_81_, v___x_82_);
if (v___x_83_ == 0)
{
lean_object* v___x_84_; 
v___x_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_84_, 0, v_f_74_);
return v___x_84_;
}
else
{
uint8_t v___x_85_; 
v___x_85_ = lean_nat_dec_le(v___x_82_, v___x_82_);
if (v___x_85_ == 0)
{
if (v___x_83_ == 0)
{
lean_object* v___x_86_; 
v___x_86_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_86_, 0, v_f_74_);
return v___x_86_;
}
else
{
size_t v___x_87_; size_t v___x_88_; lean_object* v___x_89_; 
v___x_87_ = ((size_t)0ULL);
v___x_88_ = lean_usize_of_nat(v___x_82_);
v___x_89_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg(v_args_75_, v___x_87_, v___x_88_, v_f_74_, v_a_78_);
return v___x_89_;
}
}
else
{
size_t v___x_90_; size_t v___x_91_; lean_object* v___x_92_; 
v___x_90_ = ((size_t)0ULL);
v___x_91_ = lean_usize_of_nat(v___x_82_);
v___x_92_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg(v_args_75_, v___x_90_, v___x_91_, v_f_74_, v_a_78_);
return v___x_92_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_74_ = stack[0].m_obj;
lean_object* v_args_75_ = stack[1].m_obj;
lean_object* v_a_76_ = stack[2].m_obj;
lean_object* v_a_77_ = stack[3].m_obj;
lean_object* v_a_78_ = stack[4].m_obj;
lean_object* v_a_79_ = stack[5].m_obj;
lean_object* v_res_93_;
v_res_93_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm(v_f_74_, v_args_75_, v_a_76_, v_a_77_, v_a_78_, v_a_79_);
stack->m_obj
 = v_res_93_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm___boxed(lean_object* v_f_94_, lean_object* v_args_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm(v_f_94_, v_args_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_);
lean_dec(v_a_99_);
lean_dec_ref(v_a_98_);
lean_dec(v_a_97_);
lean_dec_ref(v_a_96_);
lean_dec_ref(v_args_95_);
return v_res_101_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0(lean_object* v_as_102_, size_t v_i_103_, size_t v_stop_104_, lean_object* v_b_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg(v_as_102_, v_i_103_, v_stop_104_, v_b_105_, v___y_108_);
return v___x_111_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_102_ = stack[0].m_obj;
size_t v_i_103_ = stack[1].m_num;
size_t v_stop_104_ = stack[2].m_num;
lean_object* v_b_105_ = stack[3].m_obj;
lean_object* v___y_106_ = stack[4].m_obj;
lean_object* v___y_107_ = stack[5].m_obj;
lean_object* v___y_108_ = stack[6].m_obj;
lean_object* v___y_109_ = stack[7].m_obj;
lean_object* v_res_112_;
v_res_112_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0(v_as_102_, v_i_103_, v_stop_104_, v_b_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_);
stack->m_obj
 = v_res_112_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___boxed(lean_object* v_as_113_, lean_object* v_i_114_, lean_object* v_stop_115_, lean_object* v_b_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
size_t v_i_boxed_122_; size_t v_stop_boxed_123_; lean_object* v_res_124_; 
v_i_boxed_122_ = lean_unbox_usize(v_i_114_);
lean_dec(v_i_114_);
v_stop_boxed_123_ = lean_unbox_usize(v_stop_115_);
lean_dec(v_stop_115_);
v_res_124_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0(v_as_113_, v_i_boxed_122_, v_stop_boxed_123_, v_b_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_);
lean_dec(v___y_120_);
lean_dec_ref(v___y_119_);
lean_dec(v___y_118_);
lean_dec_ref(v___y_117_);
lean_dec_ref(v_as_113_);
return v_res_124_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__2(size_t v_sz_125_, size_t v_i_126_, lean_object* v_bs_127_){
_start:
{
uint8_t v___x_128_; 
v___x_128_ = lean_usize_dec_lt(v_i_126_, v_sz_125_);
if (v___x_128_ == 0)
{
return v_bs_127_;
}
else
{
lean_object* v_v_129_; lean_object* v___x_130_; lean_object* v_bs_x27_131_; size_t v___x_132_; size_t v___x_133_; lean_object* v___x_134_; 
v_v_129_ = lean_array_uget(v_bs_127_, v_i_126_);
v___x_130_ = lean_unsigned_to_nat(0u);
v_bs_x27_131_ = lean_array_uset(v_bs_127_, v_i_126_, v___x_130_);
v___x_132_ = ((size_t)1ULL);
v___x_133_ = lean_usize_add(v_i_126_, v___x_132_);
v___x_134_ = lean_array_uset(v_bs_x27_131_, v_i_126_, v_v_129_);
v_i_126_ = v___x_133_;
v_bs_127_ = v___x_134_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_125_ = stack[0].m_num;
size_t v_i_126_ = stack[1].m_num;
lean_object* v_bs_127_ = stack[2].m_obj;
lean_object* v_res_136_;
v_res_136_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__2(v_sz_125_, v_i_126_, v_bs_127_);
stack->m_obj
 = v_res_136_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__2___boxed(lean_object* v_sz_137_, lean_object* v_i_138_, lean_object* v_bs_139_){
_start:
{
size_t v_sz_boxed_140_; size_t v_i_boxed_141_; lean_object* v_res_142_; 
v_sz_boxed_140_ = lean_unbox_usize(v_sz_137_);
lean_dec(v_sz_137_);
v_i_boxed_141_ = lean_unbox_usize(v_i_138_);
lean_dec(v_i_138_);
v_res_142_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__2(v_sz_boxed_140_, v_i_boxed_141_, v_bs_139_);
return v_res_142_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__1(size_t v_sz_143_, size_t v_i_144_, lean_object* v_bs_145_){
_start:
{
uint8_t v___x_146_; 
v___x_146_ = lean_usize_dec_lt(v_i_144_, v_sz_143_);
if (v___x_146_ == 0)
{
return v_bs_145_;
}
else
{
lean_object* v_v_147_; lean_object* v___x_148_; lean_object* v_bs_x27_149_; lean_object* v___x_150_; size_t v___x_151_; size_t v___x_152_; lean_object* v___x_153_; 
v_v_147_ = lean_array_uget(v_bs_145_, v_i_144_);
v___x_148_ = lean_unsigned_to_nat(0u);
v_bs_x27_149_ = lean_array_uset(v_bs_145_, v_i_144_, v___x_148_);
v___x_150_ = l_Lean_mkIdent(v_v_147_);
v___x_151_ = ((size_t)1ULL);
v___x_152_ = lean_usize_add(v_i_144_, v___x_151_);
v___x_153_ = lean_array_uset(v_bs_x27_149_, v_i_144_, v___x_150_);
v_i_144_ = v___x_152_;
v_bs_145_ = v___x_153_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_143_ = stack[0].m_num;
size_t v_i_144_ = stack[1].m_num;
lean_object* v_bs_145_ = stack[2].m_obj;
lean_object* v_res_155_;
v_res_155_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__1(v_sz_143_, v_i_144_, v_bs_145_);
stack->m_obj
 = v_res_155_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__1___boxed(lean_object* v_sz_156_, lean_object* v_i_157_, lean_object* v_bs_158_){
_start:
{
size_t v_sz_boxed_159_; size_t v_i_boxed_160_; lean_object* v_res_161_; 
v_sz_boxed_159_ = lean_unbox_usize(v_sz_156_);
lean_dec(v_sz_156_);
v_i_boxed_160_ = lean_unbox_usize(v_i_157_);
lean_dec(v_i_157_);
v_res_161_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__1(v_sz_boxed_159_, v_i_boxed_160_, v_bs_158_);
return v_res_161_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__0(lean_object* v_msgData_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
lean_object* v___x_168_; lean_object* v_env_169_; uint8_t v___x_170_; lean_object* v_env_171_; lean_object* v___x_172_; lean_object* v_toCold_173_; lean_object* v_mctx_174_; lean_object* v_lctx_175_; lean_object* v_options_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_168_ = lean_st_ref_get(v___y_166_);
v_env_169_ = lean_ctor_get(v___x_168_, 0);
lean_inc_ref(v_env_169_);
lean_dec(v___x_168_);
v___x_170_ = 0;
v_env_171_ = l_Lean_Environment_setRecordingDeps(v_env_169_, v___x_170_);
v___x_172_ = lean_st_ref_get(v___y_164_);
v_toCold_173_ = lean_ctor_get(v___y_165_, 0);
v_mctx_174_ = lean_ctor_get(v___x_172_, 0);
lean_inc_ref(v_mctx_174_);
lean_dec(v___x_172_);
v_lctx_175_ = lean_ctor_get(v___y_163_, 2);
v_options_176_ = lean_ctor_get(v_toCold_173_, 2);
lean_inc_ref(v_options_176_);
lean_inc_ref(v_lctx_175_);
v___x_177_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_177_, 0, v_env_171_);
lean_ctor_set(v___x_177_, 1, v_mctx_174_);
lean_ctor_set(v___x_177_, 2, v_lctx_175_);
lean_ctor_set(v___x_177_, 3, v_options_176_);
v___x_178_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
lean_ctor_set(v___x_178_, 1, v_msgData_162_);
v___x_179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
return v___x_179_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_162_ = stack[0].m_obj;
lean_object* v___y_163_ = stack[1].m_obj;
lean_object* v___y_164_ = stack[2].m_obj;
lean_object* v___y_165_ = stack[3].m_obj;
lean_object* v___y_166_ = stack[4].m_obj;
lean_object* v_res_180_;
v_res_180_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__0(v_msgData_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_);
stack->m_obj
 = v_res_180_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__0___boxed(lean_object* v_msgData_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__0(v_msgData_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
return v_res_187_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = lean_box(1);
v___x_189_ = l_Lean_MessageData_ofFormat(v___x_188_);
return v___x_189_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__2));
v___x_194_ = l_Lean_MessageData_ofFormat(v___x_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3(lean_object* v_x_195_, lean_object* v_x_196_){
_start:
{
if (lean_obj_tag(v_x_196_) == 0)
{
return v_x_195_;
}
else
{
lean_object* v_head_197_; lean_object* v_tail_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_220_; 
v_head_197_ = lean_ctor_get(v_x_196_, 0);
v_tail_198_ = lean_ctor_get(v_x_196_, 1);
v_isSharedCheck_220_ = !lean_is_exclusive(v_x_196_);
if (v_isSharedCheck_220_ == 0)
{
v___x_200_ = v_x_196_;
v_isShared_201_ = v_isSharedCheck_220_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_tail_198_);
lean_inc(v_head_197_);
lean_dec(v_x_196_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_220_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v_before_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_218_; 
v_before_202_ = lean_ctor_get(v_head_197_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v_head_197_);
if (v_isSharedCheck_218_ == 0)
{
lean_object* v_unused_219_; 
v_unused_219_ = lean_ctor_get(v_head_197_, 1);
lean_dec(v_unused_219_);
v___x_204_ = v_head_197_;
v_isShared_205_ = v_isSharedCheck_218_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_before_202_);
lean_dec(v_head_197_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_218_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_206_; lean_object* v___x_208_; 
v___x_206_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_205_ == 0)
{
lean_ctor_set_tag(v___x_204_, 7);
lean_ctor_set(v___x_204_, 1, v___x_206_);
lean_ctor_set(v___x_204_, 0, v_x_195_);
v___x_208_ = v___x_204_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_x_195_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v___x_206_);
v___x_208_ = v_reuseFailAlloc_217_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
lean_object* v___x_209_; lean_object* v___x_211_; 
v___x_209_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__3);
if (v_isShared_201_ == 0)
{
lean_ctor_set_tag(v___x_200_, 7);
lean_ctor_set(v___x_200_, 1, v___x_209_);
lean_ctor_set(v___x_200_, 0, v___x_208_);
v___x_211_ = v___x_200_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_208_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v___x_209_);
v___x_211_ = v_reuseFailAlloc_216_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_212_ = l_Lean_MessageData_ofSyntax(v_before_202_);
v___x_213_ = l_Lean_indentD(v___x_212_);
v___x_214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_211_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
v_x_195_ = v___x_214_;
v_x_196_ = v_tail_198_;
goto _start;
}
}
}
}
}
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__2(lean_object* v_opts_221_, lean_object* v_opt_222_){
_start:
{
lean_object* v_name_223_; lean_object* v_defValue_224_; lean_object* v_map_225_; lean_object* v___x_226_; 
v_name_223_ = lean_ctor_get(v_opt_222_, 0);
v_defValue_224_ = lean_ctor_get(v_opt_222_, 1);
v_map_225_ = lean_ctor_get(v_opts_221_, 0);
v___x_226_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_225_, v_name_223_);
if (lean_obj_tag(v___x_226_) == 0)
{
uint8_t v___x_227_; 
v___x_227_ = lean_unbox(v_defValue_224_);
return v___x_227_;
}
else
{
lean_object* v_val_228_; 
v_val_228_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_val_228_);
lean_dec_ref_known(v___x_226_, 1);
if (lean_obj_tag(v_val_228_) == 1)
{
uint8_t v_v_229_; 
v_v_229_ = lean_ctor_get_uint8(v_val_228_, 0);
lean_dec_ref_known(v_val_228_, 0);
return v_v_229_;
}
else
{
uint8_t v___x_230_; 
lean_dec(v_val_228_);
v___x_230_ = lean_unbox(v_defValue_224_);
return v___x_230_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_221_ = stack[0].m_obj;
lean_object* v_opt_222_ = stack[1].m_obj;
uint8_t v_res_231_;
v_res_231_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__2(v_opts_221_, v_opt_222_);
stack->m_num = v_res_231_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__2___boxed(lean_object* v_opts_232_, lean_object* v_opt_233_){
_start:
{
uint8_t v_res_234_; lean_object* v_r_235_; 
v_res_234_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__2(v_opts_232_, v_opt_233_);
lean_dec_ref(v_opt_233_);
lean_dec_ref(v_opts_232_);
v_r_235_ = lean_box(v_res_234_);
return v_r_235_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg___closed__1));
v___x_240_ = l_Lean_MessageData_ofFormat(v___x_239_);
return v___x_240_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg(lean_object* v_msgData_241_, lean_object* v_macroStack_242_, lean_object* v___y_243_){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; uint8_t v___x_247_; 
v___x_245_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_243_);
v___x_246_ = l_Lean_Elab_pp_macroStack;
v___x_247_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__2(v___x_245_, v___x_246_);
lean_dec_ref(v___x_245_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; 
lean_dec(v_macroStack_242_);
v___x_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_248_, 0, v_msgData_241_);
return v___x_248_;
}
else
{
if (lean_obj_tag(v_macroStack_242_) == 0)
{
lean_object* v___x_249_; 
v___x_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_249_, 0, v_msgData_241_);
return v___x_249_;
}
else
{
lean_object* v_head_250_; lean_object* v_after_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_266_; 
v_head_250_ = lean_ctor_get(v_macroStack_242_, 0);
lean_inc(v_head_250_);
v_after_251_ = lean_ctor_get(v_head_250_, 1);
v_isSharedCheck_266_ = !lean_is_exclusive(v_head_250_);
if (v_isSharedCheck_266_ == 0)
{
lean_object* v_unused_267_; 
v_unused_267_ = lean_ctor_get(v_head_250_, 0);
lean_dec(v_unused_267_);
v___x_253_ = v_head_250_;
v_isShared_254_ = v_isSharedCheck_266_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_after_251_);
lean_dec(v_head_250_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_266_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_255_; lean_object* v___x_257_; 
v___x_255_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_254_ == 0)
{
lean_ctor_set_tag(v___x_253_, 7);
lean_ctor_set(v___x_253_, 1, v___x_255_);
lean_ctor_set(v___x_253_, 0, v_msgData_241_);
v___x_257_ = v___x_253_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_msgData_241_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v___x_255_);
v___x_257_ = v_reuseFailAlloc_265_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v_msgData_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_258_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg___closed__2);
v___x_259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_257_);
lean_ctor_set(v___x_259_, 1, v___x_258_);
v___x_260_ = l_Lean_MessageData_ofSyntax(v_after_251_);
v___x_261_ = l_Lean_indentD(v___x_260_);
v_msgData_262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_262_, 0, v___x_259_);
lean_ctor_set(v_msgData_262_, 1, v___x_261_);
v___x_263_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_spec__3(v_msgData_262_, v_macroStack_242_);
v___x_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
return v___x_264_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_241_ = stack[0].m_obj;
lean_object* v_macroStack_242_ = stack[1].m_obj;
lean_object* v___y_243_ = stack[2].m_obj;
lean_object* v_res_268_;
v_res_268_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg(v_msgData_241_, v_macroStack_242_, v___y_243_);
stack->m_obj
 = v_res_268_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_269_, lean_object* v_macroStack_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg(v_msgData_269_, v_macroStack_270_, v___y_271_);
lean_dec_ref(v___y_271_);
return v_res_273_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(lean_object* v_msg_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v_ref_282_; lean_object* v_macroStack_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v_a_286_; lean_object* v___x_287_; lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_296_; 
v_ref_282_ = lean_ctor_get(v___y_279_, 2);
v_macroStack_283_ = lean_ctor_get(v___y_275_, 1);
v___x_284_ = l_Lean_Elab_getBetterRef(v_ref_282_, v_macroStack_283_);
v___x_285_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__0(v_msg_274_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
v_a_286_ = lean_ctor_get(v___x_285_, 0);
lean_inc(v_a_286_);
lean_dec_ref(v___x_285_);
lean_inc(v_macroStack_283_);
v___x_287_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg(v_a_286_, v_macroStack_283_, v___y_279_);
v_a_288_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_296_ == 0)
{
v___x_290_ = v___x_287_;
v_isShared_291_ = v_isSharedCheck_296_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_287_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_296_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_292_; lean_object* v___x_294_; 
v___x_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_284_);
lean_ctor_set(v___x_292_, 1, v_a_288_);
if (v_isShared_291_ == 0)
{
lean_ctor_set_tag(v___x_290_, 1);
lean_ctor_set(v___x_290_, 0, v___x_292_);
v___x_294_ = v___x_290_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_292_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_274_ = stack[0].m_obj;
lean_object* v___y_275_ = stack[1].m_obj;
lean_object* v___y_276_ = stack[2].m_obj;
lean_object* v___y_277_ = stack[3].m_obj;
lean_object* v___y_278_ = stack[4].m_obj;
lean_object* v___y_279_ = stack[5].m_obj;
lean_object* v___y_280_ = stack[6].m_obj;
lean_object* v_res_297_;
v_res_297_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v_msg_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
stack->m_obj
 = v_res_297_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg___boxed(lean_object* v_msg_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v_msg_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
return v_res_306_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__1(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__0));
v___x_309_ = l_Lean_stringToMessageData(v___x_308_);
return v___x_309_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8(void){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Array_mkArray0___redArg();
return v___x_324_;
}
}
lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType(lean_object* v_indVal_327_, lean_object* v_t_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
lean_object* v_toConstantVal_336_; lean_object* v_levelParams_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_385_; 
v_toConstantVal_336_ = lean_ctor_get(v_indVal_327_, 0);
lean_inc_ref(v_toConstantVal_336_);
lean_dec_ref(v_indVal_327_);
v_levelParams_337_ = lean_ctor_get(v_toConstantVal_336_, 1);
v_isSharedCheck_385_ = !lean_is_exclusive(v_toConstantVal_336_);
if (v_isSharedCheck_385_ == 0)
{
lean_object* v_unused_386_; lean_object* v_unused_387_; 
v_unused_386_ = lean_ctor_get(v_toConstantVal_336_, 2);
lean_dec(v_unused_386_);
v_unused_387_ = lean_ctor_get(v_toConstantVal_336_, 0);
lean_dec(v_unused_387_);
v___x_339_ = v_toConstantVal_336_;
v_isShared_340_ = v_isSharedCheck_385_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_levelParams_337_);
lean_dec(v_toConstantVal_336_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_385_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_341_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
lean_inc(v_t_328_);
v___x_342_ = l_Lean_Syntax_isOfKind(v_t_328_, v___x_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; lean_object* v___x_344_; 
lean_del_object(v___x_339_);
lean_dec(v_levelParams_337_);
lean_dec(v_t_328_);
v___x_343_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__1, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__1_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__1);
v___x_344_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v___x_343_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_);
return v___x_344_;
}
else
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_345_ = lean_unsigned_to_nat(0u);
v___x_346_ = l_Lean_Syntax_getArg(v_t_328_, v___x_345_);
v___x_347_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__3));
lean_inc(v___x_346_);
v___x_348_ = l_Lean_Syntax_isOfKind(v___x_346_, v___x_347_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; lean_object* v___x_350_; 
lean_dec(v___x_346_);
lean_del_object(v___x_339_);
lean_dec(v_levelParams_337_);
lean_dec(v_t_328_);
v___x_349_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__1, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__1_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__1);
v___x_350_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v___x_349_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_);
return v___x_350_;
}
else
{
lean_object* v_ref_351_; lean_object* v___x_352_; size_t v_sz_353_; size_t v___x_354_; lean_object* v_levels_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v_args_359_; uint8_t v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; size_t v_sz_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_375_; 
v_ref_351_ = lean_ctor_get(v_a_333_, 2);
v___x_352_ = lean_array_mk(v_levelParams_337_);
v_sz_353_ = lean_array_size(v___x_352_);
v___x_354_ = ((size_t)0ULL);
v_levels_355_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__1(v_sz_353_, v___x_354_, v___x_352_);
v___x_356_ = lean_unsigned_to_nat(1u);
v___x_357_ = l_Lean_Syntax_getArg(v___x_346_, v___x_356_);
lean_dec(v___x_346_);
v___x_358_ = l_Lean_Syntax_getArg(v_t_328_, v___x_356_);
lean_dec(v_t_328_);
v_args_359_ = l_Lean_Syntax_getArgs(v___x_358_);
lean_dec(v___x_358_);
v___x_360_ = 0;
v___x_361_ = l_Lean_SourceInfo_fromRef(v_ref_351_, v___x_360_);
v___x_362_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__4));
lean_inc_n(v___x_361_, 3);
v___x_363_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_361_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
v___x_364_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__6));
v___x_365_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__7));
v___x_366_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_361_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
v___x_367_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_368_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_369_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__9));
v_sz_370_ = lean_array_size(v_levels_355_);
v___x_371_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__2(v_sz_370_, v___x_354_, v_levels_355_);
v___x_372_ = l_Lean_Syntax_SepArray_ofElems(v___x_369_, v___x_371_);
lean_dec_ref(v___x_371_);
v___x_373_ = l_Array_append___redArg(v___x_368_, v___x_372_);
lean_dec_ref(v___x_372_);
if (v_isShared_340_ == 0)
{
lean_ctor_set_tag(v___x_339_, 1);
lean_ctor_set(v___x_339_, 2, v___x_373_);
lean_ctor_set(v___x_339_, 1, v___x_367_);
lean_ctor_set(v___x_339_, 0, v___x_361_);
v___x_375_ = v___x_339_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_361_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v___x_367_);
lean_ctor_set(v_reuseFailAlloc_384_, 2, v___x_373_);
v___x_375_ = v_reuseFailAlloc_384_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_376_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__10));
lean_inc_n(v___x_361_, 4);
v___x_377_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_361_);
lean_ctor_set(v___x_377_, 1, v___x_376_);
v___x_378_ = l_Lean_Syntax_node4(v___x_361_, v___x_364_, v___x_357_, v___x_366_, v___x_375_, v___x_377_);
v___x_379_ = l_Lean_Syntax_node2(v___x_361_, v___x_347_, v___x_363_, v___x_378_);
v___x_380_ = l_Array_append___redArg(v___x_368_, v_args_359_);
lean_dec_ref(v_args_359_);
v___x_381_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_381_, 0, v___x_361_);
lean_ctor_set(v___x_381_, 1, v___x_367_);
lean_ctor_set(v___x_381_, 2, v___x_380_);
v___x_382_ = l_Lean_Syntax_node2(v___x_361_, v___x_341_, v___x_379_, v___x_381_);
v___x_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
return v___x_383_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_0interp(lean_interpreter_value* stack)
{
lean_object* v_indVal_327_ = stack[0].m_obj;
lean_object* v_t_328_ = stack[1].m_obj;
lean_object* v_a_329_ = stack[2].m_obj;
lean_object* v_a_330_ = stack[3].m_obj;
lean_object* v_a_331_ = stack[4].m_obj;
lean_object* v_a_332_ = stack[5].m_obj;
lean_object* v_a_333_ = stack[6].m_obj;
lean_object* v_a_334_ = stack[7].m_obj;
lean_object* v_res_388_;
v_res_388_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType(v_indVal_327_, v_t_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_);
stack->m_obj
 = v_res_388_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___boxed(lean_object* v_indVal_389_, lean_object* v_t_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType(v_indVal_389_, v_t_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_);
lean_dec(v_a_396_);
lean_dec_ref(v_a_395_);
lean_dec(v_a_394_);
lean_dec_ref(v_a_393_);
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
return v_res_398_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0(lean_object* v_00_u03b1_399_, lean_object* v_msg_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v_msg_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
return v___x_408_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_400_ = stack[1].m_obj;
lean_object* v___y_401_ = stack[2].m_obj;
lean_object* v___y_402_ = stack[3].m_obj;
lean_object* v___y_403_ = stack[4].m_obj;
lean_object* v___y_404_ = stack[5].m_obj;
lean_object* v___y_405_ = stack[6].m_obj;
lean_object* v___y_406_ = stack[7].m_obj;
lean_object* v_res_409_;
v_res_409_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0(lean_box(0), v_msg_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
stack->m_obj
 = v_res_409_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___boxed(lean_object* v_00_u03b1_410_, lean_object* v_msg_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0(v_00_u03b1_410_, v_msg_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
return v_res_419_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1(lean_object* v_msgData_420_, lean_object* v_macroStack_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___redArg(v_msgData_420_, v_macroStack_421_, v___y_426_);
return v___x_429_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_420_ = stack[0].m_obj;
lean_object* v_macroStack_421_ = stack[1].m_obj;
lean_object* v___y_422_ = stack[2].m_obj;
lean_object* v___y_423_ = stack[3].m_obj;
lean_object* v___y_424_ = stack[4].m_obj;
lean_object* v___y_425_ = stack[5].m_obj;
lean_object* v___y_426_ = stack[6].m_obj;
lean_object* v___y_427_ = stack[7].m_obj;
lean_object* v_res_430_;
v_res_430_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1(v_msgData_420_, v_macroStack_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
stack->m_obj
 = v_res_430_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1___boxed(lean_object* v_msgData_431_, lean_object* v_macroStack_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__1(v_msgData_431_, v_macroStack_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
return v_res_440_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg___lam__0(lean_object* v_k_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v_b_444_, lean_object* v_c_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
lean_object* v___x_451_; 
lean_inc(v___y_449_);
lean_inc_ref(v___y_448_);
lean_inc(v___y_447_);
lean_inc_ref(v___y_446_);
lean_inc(v___y_443_);
lean_inc_ref(v___y_442_);
v___x_451_ = lean_apply_9(v_k_441_, v_b_444_, v_c_445_, v___y_442_, v___y_443_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, lean_box(0));
return v___x_451_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_441_ = stack[0].m_obj;
lean_object* v___y_442_ = stack[1].m_obj;
lean_object* v___y_443_ = stack[2].m_obj;
lean_object* v_b_444_ = stack[3].m_obj;
lean_object* v_c_445_ = stack[4].m_obj;
lean_object* v___y_446_ = stack[5].m_obj;
lean_object* v___y_447_ = stack[6].m_obj;
lean_object* v___y_448_ = stack[7].m_obj;
lean_object* v___y_449_ = stack[8].m_obj;
lean_object* v_res_452_;
v_res_452_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg___lam__0(v_k_441_, v___y_442_, v___y_443_, v_b_444_, v_c_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
stack->m_obj
 = v_res_452_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg___lam__0___boxed(lean_object* v_k_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v_b_456_, lean_object* v_c_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg___lam__0(v_k_453_, v___y_454_, v___y_455_, v_b_456_, v_c_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
return v_res_463_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg(lean_object* v_type_464_, lean_object* v_k_465_, uint8_t v_cleanupAnnotations_466_, uint8_t v_whnfType_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v___f_475_; lean_object* v___x_476_; 
lean_inc(v___y_469_);
lean_inc_ref(v___y_468_);
v___f_475_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_475_, 0, v_k_465_);
lean_closure_set(v___f_475_, 1, v___y_468_);
lean_closure_set(v___f_475_, 2, v___y_469_);
v___x_476_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_464_, v___f_475_, v_cleanupAnnotations_466_, v_whnfType_467_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
if (lean_obj_tag(v___x_476_) == 0)
{
return v___x_476_;
}
else
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_484_; 
v_a_477_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_484_ == 0)
{
v___x_479_ = v___x_476_;
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_476_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_482_; 
if (v_isShared_480_ == 0)
{
v___x_482_ = v___x_479_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_a_477_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_464_ = stack[0].m_obj;
lean_object* v_k_465_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_466_ = stack[2].m_num;
uint8_t v_whnfType_467_ = stack[3].m_num;
lean_object* v___y_468_ = stack[4].m_obj;
lean_object* v___y_469_ = stack[5].m_obj;
lean_object* v___y_470_ = stack[6].m_obj;
lean_object* v___y_471_ = stack[7].m_obj;
lean_object* v___y_472_ = stack[8].m_obj;
lean_object* v___y_473_ = stack[9].m_obj;
lean_object* v_res_485_;
v_res_485_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg(v_type_464_, v_k_465_, v_cleanupAnnotations_466_, v_whnfType_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
stack->m_obj
 = v_res_485_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg___boxed(lean_object* v_type_486_, lean_object* v_k_487_, lean_object* v_cleanupAnnotations_488_, lean_object* v_whnfType_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_497_; uint8_t v_whnfType_boxed_498_; lean_object* v_res_499_; 
v_cleanupAnnotations_boxed_497_ = lean_unbox(v_cleanupAnnotations_488_);
v_whnfType_boxed_498_ = lean_unbox(v_whnfType_489_);
v_res_499_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg(v_type_486_, v_k_487_, v_cleanupAnnotations_boxed_497_, v_whnfType_boxed_498_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
return v_res_499_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2(lean_object* v_00_u03b1_500_, lean_object* v_type_501_, lean_object* v_k_502_, uint8_t v_cleanupAnnotations_503_, uint8_t v_whnfType_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg(v_type_501_, v_k_502_, v_cleanupAnnotations_503_, v_whnfType_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
return v___x_512_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_501_ = stack[1].m_obj;
lean_object* v_k_502_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_503_ = stack[3].m_num;
uint8_t v_whnfType_504_ = stack[4].m_num;
lean_object* v___y_505_ = stack[5].m_obj;
lean_object* v___y_506_ = stack[6].m_obj;
lean_object* v___y_507_ = stack[7].m_obj;
lean_object* v___y_508_ = stack[8].m_obj;
lean_object* v___y_509_ = stack[9].m_obj;
lean_object* v___y_510_ = stack[10].m_obj;
lean_object* v_res_513_;
v_res_513_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2(lean_box(0), v_type_501_, v_k_502_, v_cleanupAnnotations_503_, v_whnfType_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
stack->m_obj
 = v_res_513_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___boxed(lean_object* v_00_u03b1_514_, lean_object* v_type_515_, lean_object* v_k_516_, lean_object* v_cleanupAnnotations_517_, lean_object* v_whnfType_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_526_; uint8_t v_whnfType_boxed_527_; lean_object* v_res_528_; 
v_cleanupAnnotations_boxed_526_ = lean_unbox(v_cleanupAnnotations_517_);
v_whnfType_boxed_527_ = lean_unbox(v_whnfType_518_);
v_res_528_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2(v_00_u03b1_514_, v_type_515_, v_k_516_, v_cleanupAnnotations_boxed_526_, v_whnfType_boxed_527_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
return v_res_528_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__0));
v___x_531_ = l_String_toRawSubstring_x27(v___x_530_);
return v___x_531_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8(void){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__7));
v___x_547_ = l_String_toRawSubstring_x27(v___x_546_);
return v___x_547_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg(lean_object* v_as_560_, size_t v_sz_561_, size_t v_i_562_, lean_object* v_b_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v_a_570_; uint8_t v___x_574_; 
v___x_574_ = lean_usize_dec_lt(v_i_562_, v_sz_561_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; 
v___x_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_575_, 0, v_b_563_);
return v___x_575_;
}
else
{
lean_object* v_snd_576_; lean_object* v_fst_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_653_; 
v_snd_576_ = lean_ctor_get(v_b_563_, 1);
v_fst_577_ = lean_ctor_get(v_b_563_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v_b_563_);
if (v_isSharedCheck_653_ == 0)
{
v___x_579_ = v_b_563_;
v_isShared_580_ = v_isSharedCheck_653_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_snd_576_);
lean_inc(v_fst_577_);
lean_dec(v_b_563_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_653_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v_array_581_; lean_object* v_start_582_; lean_object* v_stop_583_; uint8_t v___x_584_; 
v_array_581_ = lean_ctor_get(v_snd_576_, 0);
v_start_582_ = lean_ctor_get(v_snd_576_, 1);
v_stop_583_ = lean_ctor_get(v_snd_576_, 2);
v___x_584_ = lean_nat_dec_lt(v_start_582_, v_stop_583_);
if (v___x_584_ == 0)
{
lean_object* v___x_586_; 
if (v_isShared_580_ == 0)
{
v___x_586_ = v___x_579_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_fst_577_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v_snd_576_);
v___x_586_ = v_reuseFailAlloc_588_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_object* v___x_587_; 
v___x_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
return v___x_587_;
}
}
else
{
lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_649_; 
lean_inc(v_stop_583_);
lean_inc(v_start_582_);
lean_inc_ref(v_array_581_);
v_isSharedCheck_649_ = !lean_is_exclusive(v_snd_576_);
if (v_isSharedCheck_649_ == 0)
{
lean_object* v_unused_650_; lean_object* v_unused_651_; lean_object* v_unused_652_; 
v_unused_650_ = lean_ctor_get(v_snd_576_, 2);
lean_dec(v_unused_650_);
v_unused_651_ = lean_ctor_get(v_snd_576_, 1);
lean_dec(v_unused_651_);
v_unused_652_ = lean_ctor_get(v_snd_576_, 0);
lean_dec(v_unused_652_);
v___x_590_ = v_snd_576_;
v_isShared_591_ = v_isSharedCheck_649_;
goto v_resetjp_589_;
}
else
{
lean_dec(v_snd_576_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_649_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v_a_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_597_; 
v_a_592_ = lean_array_uget_borrowed(v_as_560_, v_i_562_);
v___x_593_ = lean_array_fget(v_array_581_, v_start_582_);
v___x_594_ = lean_unsigned_to_nat(1u);
v___x_595_ = lean_nat_add(v_start_582_, v___x_594_);
lean_dec(v_start_582_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 1, v___x_595_);
v___x_597_ = v___x_590_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_array_581_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v___x_595_);
lean_ctor_set(v_reuseFailAlloc_648_, 2, v_stop_583_);
v___x_597_ = v_reuseFailAlloc_648_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
lean_inc(v_a_592_);
v___x_598_ = l_Lean_mkIdent(v_a_592_);
v___x_599_ = l_Lean_Meta_isType(v___x_593_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; uint8_t v___x_601_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_a_600_);
lean_dec_ref_known(v___x_599_, 1);
v___x_601_ = lean_unbox(v_a_600_);
if (v___x_601_ == 0)
{
lean_object* v_toCold_602_; lean_object* v_ref_603_; lean_object* v_quotContext_604_; lean_object* v_currMacroScope_605_; uint8_t v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_619_; 
v_toCold_602_ = lean_ctor_get(v___y_566_, 0);
v_ref_603_ = lean_ctor_get(v___y_566_, 2);
v_quotContext_604_ = lean_ctor_get(v_toCold_602_, 8);
v_currMacroScope_605_ = lean_ctor_get(v_toCold_602_, 9);
v___x_606_ = lean_unbox(v_a_600_);
lean_dec(v_a_600_);
v___x_607_ = l_Lean_SourceInfo_fromRef(v_ref_603_, v___x_606_);
v___x_608_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_609_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1);
v___x_610_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__2));
lean_inc(v_currMacroScope_605_);
lean_inc(v_quotContext_604_);
v___x_611_ = l_Lean_addMacroScope(v_quotContext_604_, v___x_610_, v_currMacroScope_605_);
v___x_612_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__6));
lean_inc_n(v___x_607_, 2);
v___x_613_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_613_, 0, v___x_607_);
lean_ctor_set(v___x_613_, 1, v___x_609_);
lean_ctor_set(v___x_613_, 2, v___x_611_);
lean_ctor_set(v___x_613_, 3, v___x_612_);
v___x_614_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_615_ = l_Lean_Syntax_node1(v___x_607_, v___x_614_, v___x_598_);
v___x_616_ = l_Lean_Syntax_node2(v___x_607_, v___x_608_, v___x_613_, v___x_615_);
v___x_617_ = lean_array_push(v_fst_577_, v___x_616_);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 1, v___x_597_);
lean_ctor_set(v___x_579_, 0, v___x_617_);
v___x_619_ = v___x_579_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_617_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v___x_597_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
v_a_570_ = v___x_619_;
goto v___jp_569_;
}
}
else
{
lean_object* v_toCold_621_; lean_object* v_ref_622_; lean_object* v_quotContext_623_; lean_object* v_currMacroScope_624_; uint8_t v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_638_; 
lean_dec(v_a_600_);
v_toCold_621_ = lean_ctor_get(v___y_566_, 0);
v_ref_622_ = lean_ctor_get(v___y_566_, 2);
v_quotContext_623_ = lean_ctor_get(v_toCold_621_, 8);
v_currMacroScope_624_ = lean_ctor_get(v_toCold_621_, 9);
v___x_625_ = 0;
v___x_626_ = l_Lean_SourceInfo_fromRef(v_ref_622_, v___x_625_);
v___x_627_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_628_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8);
v___x_629_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__9));
lean_inc(v_currMacroScope_624_);
lean_inc(v_quotContext_623_);
v___x_630_ = l_Lean_addMacroScope(v_quotContext_623_, v___x_629_, v_currMacroScope_624_);
v___x_631_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__12));
lean_inc_n(v___x_626_, 2);
v___x_632_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_632_, 0, v___x_626_);
lean_ctor_set(v___x_632_, 1, v___x_628_);
lean_ctor_set(v___x_632_, 2, v___x_630_);
lean_ctor_set(v___x_632_, 3, v___x_631_);
v___x_633_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_634_ = l_Lean_Syntax_node1(v___x_626_, v___x_633_, v___x_598_);
v___x_635_ = l_Lean_Syntax_node2(v___x_626_, v___x_627_, v___x_632_, v___x_634_);
v___x_636_ = lean_array_push(v_fst_577_, v___x_635_);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 1, v___x_597_);
lean_ctor_set(v___x_579_, 0, v___x_636_);
v___x_638_ = v___x_579_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_636_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v___x_597_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
v_a_570_ = v___x_638_;
goto v___jp_569_;
}
}
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_dec(v___x_598_);
lean_dec_ref(v___x_597_);
lean_del_object(v___x_579_);
lean_dec(v_fst_577_);
v_a_640_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_599_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_599_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
}
}
}
}
v___jp_569_:
{
size_t v___x_571_; size_t v___x_572_; 
v___x_571_ = ((size_t)1ULL);
v___x_572_ = lean_usize_add(v_i_562_, v___x_571_);
v_i_562_ = v___x_572_;
v_b_563_ = v_a_570_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_560_ = stack[0].m_obj;
size_t v_sz_561_ = stack[1].m_num;
size_t v_i_562_ = stack[2].m_num;
lean_object* v_b_563_ = stack[3].m_obj;
lean_object* v___y_564_ = stack[4].m_obj;
lean_object* v___y_565_ = stack[5].m_obj;
lean_object* v___y_566_ = stack[6].m_obj;
lean_object* v___y_567_ = stack[7].m_obj;
lean_object* v_res_654_;
v_res_654_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg(v_as_560_, v_sz_561_, v_i_562_, v_b_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
stack->m_obj
 = v_res_654_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___boxed(lean_object* v_as_655_, lean_object* v_sz_656_, lean_object* v_i_657_, lean_object* v_b_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
size_t v_sz_boxed_664_; size_t v_i_boxed_665_; lean_object* v_res_666_; 
v_sz_boxed_664_ = lean_unbox_usize(v_sz_656_);
lean_dec(v_sz_656_);
v_i_boxed_665_ = lean_unbox_usize(v_i_657_);
lean_dec(v_i_657_);
v_res_666_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg(v_as_655_, v_sz_boxed_664_, v_i_boxed_665_, v_b_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec_ref(v_as_655_);
return v_res_666_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__1));
v___x_671_ = l_String_toRawSubstring_x27(v___x_670_);
return v___x_671_;
}
}
lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0(lean_object* v_argNames_707_, size_t v___x_708_, lean_object* v_a_709_, lean_object* v_name_710_, lean_object* v_xs_711_, lean_object* v_x_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; size_t v_sz_725_; lean_object* v___x_726_; 
v___x_720_ = lean_unsigned_to_nat(0u);
v___x_721_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__0));
v___x_722_ = lean_array_get_size(v_xs_711_);
v___x_723_ = l_Array_toSubarray___redArg(v_xs_711_, v___x_720_, v___x_722_);
v___x_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_721_);
lean_ctor_set(v___x_724_, 1, v___x_723_);
v_sz_725_ = lean_array_size(v_argNames_707_);
v___x_726_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg(v_argNames_707_, v_sz_725_, v___x_708_, v___x_724_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; lean_object* v_toCold_728_; lean_object* v_fst_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_778_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_a_727_);
lean_dec_ref_known(v___x_726_, 1);
v_toCold_728_ = lean_ctor_get(v___y_717_, 0);
v_fst_729_ = lean_ctor_get(v_a_727_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v_a_727_);
if (v_isSharedCheck_778_ == 0)
{
lean_object* v_unused_779_; 
v_unused_779_ = lean_ctor_get(v_a_727_, 1);
lean_dec(v_unused_779_);
v___x_731_ = v_a_727_;
v_isShared_732_ = v_isSharedCheck_778_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_fst_729_);
lean_dec(v_a_727_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_778_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v_ref_733_; lean_object* v_quotContext_734_; lean_object* v_currMacroScope_735_; uint8_t v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___y_747_; lean_object* v___x_764_; 
v_ref_733_ = lean_ctor_get(v___y_717_, 2);
v_quotContext_734_ = lean_ctor_get(v_toCold_728_, 8);
v_currMacroScope_735_ = lean_ctor_get(v_toCold_728_, 9);
v___x_736_ = 0;
v___x_737_ = l_Lean_SourceInfo_fromRef(v_ref_733_, v___x_736_);
v___x_738_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_739_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__2, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__2_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__2);
v___x_740_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__4));
lean_inc(v_currMacroScope_735_);
lean_inc(v_quotContext_734_);
v___x_741_ = l_Lean_addMacroScope(v_quotContext_734_, v___x_740_, v_currMacroScope_735_);
v___x_742_ = lean_box(0);
v___x_743_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__10));
lean_inc(v___x_737_);
v___x_744_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_744_, 0, v___x_737_);
lean_ctor_set(v___x_744_, 1, v___x_739_);
lean_ctor_set(v___x_744_, 2, v___x_741_);
lean_ctor_set(v___x_744_, 3, v___x_743_);
v___x_745_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
lean_inc(v_name_710_);
v___x_764_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_742_, v_name_710_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v___x_765_; 
v___x_765_ = l_Lean_quoteNameMk(v_name_710_);
v___y_747_ = v___x_765_;
goto v___jp_746_;
}
else
{
lean_object* v_val_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
lean_dec(v_name_710_);
v_val_766_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_val_766_);
lean_dec_ref_known(v___x_764_, 1);
v___x_767_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__16));
v___x_768_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__17));
v___x_769_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__18));
v___x_770_ = lean_string_intercalate(v___x_769_, v_val_766_);
v___x_771_ = lean_string_append(v___x_768_, v___x_770_);
lean_dec_ref(v___x_770_);
v___x_772_ = lean_box(2);
v___x_773_ = l_Lean_Syntax_mkNameLit(v___x_771_, v___x_772_);
v___x_774_ = lean_unsigned_to_nat(1u);
v___x_775_ = lean_mk_empty_array_with_capacity(v___x_774_);
v___x_776_ = lean_array_push(v___x_775_, v___x_773_);
v___x_777_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_777_, 0, v___x_772_);
lean_ctor_set(v___x_777_, 1, v___x_767_);
lean_ctor_set(v___x_777_, 2, v___x_776_);
v___y_747_ = v___x_777_;
goto v___jp_746_;
}
v___jp_746_:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_751_; 
v___x_748_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__12));
v___x_749_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__13));
lean_inc(v___x_737_);
if (v_isShared_732_ == 0)
{
lean_ctor_set_tag(v___x_731_, 2);
lean_ctor_set(v___x_731_, 1, v___x_749_);
lean_ctor_set(v___x_731_, 0, v___x_737_);
v___x_751_ = v___x_731_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_737_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v___x_749_);
v___x_751_ = v_reuseFailAlloc_763_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_752_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_753_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__9));
v___x_754_ = l_Lean_Syntax_SepArray_ofElems(v___x_753_, v_a_709_);
v___x_755_ = l_Array_append___redArg(v___x_752_, v___x_754_);
lean_dec_ref(v___x_754_);
lean_inc_n(v___x_737_, 4);
v___x_756_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_756_, 0, v___x_737_);
lean_ctor_set(v___x_756_, 1, v___x_745_);
lean_ctor_set(v___x_756_, 2, v___x_755_);
v___x_757_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__14));
v___x_758_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_737_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
v___x_759_ = l_Lean_Syntax_node3(v___x_737_, v___x_748_, v___x_751_, v___x_756_, v___x_758_);
v___x_760_ = l_Lean_Syntax_node2(v___x_737_, v___x_745_, v___y_747_, v___x_759_);
v___x_761_ = l_Lean_Syntax_node2(v___x_737_, v___x_738_, v___x_744_, v___x_760_);
v___x_762_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm(v___x_761_, v_fst_729_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
lean_dec(v_fst_729_);
return v___x_762_;
}
}
}
}
else
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_787_; 
lean_dec(v_name_710_);
v_a_780_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_787_ == 0)
{
v___x_782_ = v___x_726_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_726_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_a_780_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_argNames_707_ = stack[0].m_obj;
size_t v___x_708_ = stack[1].m_num;
lean_object* v_a_709_ = stack[2].m_obj;
lean_object* v_name_710_ = stack[3].m_obj;
lean_object* v_xs_711_ = stack[4].m_obj;
lean_object* v_x_712_ = stack[5].m_obj;
lean_object* v___y_713_ = stack[6].m_obj;
lean_object* v___y_714_ = stack[7].m_obj;
lean_object* v___y_715_ = stack[8].m_obj;
lean_object* v___y_716_ = stack[9].m_obj;
lean_object* v___y_717_ = stack[10].m_obj;
lean_object* v___y_718_ = stack[11].m_obj;
lean_object* v_res_788_;
v_res_788_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0(v_argNames_707_, v___x_708_, v_a_709_, v_name_710_, v_xs_711_, v_x_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
stack->m_obj
 = v_res_788_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___boxed(lean_object* v_argNames_789_, lean_object* v___x_790_, lean_object* v_a_791_, lean_object* v_name_792_, lean_object* v_xs_793_, lean_object* v_x_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
size_t v___x_11589__boxed_802_; lean_object* v_res_803_; 
v___x_11589__boxed_802_ = lean_unbox_usize(v___x_790_);
lean_dec(v___x_790_);
v_res_803_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0(v_argNames_789_, v___x_11589__boxed_802_, v_a_791_, v_name_792_, v_xs_793_, v_x_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
lean_dec(v___y_798_);
lean_dec_ref(v___y_797_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec_ref(v_x_794_);
lean_dec_ref(v_a_791_);
lean_dec_ref(v_argNames_789_);
return v_res_803_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_805_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__0));
v___x_806_ = l_String_toRawSubstring_x27(v___x_805_);
return v___x_806_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg(size_t v_sz_822_, size_t v_i_823_, lean_object* v_bs_824_, lean_object* v___y_825_){
_start:
{
uint8_t v___x_827_; 
v___x_827_ = lean_usize_dec_lt(v_i_823_, v_sz_822_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; 
v___x_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_828_, 0, v_bs_824_);
return v___x_828_;
}
else
{
lean_object* v_toCold_829_; lean_object* v_ref_830_; lean_object* v_quotContext_831_; lean_object* v_currMacroScope_832_; lean_object* v_v_833_; lean_object* v___x_834_; lean_object* v_bs_x27_835_; uint8_t v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; size_t v___x_852_; size_t v___x_853_; lean_object* v___x_854_; 
v_toCold_829_ = lean_ctor_get(v___y_825_, 0);
v_ref_830_ = lean_ctor_get(v___y_825_, 2);
v_quotContext_831_ = lean_ctor_get(v_toCold_829_, 8);
v_currMacroScope_832_ = lean_ctor_get(v_toCold_829_, 9);
v_v_833_ = lean_array_uget(v_bs_824_, v_i_823_);
v___x_834_ = lean_unsigned_to_nat(0u);
v_bs_x27_835_ = lean_array_uset(v_bs_824_, v_i_823_, v___x_834_);
v___x_836_ = 0;
v___x_837_ = l_Lean_SourceInfo_fromRef(v_ref_830_, v___x_836_);
v___x_838_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__6));
v___x_839_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__1);
v___x_840_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__3));
lean_inc(v_currMacroScope_832_);
lean_inc(v_quotContext_831_);
v___x_841_ = l_Lean_addMacroScope(v_quotContext_831_, v___x_840_, v_currMacroScope_832_);
v___x_842_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__7));
lean_inc_n(v___x_837_, 4);
v___x_843_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_843_, 0, v___x_837_);
lean_ctor_set(v___x_843_, 1, v___x_839_);
lean_ctor_set(v___x_843_, 2, v___x_841_);
lean_ctor_set(v___x_843_, 3, v___x_842_);
v___x_844_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__7));
v___x_845_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_845_, 0, v___x_837_);
lean_ctor_set(v___x_845_, 1, v___x_844_);
v___x_846_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_847_ = l_Lean_mkIdent(v_v_833_);
v___x_848_ = l_Lean_Syntax_node1(v___x_837_, v___x_846_, v___x_847_);
v___x_849_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__10));
v___x_850_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_837_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
v___x_851_ = l_Lean_Syntax_node4(v___x_837_, v___x_838_, v___x_843_, v___x_845_, v___x_848_, v___x_850_);
v___x_852_ = ((size_t)1ULL);
v___x_853_ = lean_usize_add(v_i_823_, v___x_852_);
v___x_854_ = lean_array_uset(v_bs_x27_835_, v_i_823_, v___x_851_);
v_i_823_ = v___x_853_;
v_bs_824_ = v___x_854_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_822_ = stack[0].m_num;
size_t v_i_823_ = stack[1].m_num;
lean_object* v_bs_824_ = stack[2].m_obj;
lean_object* v___y_825_ = stack[3].m_obj;
lean_object* v_res_856_;
v_res_856_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg(v_sz_822_, v_i_823_, v_bs_824_, v___y_825_);
stack->m_obj
 = v_res_856_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___boxed(lean_object* v_sz_857_, lean_object* v_i_858_, lean_object* v_bs_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
size_t v_sz_boxed_862_; size_t v_i_boxed_863_; lean_object* v_res_864_; 
v_sz_boxed_862_ = lean_unbox_usize(v_sz_857_);
lean_dec(v_sz_857_);
v_i_boxed_863_ = lean_unbox_usize(v_i_858_);
lean_dec(v_i_858_);
v_res_864_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg(v_sz_boxed_862_, v_i_boxed_863_, v_bs_859_, v___y_860_);
lean_dec_ref(v___y_860_);
return v_res_864_;
}
}
lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr(lean_object* v_indVal_867_, lean_object* v_argNames_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
lean_object* v_toConstantVal_876_; lean_object* v_name_877_; lean_object* v_levelParams_878_; lean_object* v_type_879_; lean_object* v___x_880_; size_t v_sz_881_; size_t v___x_882_; lean_object* v___x_883_; 
v_toConstantVal_876_ = lean_ctor_get(v_indVal_867_, 0);
lean_inc_ref(v_toConstantVal_876_);
lean_dec_ref(v_indVal_867_);
v_name_877_ = lean_ctor_get(v_toConstantVal_876_, 0);
lean_inc(v_name_877_);
v_levelParams_878_ = lean_ctor_get(v_toConstantVal_876_, 1);
lean_inc(v_levelParams_878_);
v_type_879_ = lean_ctor_get(v_toConstantVal_876_, 2);
lean_inc_ref(v_type_879_);
lean_dec_ref(v_toConstantVal_876_);
v___x_880_ = lean_array_mk(v_levelParams_878_);
v_sz_881_ = lean_array_size(v___x_880_);
v___x_882_ = ((size_t)0ULL);
v___x_883_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg(v_sz_881_, v___x_882_, v___x_880_, v_a_873_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_885_; lean_object* v___f_886_; uint8_t v___x_887_; lean_object* v___x_888_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
lean_dec_ref_known(v___x_883_, 1);
v___x_885_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___boxed__const__1));
v___f_886_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___boxed), 13, 4);
lean_closure_set(v___f_886_, 0, v_argNames_868_);
lean_closure_set(v___f_886_, 1, v___x_885_);
lean_closure_set(v___f_886_, 2, v_a_884_);
lean_closure_set(v___f_886_, 3, v_name_877_);
v___x_887_ = 0;
v___x_888_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg(v_type_879_, v___f_886_, v___x_887_, v___x_887_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
return v___x_888_;
}
else
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
lean_dec_ref(v_type_879_);
lean_dec(v_name_877_);
lean_dec_ref(v_argNames_868_);
v_a_889_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_883_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_883_);
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
LEAN_EXPORT void l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_indVal_867_ = stack[0].m_obj;
lean_object* v_argNames_868_ = stack[1].m_obj;
lean_object* v_a_869_ = stack[2].m_obj;
lean_object* v_a_870_ = stack[3].m_obj;
lean_object* v_a_871_ = stack[4].m_obj;
lean_object* v_a_872_ = stack[5].m_obj;
lean_object* v_a_873_ = stack[6].m_obj;
lean_object* v_a_874_ = stack[7].m_obj;
lean_object* v_res_897_;
v_res_897_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr(v_indVal_867_, v_argNames_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
stack->m_obj
 = v_res_897_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___boxed(lean_object* v_indVal_898_, lean_object* v_argNames_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr(v_indVal_898_, v_argNames_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_);
lean_dec(v_a_905_);
lean_dec_ref(v_a_904_);
lean_dec(v_a_903_);
lean_dec_ref(v_a_902_);
lean_dec(v_a_901_);
lean_dec_ref(v_a_900_);
return v_res_907_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0(size_t v_sz_908_, size_t v_i_909_, lean_object* v_bs_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg(v_sz_908_, v_i_909_, v_bs_910_, v___y_915_);
return v___x_918_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_908_ = stack[0].m_num;
size_t v_i_909_ = stack[1].m_num;
lean_object* v_bs_910_ = stack[2].m_obj;
lean_object* v___y_911_ = stack[3].m_obj;
lean_object* v___y_912_ = stack[4].m_obj;
lean_object* v___y_913_ = stack[5].m_obj;
lean_object* v___y_914_ = stack[6].m_obj;
lean_object* v___y_915_ = stack[7].m_obj;
lean_object* v___y_916_ = stack[8].m_obj;
lean_object* v_res_919_;
v_res_919_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0(v_sz_908_, v_i_909_, v_bs_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
stack->m_obj
 = v_res_919_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___boxed(lean_object* v_sz_920_, lean_object* v_i_921_, lean_object* v_bs_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
size_t v_sz_boxed_930_; size_t v_i_boxed_931_; lean_object* v_res_932_; 
v_sz_boxed_930_ = lean_unbox_usize(v_sz_920_);
lean_dec(v_sz_920_);
v_i_boxed_931_ = lean_unbox_usize(v_i_921_);
lean_dec(v_i_921_);
v_res_932_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0(v_sz_boxed_930_, v_i_boxed_931_, v_bs_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
return v_res_932_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1(lean_object* v_as_933_, size_t v_sz_934_, size_t v_i_935_, lean_object* v_b_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v___x_944_; 
v___x_944_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg(v_as_933_, v_sz_934_, v_i_935_, v_b_936_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
return v___x_944_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_933_ = stack[0].m_obj;
size_t v_sz_934_ = stack[1].m_num;
size_t v_i_935_ = stack[2].m_num;
lean_object* v_b_936_ = stack[3].m_obj;
lean_object* v___y_937_ = stack[4].m_obj;
lean_object* v___y_938_ = stack[5].m_obj;
lean_object* v___y_939_ = stack[6].m_obj;
lean_object* v___y_940_ = stack[7].m_obj;
lean_object* v___y_941_ = stack[8].m_obj;
lean_object* v___y_942_ = stack[9].m_obj;
lean_object* v_res_945_;
v_res_945_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1(v_as_933_, v_sz_934_, v_i_935_, v_b_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
stack->m_obj
 = v_res_945_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___boxed(lean_object* v_as_946_, lean_object* v_sz_947_, lean_object* v_i_948_, lean_object* v_b_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
size_t v_sz_boxed_957_; size_t v_i_boxed_958_; lean_object* v_res_959_; 
v_sz_boxed_957_ = lean_unbox_usize(v_sz_947_);
lean_dec(v_sz_947_);
v_i_boxed_958_ = lean_unbox_usize(v_i_948_);
lean_dec(v_i_948_);
v_res_959_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1(v_as_946_, v_sz_boxed_957_, v_i_boxed_958_, v_b_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec_ref(v_as_946_);
return v_res_959_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__2));
v___x_967_ = l_String_toRawSubstring_x27(v___x_966_);
return v___x_967_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg(size_t v_sz_970_, size_t v_i_971_, lean_object* v_bs_972_, lean_object* v___y_973_){
_start:
{
uint8_t v___x_975_; 
v___x_975_ = lean_usize_dec_lt(v_i_971_, v_sz_970_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; 
v___x_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_976_, 0, v_bs_972_);
return v___x_976_;
}
else
{
lean_object* v_toCold_977_; lean_object* v_ref_978_; lean_object* v_quotContext_979_; lean_object* v_currMacroScope_980_; lean_object* v_v_981_; lean_object* v___x_982_; lean_object* v_bs_x27_983_; uint8_t v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; size_t v___x_995_; size_t v___x_996_; lean_object* v___x_997_; 
v_toCold_977_ = lean_ctor_get(v___y_973_, 0);
v_ref_978_ = lean_ctor_get(v___y_973_, 2);
v_quotContext_979_ = lean_ctor_get(v_toCold_977_, 8);
v_currMacroScope_980_ = lean_ctor_get(v_toCold_977_, 9);
v_v_981_ = lean_array_uget(v_bs_972_, v_i_971_);
v___x_982_ = lean_unsigned_to_nat(0u);
v_bs_x27_983_ = lean_array_uset(v_bs_972_, v_i_971_, v___x_982_);
v___x_984_ = 0;
v___x_985_ = l_Lean_SourceInfo_fromRef(v_ref_978_, v___x_984_);
v___x_986_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__1));
v___x_987_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__18));
lean_inc_n(v___x_985_, 2);
v___x_988_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_985_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__2);
v___x_990_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__3));
lean_inc(v_currMacroScope_980_);
lean_inc(v_quotContext_979_);
v___x_991_ = l_Lean_addMacroScope(v_quotContext_979_, v___x_990_, v_currMacroScope_980_);
v___x_992_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__7));
v___x_993_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_993_, 0, v___x_985_);
lean_ctor_set(v___x_993_, 1, v___x_989_);
lean_ctor_set(v___x_993_, 2, v___x_991_);
lean_ctor_set(v___x_993_, 3, v___x_992_);
v___x_994_ = l_Lean_Syntax_node3(v___x_985_, v___x_986_, v_v_981_, v___x_988_, v___x_993_);
v___x_995_ = ((size_t)1ULL);
v___x_996_ = lean_usize_add(v_i_971_, v___x_995_);
v___x_997_ = lean_array_uset(v_bs_x27_983_, v_i_971_, v___x_994_);
v_i_971_ = v___x_996_;
v_bs_972_ = v___x_997_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_970_ = stack[0].m_num;
size_t v_i_971_ = stack[1].m_num;
lean_object* v_bs_972_ = stack[2].m_obj;
lean_object* v___y_973_ = stack[3].m_obj;
lean_object* v_res_999_;
v_res_999_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg(v_sz_970_, v_i_971_, v_bs_972_, v___y_973_);
stack->m_obj
 = v_res_999_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___boxed(lean_object* v_sz_1000_, lean_object* v_i_1001_, lean_object* v_bs_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
size_t v_sz_boxed_1005_; size_t v_i_boxed_1006_; lean_object* v_res_1007_; 
v_sz_boxed_1005_ = lean_unbox_usize(v_sz_1000_);
lean_dec(v_sz_1000_);
v_i_boxed_1006_ = lean_unbox_usize(v_i_1001_);
lean_dec(v_i_1001_);
v_res_1007_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg(v_sz_boxed_1005_, v_i_boxed_1006_, v_bs_1002_, v___y_1003_);
lean_dec_ref(v___y_1003_);
return v_res_1007_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1008_; 
v___x_1008_ = l_instMonadEIO___redArg();
return v___x_1008_;
}
}
lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1(lean_object* v_msg_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v_toApplicative_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1116_; 
v___x_1023_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__0);
v___x_1024_ = l_StateRefT_x27_instMonad___redArg(v___x_1023_);
v_toApplicative_1025_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1116_ == 0)
{
lean_object* v_unused_1117_; 
v_unused_1117_ = lean_ctor_get(v___x_1024_, 1);
lean_dec(v_unused_1117_);
v___x_1027_ = v___x_1024_;
v_isShared_1028_ = v_isSharedCheck_1116_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_toApplicative_1025_);
lean_dec(v___x_1024_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1116_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v_toFunctor_1029_; lean_object* v_toSeq_1030_; lean_object* v_toSeqLeft_1031_; lean_object* v_toSeqRight_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1114_; 
v_toFunctor_1029_ = lean_ctor_get(v_toApplicative_1025_, 0);
v_toSeq_1030_ = lean_ctor_get(v_toApplicative_1025_, 2);
v_toSeqLeft_1031_ = lean_ctor_get(v_toApplicative_1025_, 3);
v_toSeqRight_1032_ = lean_ctor_get(v_toApplicative_1025_, 4);
v_isSharedCheck_1114_ = !lean_is_exclusive(v_toApplicative_1025_);
if (v_isSharedCheck_1114_ == 0)
{
lean_object* v_unused_1115_; 
v_unused_1115_ = lean_ctor_get(v_toApplicative_1025_, 1);
lean_dec(v_unused_1115_);
v___x_1034_ = v_toApplicative_1025_;
v_isShared_1035_ = v_isSharedCheck_1114_;
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
v_isShared_1035_ = v_isSharedCheck_1114_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___f_1036_; lean_object* v___f_1037_; lean_object* v___f_1038_; lean_object* v___f_1039_; lean_object* v___x_1040_; lean_object* v___f_1041_; lean_object* v___f_1042_; lean_object* v___f_1043_; lean_object* v___x_1045_; 
v___f_1036_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__1));
v___f_1037_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__2));
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
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1040_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v___f_1036_);
lean_ctor_set(v_reuseFailAlloc_1113_, 2, v___f_1043_);
lean_ctor_set(v_reuseFailAlloc_1113_, 3, v___f_1042_);
lean_ctor_set(v_reuseFailAlloc_1113_, 4, v___f_1041_);
v___x_1045_ = v_reuseFailAlloc_1113_;
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
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v___f_1037_);
v___x_1047_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
lean_object* v___x_1048_; lean_object* v_toApplicative_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1110_; 
v___x_1048_ = l_StateRefT_x27_instMonad___redArg(v___x_1047_);
v_toApplicative_1049_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1110_ == 0)
{
lean_object* v_unused_1111_; 
v_unused_1111_ = lean_ctor_get(v___x_1048_, 1);
lean_dec(v_unused_1111_);
v___x_1051_ = v___x_1048_;
v_isShared_1052_ = v_isSharedCheck_1110_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_toApplicative_1049_);
lean_dec(v___x_1048_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1110_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v_toFunctor_1053_; lean_object* v_toSeq_1054_; lean_object* v_toSeqLeft_1055_; lean_object* v_toSeqRight_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1108_; 
v_toFunctor_1053_ = lean_ctor_get(v_toApplicative_1049_, 0);
v_toSeq_1054_ = lean_ctor_get(v_toApplicative_1049_, 2);
v_toSeqLeft_1055_ = lean_ctor_get(v_toApplicative_1049_, 3);
v_toSeqRight_1056_ = lean_ctor_get(v_toApplicative_1049_, 4);
v_isSharedCheck_1108_ = !lean_is_exclusive(v_toApplicative_1049_);
if (v_isSharedCheck_1108_ == 0)
{
lean_object* v_unused_1109_; 
v_unused_1109_ = lean_ctor_get(v_toApplicative_1049_, 1);
lean_dec(v_unused_1109_);
v___x_1058_ = v_toApplicative_1049_;
v_isShared_1059_ = v_isSharedCheck_1108_;
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
v_isShared_1059_ = v_isSharedCheck_1108_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___f_1060_; lean_object* v___f_1061_; lean_object* v___f_1062_; lean_object* v___f_1063_; lean_object* v___x_1064_; lean_object* v___f_1065_; lean_object* v___f_1066_; lean_object* v___f_1067_; lean_object* v___x_1069_; 
v___f_1060_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__3));
v___f_1061_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__4));
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
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1064_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v___f_1060_);
lean_ctor_set(v_reuseFailAlloc_1107_, 2, v___f_1067_);
lean_ctor_set(v_reuseFailAlloc_1107_, 3, v___f_1066_);
lean_ctor_set(v_reuseFailAlloc_1107_, 4, v___f_1065_);
v___x_1069_ = v_reuseFailAlloc_1107_;
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
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1069_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v___f_1061_);
v___x_1071_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
lean_object* v___x_1072_; lean_object* v_toApplicative_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1104_; 
v___x_1072_ = l_StateRefT_x27_instMonad___redArg(v___x_1071_);
v_toApplicative_1073_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1104_ == 0)
{
lean_object* v_unused_1105_; 
v_unused_1105_ = lean_ctor_get(v___x_1072_, 1);
lean_dec(v_unused_1105_);
v___x_1075_ = v___x_1072_;
v_isShared_1076_ = v_isSharedCheck_1104_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_toApplicative_1073_);
lean_dec(v___x_1072_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1104_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v_toFunctor_1077_; lean_object* v_toSeq_1078_; lean_object* v_toSeqLeft_1079_; lean_object* v_toSeqRight_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1102_; 
v_toFunctor_1077_ = lean_ctor_get(v_toApplicative_1073_, 0);
v_toSeq_1078_ = lean_ctor_get(v_toApplicative_1073_, 2);
v_toSeqLeft_1079_ = lean_ctor_get(v_toApplicative_1073_, 3);
v_toSeqRight_1080_ = lean_ctor_get(v_toApplicative_1073_, 4);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_toApplicative_1073_);
if (v_isSharedCheck_1102_ == 0)
{
lean_object* v_unused_1103_; 
v_unused_1103_ = lean_ctor_get(v_toApplicative_1073_, 1);
lean_dec(v_unused_1103_);
v___x_1082_ = v_toApplicative_1073_;
v_isShared_1083_ = v_isSharedCheck_1102_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_toSeqRight_1080_);
lean_inc(v_toSeqLeft_1079_);
lean_inc(v_toSeq_1078_);
lean_inc(v_toFunctor_1077_);
lean_dec(v_toApplicative_1073_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1102_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___f_1084_; lean_object* v___f_1085_; lean_object* v___f_1086_; lean_object* v___f_1087_; lean_object* v___x_1088_; lean_object* v___f_1089_; lean_object* v___f_1090_; lean_object* v___f_1091_; lean_object* v___x_1093_; 
v___f_1084_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__5));
v___f_1085_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__6));
lean_inc_ref(v_toFunctor_1077_);
v___f_1086_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1086_, 0, v_toFunctor_1077_);
v___f_1087_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1087_, 0, v_toFunctor_1077_);
v___x_1088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___f_1086_);
lean_ctor_set(v___x_1088_, 1, v___f_1087_);
v___f_1089_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1089_, 0, v_toSeqRight_1080_);
v___f_1090_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1090_, 0, v_toSeqLeft_1079_);
v___f_1091_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1091_, 0, v_toSeq_1078_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 4, v___f_1089_);
lean_ctor_set(v___x_1082_, 3, v___f_1090_);
lean_ctor_set(v___x_1082_, 2, v___f_1091_);
lean_ctor_set(v___x_1082_, 1, v___f_1084_);
lean_ctor_set(v___x_1082_, 0, v___x_1088_);
v___x_1093_ = v___x_1082_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1088_);
lean_ctor_set(v_reuseFailAlloc_1101_, 1, v___f_1084_);
lean_ctor_set(v_reuseFailAlloc_1101_, 2, v___f_1091_);
lean_ctor_set(v_reuseFailAlloc_1101_, 3, v___f_1090_);
lean_ctor_set(v_reuseFailAlloc_1101_, 4, v___f_1089_);
v___x_1093_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
lean_object* v___x_1095_; 
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 1, v___f_1085_);
lean_ctor_set(v___x_1075_, 0, v___x_1093_);
v___x_1095_ = v___x_1075_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1093_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v___f_1085_);
v___x_1095_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_27701__overap_1098_; lean_object* v___x_1099_; 
v___x_1096_ = lean_box(0);
v___x_1097_ = l_instInhabitedOfMonad___redArg(v___x_1095_, v___x_1096_);
v___x_27701__overap_1098_ = lean_panic_fn_borrowed(v___x_1097_, v_msg_1015_);
lean_dec(v___x_1097_);
lean_inc(v___y_1021_);
lean_inc_ref(v___y_1020_);
lean_inc(v___y_1019_);
lean_inc_ref(v___y_1018_);
lean_inc(v___y_1017_);
lean_inc_ref(v___y_1016_);
v___x_1099_ = lean_apply_7(v___x_27701__overap_1098_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, lean_box(0));
return v___x_1099_;
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
LEAN_EXPORT void l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1015_ = stack[0].m_obj;
lean_object* v___y_1016_ = stack[1].m_obj;
lean_object* v___y_1017_ = stack[2].m_obj;
lean_object* v___y_1018_ = stack[3].m_obj;
lean_object* v___y_1019_ = stack[4].m_obj;
lean_object* v___y_1020_ = stack[5].m_obj;
lean_object* v___y_1021_ = stack[6].m_obj;
lean_object* v_res_1118_;
v_res_1118_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1(v_msg_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
stack->m_obj
 = v_res_1118_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___boxed(lean_object* v_msg_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1(v_msg_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
return v_res_1127_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__17));
v___x_1129_ = l_Lean_stringToMessageData(v___x_1128_);
return v___x_1129_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__2(void){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__1));
v___x_1132_ = l_Lean_stringToMessageData(v___x_1131_);
return v___x_1132_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__6(void){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1136_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__5));
v___x_1137_ = lean_unsigned_to_nat(11u);
v___x_1138_ = lean_unsigned_to_nat(122u);
v___x_1139_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__4));
v___x_1140_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__3));
v___x_1141_ = l_mkPanicMessageWithDecl(v___x_1140_, v___x_1139_, v___x_1138_, v___x_1137_, v___x_1136_);
return v___x_1141_;
}
}
lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1(lean_object* v_constName_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v___x_1158_; lean_object* v_env_1159_; uint8_t v___x_1160_; lean_object* v___x_1161_; 
v___x_1158_ = lean_st_ref_get(v___y_1148_);
v_env_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc_ref(v_env_1159_);
lean_dec(v___x_1158_);
v___x_1160_ = 0;
lean_inc(v_constName_1142_);
v___x_1161_ = l_Lean_Environment_findAsync_x3f(v_env_1159_, v_constName_1142_, v___x_1160_);
if (lean_obj_tag(v___x_1161_) == 1)
{
lean_object* v_val_1162_; uint8_t v_kind_1163_; 
v_val_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_val_1162_);
lean_dec_ref_known(v___x_1161_, 1);
v_kind_1163_ = lean_ctor_get_uint8(v_val_1162_, sizeof(void*)*3);
if (v_kind_1163_ == 6)
{
lean_object* v___x_1164_; 
v___x_1164_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1162_);
if (lean_obj_tag(v___x_1164_) == 6)
{
lean_object* v_val_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
lean_dec(v_constName_1142_);
v_val_1165_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1167_ = v___x_1164_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_val_1165_);
lean_dec(v___x_1164_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
lean_ctor_set_tag(v___x_1167_, 0);
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_val_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
else
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
lean_dec_ref(v___x_1164_);
v___x_1173_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__6, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__6_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__6);
v___x_1174_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1(v___x_1173_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1183_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1177_ = v___x_1174_;
v_isShared_1178_ = v_isSharedCheck_1183_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1174_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1183_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
if (lean_obj_tag(v_a_1175_) == 0)
{
lean_del_object(v___x_1177_);
goto v___jp_1150_;
}
else
{
lean_object* v_val_1179_; lean_object* v___x_1181_; 
lean_dec(v_constName_1142_);
v_val_1179_ = lean_ctor_get(v_a_1175_, 0);
lean_inc(v_val_1179_);
lean_dec_ref_known(v_a_1175_, 1);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v_val_1179_);
v___x_1181_ = v___x_1177_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_val_1179_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
else
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1191_; 
lean_dec(v_constName_1142_);
v_a_1184_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1186_ = v___x_1174_;
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1174_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1189_; 
if (v_isShared_1187_ == 0)
{
v___x_1189_ = v___x_1186_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1184_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
}
else
{
lean_dec(v_val_1162_);
goto v___jp_1150_;
}
}
else
{
lean_dec(v___x_1161_);
goto v___jp_1150_;
}
v___jp_1150_:
{
lean_object* v___x_1151_; uint8_t v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1151_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__0, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__0_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__0);
v___x_1152_ = 0;
v___x_1153_ = l_Lean_MessageData_ofConstName(v_constName_1142_, v___x_1152_);
v___x_1154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1151_);
lean_ctor_set(v___x_1154_, 1, v___x_1153_);
v___x_1155_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__2, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__2_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__2);
v___x_1156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1154_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v___x_1156_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
return v___x_1157_;
}
}
}
LEAN_EXPORT void l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1142_ = stack[0].m_obj;
lean_object* v___y_1143_ = stack[1].m_obj;
lean_object* v___y_1144_ = stack[2].m_obj;
lean_object* v___y_1145_ = stack[3].m_obj;
lean_object* v___y_1146_ = stack[4].m_obj;
lean_object* v___y_1147_ = stack[5].m_obj;
lean_object* v___y_1148_ = stack[6].m_obj;
lean_object* v_res_1192_;
v_res_1192_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1(v_constName_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
stack->m_obj
 = v_res_1192_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___boxed(lean_object* v_constName_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1(v_constName_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
return v_res_1201_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__0(lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v_ref_1209_; uint8_t v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v_ref_1209_ = lean_ctor_get(v___y_1206_, 2);
v___x_1210_ = 0;
v___x_1211_ = l_Lean_SourceInfo_fromRef(v_ref_1209_, v___x_1210_);
v___x_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
return v___x_1212_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1202_ = stack[0].m_obj;
lean_object* v___y_1203_ = stack[1].m_obj;
lean_object* v___y_1204_ = stack[2].m_obj;
lean_object* v___y_1205_ = stack[3].m_obj;
lean_object* v___y_1206_ = stack[4].m_obj;
lean_object* v___y_1207_ = stack[5].m_obj;
lean_object* v_res_1213_;
v_res_1213_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__0(v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
stack->m_obj
 = v_res_1213_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__0___boxed(lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__0(v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
return v_res_1221_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg(lean_object* v_upperBound_1229_, lean_object* v_a_1230_, lean_object* v_b_1231_, lean_object* v___y_1232_){
_start:
{
uint8_t v___x_1234_; 
v___x_1234_ = lean_nat_dec_lt(v_a_1230_, v_upperBound_1229_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; 
lean_dec(v_a_1230_);
v___x_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1235_, 0, v_b_1231_);
return v___x_1235_;
}
else
{
lean_object* v_ref_1236_; uint8_t v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v_ref_1236_ = lean_ctor_get(v___y_1232_, 2);
v___x_1237_ = 0;
v___x_1238_ = l_Lean_SourceInfo_fromRef(v_ref_1236_, v___x_1237_);
v___x_1239_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__1));
v___x_1240_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__2));
lean_inc(v___x_1238_);
v___x_1241_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1238_);
lean_ctor_set(v___x_1241_, 1, v___x_1240_);
v___x_1242_ = l_Lean_Syntax_node1(v___x_1238_, v___x_1239_, v___x_1241_);
v___x_1243_ = lean_array_push(v_b_1231_, v___x_1242_);
v___x_1244_ = lean_unsigned_to_nat(1u);
v___x_1245_ = lean_nat_add(v_a_1230_, v___x_1244_);
lean_dec(v_a_1230_);
v_a_1230_ = v___x_1245_;
v_b_1231_ = v___x_1243_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1229_ = stack[0].m_obj;
lean_object* v_a_1230_ = stack[1].m_obj;
lean_object* v_b_1231_ = stack[2].m_obj;
lean_object* v___y_1232_ = stack[3].m_obj;
lean_object* v_res_1247_;
v_res_1247_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg(v_upperBound_1229_, v_a_1230_, v_b_1231_, v___y_1232_);
stack->m_obj
 = v_res_1247_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___boxed(lean_object* v_upperBound_1248_, lean_object* v_a_1249_, lean_object* v_b_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg(v_upperBound_1248_, v_a_1249_, v_b_1250_, v___y_1251_);
lean_dec_ref(v___y_1251_);
lean_dec(v_upperBound_1248_);
return v_res_1253_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6___redArg(lean_object* v_upperBound_1254_, lean_object* v_header_1255_, lean_object* v_xs_1256_, lean_object* v_indVal_1257_, lean_object* v_auxFunName_1258_, lean_object* v_levelInsts_1259_, lean_object* v_a_1260_, lean_object* v_b_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
uint8_t v___x_1267_; 
v___x_1267_ = lean_nat_dec_lt(v_a_1260_, v_upperBound_1254_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; 
lean_dec(v_a_1260_);
lean_dec(v_auxFunName_1258_);
lean_dec_ref(v_indVal_1257_);
v___x_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1268_, 0, v_b_1261_);
return v___x_1268_;
}
else
{
lean_object* v_fst_1269_; lean_object* v_snd_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1363_; 
v_fst_1269_ = lean_ctor_get(v_b_1261_, 0);
v_snd_1270_ = lean_ctor_get(v_b_1261_, 1);
v_isSharedCheck_1363_ = !lean_is_exclusive(v_b_1261_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1272_ = v_b_1261_;
v_isShared_1273_ = v_isSharedCheck_1363_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_snd_1270_);
lean_inc(v_fst_1269_);
lean_dec(v_b_1261_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1363_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v_argNames_1274_; lean_object* v_toCold_1275_; lean_object* v_ref_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; uint8_t v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v_a_1289_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v_argNames_1274_ = lean_ctor_get(v_header_1255_, 1);
v_toCold_1275_ = lean_ctor_get(v___y_1264_, 0);
v_ref_1276_ = lean_ctor_get(v___y_1264_, 2);
v___x_1277_ = lean_box(0);
v___x_1278_ = l_Lean_instInhabitedExpr;
v___x_1279_ = lean_array_get_borrowed(v___x_1277_, v_argNames_1274_, v_a_1260_);
lean_inc(v___x_1279_);
v___x_1280_ = l_Lean_mkIdent(v___x_1279_);
v___x_1281_ = 0;
v___x_1282_ = l_Lean_SourceInfo_fromRef(v_ref_1276_, v___x_1281_);
v___x_1283_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__1));
v___x_1284_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__2));
lean_inc_n(v___x_1282_, 2);
v___x_1285_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1282_);
lean_ctor_set(v___x_1285_, 1, v___x_1284_);
v___x_1286_ = l_Lean_Syntax_node1(v___x_1282_, v___x_1283_, v___x_1285_);
v___x_1287_ = lean_array_push(v_fst_1269_, v___x_1286_);
v___x_1297_ = lean_array_get_borrowed(v___x_1278_, v_xs_1256_, v_a_1260_);
lean_inc(v___y_1265_);
lean_inc_ref(v___y_1264_);
lean_inc(v___y_1263_);
lean_inc_ref(v___y_1262_);
lean_inc(v___x_1297_);
v___x_1298_ = lean_infer_type(v___x_1297_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v_toConstantVal_1299_; lean_object* v_a_1300_; lean_object* v_name_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1352_; 
v_toConstantVal_1299_ = lean_ctor_get(v_indVal_1257_, 0);
lean_inc_ref(v_toConstantVal_1299_);
v_a_1300_ = lean_ctor_get(v___x_1298_, 0);
lean_inc(v_a_1300_);
lean_dec_ref_known(v___x_1298_, 1);
v_name_1301_ = lean_ctor_get(v_toConstantVal_1299_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v_toConstantVal_1299_);
if (v_isSharedCheck_1352_ == 0)
{
lean_object* v_unused_1353_; lean_object* v_unused_1354_; 
v_unused_1353_ = lean_ctor_get(v_toConstantVal_1299_, 2);
lean_dec(v_unused_1353_);
v_unused_1354_ = lean_ctor_get(v_toConstantVal_1299_, 1);
lean_dec(v_unused_1354_);
v___x_1303_ = v_toConstantVal_1299_;
v_isShared_1304_ = v_isSharedCheck_1352_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_name_1301_);
lean_dec(v_toConstantVal_1299_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1352_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
uint8_t v___x_1305_; 
v___x_1305_ = l_Lean_Expr_isAppOf(v_a_1300_, v_name_1301_);
lean_dec(v_name_1301_);
lean_dec(v_a_1300_);
if (v___x_1305_ == 0)
{
lean_object* v___x_1306_; 
lean_del_object(v___x_1303_);
lean_dec(v___x_1282_);
lean_inc(v___x_1297_);
v___x_1306_ = l_Lean_Meta_isType(v___x_1297_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_a_1307_; uint8_t v___x_1308_; 
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_a_1307_);
lean_dec_ref_known(v___x_1306_, 1);
v___x_1308_ = lean_unbox(v_a_1307_);
if (v___x_1308_ == 0)
{
lean_object* v_quotContext_1309_; lean_object* v_currMacroScope_1310_; uint8_t v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v_quotContext_1309_ = lean_ctor_get(v_toCold_1275_, 8);
v_currMacroScope_1310_ = lean_ctor_get(v_toCold_1275_, 9);
v___x_1311_ = lean_unbox(v_a_1307_);
lean_dec(v_a_1307_);
v___x_1312_ = l_Lean_SourceInfo_fromRef(v_ref_1276_, v___x_1311_);
v___x_1313_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1314_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1);
v___x_1315_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__2));
lean_inc(v_currMacroScope_1310_);
lean_inc(v_quotContext_1309_);
v___x_1316_ = l_Lean_addMacroScope(v_quotContext_1309_, v___x_1315_, v_currMacroScope_1310_);
v___x_1317_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__6));
lean_inc_n(v___x_1312_, 2);
v___x_1318_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1312_);
lean_ctor_set(v___x_1318_, 1, v___x_1314_);
lean_ctor_set(v___x_1318_, 2, v___x_1316_);
lean_ctor_set(v___x_1318_, 3, v___x_1317_);
v___x_1319_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1320_ = l_Lean_Syntax_node1(v___x_1312_, v___x_1319_, v___x_1280_);
v___x_1321_ = l_Lean_Syntax_node2(v___x_1312_, v___x_1313_, v___x_1318_, v___x_1320_);
v_a_1289_ = v___x_1321_;
goto v___jp_1288_;
}
else
{
lean_object* v_quotContext_1322_; lean_object* v_currMacroScope_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
lean_dec(v_a_1307_);
v_quotContext_1322_ = lean_ctor_get(v_toCold_1275_, 8);
v_currMacroScope_1323_ = lean_ctor_get(v_toCold_1275_, 9);
v___x_1324_ = l_Lean_SourceInfo_fromRef(v_ref_1276_, v___x_1305_);
v___x_1325_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1326_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8);
v___x_1327_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__9));
lean_inc(v_currMacroScope_1323_);
lean_inc(v_quotContext_1322_);
v___x_1328_ = l_Lean_addMacroScope(v_quotContext_1322_, v___x_1327_, v_currMacroScope_1323_);
v___x_1329_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__12));
lean_inc_n(v___x_1324_, 2);
v___x_1330_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1324_);
lean_ctor_set(v___x_1330_, 1, v___x_1326_);
lean_ctor_set(v___x_1330_, 2, v___x_1328_);
lean_ctor_set(v___x_1330_, 3, v___x_1329_);
v___x_1331_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1332_ = l_Lean_Syntax_node1(v___x_1324_, v___x_1331_, v___x_1280_);
v___x_1333_ = l_Lean_Syntax_node2(v___x_1324_, v___x_1325_, v___x_1330_, v___x_1332_);
v_a_1289_ = v___x_1333_;
goto v___jp_1288_;
}
}
else
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1341_; 
lean_dec_ref(v___x_1287_);
lean_dec(v___x_1280_);
lean_del_object(v___x_1272_);
lean_dec(v_snd_1270_);
lean_dec(v_a_1260_);
lean_dec(v_auxFunName_1258_);
lean_dec_ref(v_indVal_1257_);
v_a_1334_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1336_ = v___x_1306_;
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1306_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1339_; 
if (v_isShared_1337_ == 0)
{
v___x_1339_ = v___x_1336_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_a_1334_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
else
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1349_; 
v___x_1342_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
lean_inc(v_auxFunName_1258_);
v___x_1343_ = l_Lean_mkIdent(v_auxFunName_1258_);
v___x_1344_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1345_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_1346_ = l_Array_append___redArg(v___x_1345_, v_levelInsts_1259_);
v___x_1347_ = lean_array_push(v___x_1346_, v___x_1280_);
lean_inc(v___x_1282_);
if (v_isShared_1304_ == 0)
{
lean_ctor_set_tag(v___x_1303_, 1);
lean_ctor_set(v___x_1303_, 2, v___x_1347_);
lean_ctor_set(v___x_1303_, 1, v___x_1344_);
lean_ctor_set(v___x_1303_, 0, v___x_1282_);
v___x_1349_ = v___x_1303_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1282_);
lean_ctor_set(v_reuseFailAlloc_1351_, 1, v___x_1344_);
lean_ctor_set(v_reuseFailAlloc_1351_, 2, v___x_1347_);
v___x_1349_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
lean_object* v___x_1350_; 
v___x_1350_ = l_Lean_Syntax_node2(v___x_1282_, v___x_1342_, v___x_1343_, v___x_1349_);
v_a_1289_ = v___x_1350_;
goto v___jp_1288_;
}
}
}
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
lean_dec_ref(v___x_1287_);
lean_dec(v___x_1282_);
lean_dec(v___x_1280_);
lean_del_object(v___x_1272_);
lean_dec(v_snd_1270_);
lean_dec(v_a_1260_);
lean_dec(v_auxFunName_1258_);
lean_dec_ref(v_indVal_1257_);
v_a_1355_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1298_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1298_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
v___jp_1288_:
{
lean_object* v___x_1290_; lean_object* v___x_1292_; 
v___x_1290_ = lean_array_push(v_snd_1270_, v_a_1289_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 1, v___x_1290_);
lean_ctor_set(v___x_1272_, 0, v___x_1287_);
v___x_1292_ = v___x_1272_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1287_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v___x_1290_);
v___x_1292_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = lean_unsigned_to_nat(1u);
v___x_1294_ = lean_nat_add(v_a_1260_, v___x_1293_);
lean_dec(v_a_1260_);
v_a_1260_ = v___x_1294_;
v_b_1261_ = v___x_1292_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1254_ = stack[0].m_obj;
lean_object* v_header_1255_ = stack[1].m_obj;
lean_object* v_xs_1256_ = stack[2].m_obj;
lean_object* v_indVal_1257_ = stack[3].m_obj;
lean_object* v_auxFunName_1258_ = stack[4].m_obj;
lean_object* v_levelInsts_1259_ = stack[5].m_obj;
lean_object* v_a_1260_ = stack[6].m_obj;
lean_object* v_b_1261_ = stack[7].m_obj;
lean_object* v___y_1262_ = stack[8].m_obj;
lean_object* v___y_1263_ = stack[9].m_obj;
lean_object* v___y_1264_ = stack[10].m_obj;
lean_object* v___y_1265_ = stack[11].m_obj;
lean_object* v_res_1364_;
v_res_1364_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6___redArg(v_upperBound_1254_, v_header_1255_, v_xs_1256_, v_indVal_1257_, v_auxFunName_1258_, v_levelInsts_1259_, v_a_1260_, v_b_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
stack->m_obj
 = v_res_1364_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6___redArg___boxed(lean_object* v_upperBound_1365_, lean_object* v_header_1366_, lean_object* v_xs_1367_, lean_object* v_indVal_1368_, lean_object* v_auxFunName_1369_, lean_object* v_levelInsts_1370_, lean_object* v_a_1371_, lean_object* v_b_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6___redArg(v_upperBound_1365_, v_header_1366_, v_xs_1367_, v_indVal_1368_, v_auxFunName_1369_, v_levelInsts_1370_, v_a_1371_, v_b_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_);
lean_dec(v___y_1376_);
lean_dec_ref(v___y_1375_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
lean_dec_ref(v_levelInsts_1370_);
lean_dec_ref(v_xs_1367_);
lean_dec_ref(v_header_1366_);
lean_dec(v_upperBound_1365_);
return v_res_1378_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4___redArg(lean_object* v_upperBound_1379_, lean_object* v_header_1380_, lean_object* v_xs_1381_, lean_object* v_indVal_1382_, lean_object* v_auxFunName_1383_, lean_object* v_levelInsts_1384_, lean_object* v_a_1385_, lean_object* v_b_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
uint8_t v___x_1394_; 
v___x_1394_ = lean_nat_dec_lt(v_a_1385_, v_upperBound_1379_);
if (v___x_1394_ == 0)
{
lean_object* v___x_1395_; 
lean_dec(v_auxFunName_1383_);
lean_dec_ref(v_indVal_1382_);
v___x_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1395_, 0, v_b_1386_);
return v___x_1395_;
}
else
{
lean_object* v_fst_1396_; lean_object* v_snd_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1490_; 
v_fst_1396_ = lean_ctor_get(v_b_1386_, 0);
v_snd_1397_ = lean_ctor_get(v_b_1386_, 1);
v_isSharedCheck_1490_ = !lean_is_exclusive(v_b_1386_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1399_ = v_b_1386_;
v_isShared_1400_ = v_isSharedCheck_1490_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_snd_1397_);
lean_inc(v_fst_1396_);
lean_dec(v_b_1386_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1490_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v_argNames_1401_; lean_object* v_toCold_1402_; lean_object* v_ref_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; uint8_t v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v_a_1416_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v_argNames_1401_ = lean_ctor_get(v_header_1380_, 1);
v_toCold_1402_ = lean_ctor_get(v___y_1391_, 0);
v_ref_1403_ = lean_ctor_get(v___y_1391_, 2);
v___x_1404_ = lean_box(0);
v___x_1405_ = l_Lean_instInhabitedExpr;
v___x_1406_ = lean_array_get_borrowed(v___x_1404_, v_argNames_1401_, v_a_1385_);
lean_inc(v___x_1406_);
v___x_1407_ = l_Lean_mkIdent(v___x_1406_);
v___x_1408_ = 0;
v___x_1409_ = l_Lean_SourceInfo_fromRef(v_ref_1403_, v___x_1408_);
v___x_1410_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__1));
v___x_1411_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__2));
lean_inc_n(v___x_1409_, 2);
v___x_1412_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1409_);
lean_ctor_set(v___x_1412_, 1, v___x_1411_);
v___x_1413_ = l_Lean_Syntax_node1(v___x_1409_, v___x_1410_, v___x_1412_);
v___x_1414_ = lean_array_push(v_fst_1396_, v___x_1413_);
v___x_1424_ = lean_array_get_borrowed(v___x_1405_, v_xs_1381_, v_a_1385_);
lean_inc(v___y_1392_);
lean_inc_ref(v___y_1391_);
lean_inc(v___y_1390_);
lean_inc_ref(v___y_1389_);
lean_inc(v___x_1424_);
v___x_1425_ = lean_infer_type(v___x_1424_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_toConstantVal_1426_; lean_object* v_a_1427_; lean_object* v_name_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1479_; 
v_toConstantVal_1426_ = lean_ctor_get(v_indVal_1382_, 0);
lean_inc_ref(v_toConstantVal_1426_);
v_a_1427_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_a_1427_);
lean_dec_ref_known(v___x_1425_, 1);
v_name_1428_ = lean_ctor_get(v_toConstantVal_1426_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v_toConstantVal_1426_);
if (v_isSharedCheck_1479_ == 0)
{
lean_object* v_unused_1480_; lean_object* v_unused_1481_; 
v_unused_1480_ = lean_ctor_get(v_toConstantVal_1426_, 2);
lean_dec(v_unused_1480_);
v_unused_1481_ = lean_ctor_get(v_toConstantVal_1426_, 1);
lean_dec(v_unused_1481_);
v___x_1430_ = v_toConstantVal_1426_;
v_isShared_1431_ = v_isSharedCheck_1479_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_name_1428_);
lean_dec(v_toConstantVal_1426_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1479_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
uint8_t v___x_1432_; 
v___x_1432_ = l_Lean_Expr_isAppOf(v_a_1427_, v_name_1428_);
lean_dec(v_name_1428_);
lean_dec(v_a_1427_);
if (v___x_1432_ == 0)
{
lean_object* v___x_1433_; 
lean_del_object(v___x_1430_);
lean_dec(v___x_1409_);
lean_inc(v___x_1424_);
v___x_1433_ = l_Lean_Meta_isType(v___x_1424_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; uint8_t v___x_1435_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_a_1434_);
lean_dec_ref_known(v___x_1433_, 1);
v___x_1435_ = lean_unbox(v_a_1434_);
if (v___x_1435_ == 0)
{
lean_object* v_quotContext_1436_; lean_object* v_currMacroScope_1437_; uint8_t v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v_quotContext_1436_ = lean_ctor_get(v_toCold_1402_, 8);
v_currMacroScope_1437_ = lean_ctor_get(v_toCold_1402_, 9);
v___x_1438_ = lean_unbox(v_a_1434_);
lean_dec(v_a_1434_);
v___x_1439_ = l_Lean_SourceInfo_fromRef(v_ref_1403_, v___x_1438_);
v___x_1440_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1441_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1);
v___x_1442_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__2));
lean_inc(v_currMacroScope_1437_);
lean_inc(v_quotContext_1436_);
v___x_1443_ = l_Lean_addMacroScope(v_quotContext_1436_, v___x_1442_, v_currMacroScope_1437_);
v___x_1444_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__6));
lean_inc_n(v___x_1439_, 2);
v___x_1445_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1439_);
lean_ctor_set(v___x_1445_, 1, v___x_1441_);
lean_ctor_set(v___x_1445_, 2, v___x_1443_);
lean_ctor_set(v___x_1445_, 3, v___x_1444_);
v___x_1446_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1447_ = l_Lean_Syntax_node1(v___x_1439_, v___x_1446_, v___x_1407_);
v___x_1448_ = l_Lean_Syntax_node2(v___x_1439_, v___x_1440_, v___x_1445_, v___x_1447_);
v_a_1416_ = v___x_1448_;
goto v___jp_1415_;
}
else
{
lean_object* v_quotContext_1449_; lean_object* v_currMacroScope_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
lean_dec(v_a_1434_);
v_quotContext_1449_ = lean_ctor_get(v_toCold_1402_, 8);
v_currMacroScope_1450_ = lean_ctor_get(v_toCold_1402_, 9);
v___x_1451_ = l_Lean_SourceInfo_fromRef(v_ref_1403_, v___x_1432_);
v___x_1452_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1453_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8);
v___x_1454_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__9));
lean_inc(v_currMacroScope_1450_);
lean_inc(v_quotContext_1449_);
v___x_1455_ = l_Lean_addMacroScope(v_quotContext_1449_, v___x_1454_, v_currMacroScope_1450_);
v___x_1456_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__12));
lean_inc_n(v___x_1451_, 2);
v___x_1457_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1451_);
lean_ctor_set(v___x_1457_, 1, v___x_1453_);
lean_ctor_set(v___x_1457_, 2, v___x_1455_);
lean_ctor_set(v___x_1457_, 3, v___x_1456_);
v___x_1458_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1459_ = l_Lean_Syntax_node1(v___x_1451_, v___x_1458_, v___x_1407_);
v___x_1460_ = l_Lean_Syntax_node2(v___x_1451_, v___x_1452_, v___x_1457_, v___x_1459_);
v_a_1416_ = v___x_1460_;
goto v___jp_1415_;
}
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
lean_dec_ref(v___x_1414_);
lean_dec(v___x_1407_);
lean_del_object(v___x_1399_);
lean_dec(v_snd_1397_);
lean_dec(v_auxFunName_1383_);
lean_dec_ref(v_indVal_1382_);
v_a_1461_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v___x_1433_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1433_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1461_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
else
{
lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1476_; 
v___x_1469_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
lean_inc(v_auxFunName_1383_);
v___x_1470_ = l_Lean_mkIdent(v_auxFunName_1383_);
v___x_1471_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1472_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_1473_ = l_Array_append___redArg(v___x_1472_, v_levelInsts_1384_);
v___x_1474_ = lean_array_push(v___x_1473_, v___x_1407_);
lean_inc(v___x_1409_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set_tag(v___x_1430_, 1);
lean_ctor_set(v___x_1430_, 2, v___x_1474_);
lean_ctor_set(v___x_1430_, 1, v___x_1471_);
lean_ctor_set(v___x_1430_, 0, v___x_1409_);
v___x_1476_ = v___x_1430_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1409_);
lean_ctor_set(v_reuseFailAlloc_1478_, 1, v___x_1471_);
lean_ctor_set(v_reuseFailAlloc_1478_, 2, v___x_1474_);
v___x_1476_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
lean_object* v___x_1477_; 
v___x_1477_ = l_Lean_Syntax_node2(v___x_1409_, v___x_1469_, v___x_1470_, v___x_1476_);
v_a_1416_ = v___x_1477_;
goto v___jp_1415_;
}
}
}
}
else
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
lean_dec_ref(v___x_1414_);
lean_dec(v___x_1409_);
lean_dec(v___x_1407_);
lean_del_object(v___x_1399_);
lean_dec(v_snd_1397_);
lean_dec(v_auxFunName_1383_);
lean_dec_ref(v_indVal_1382_);
v_a_1482_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1425_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1425_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
v___jp_1415_:
{
lean_object* v___x_1417_; lean_object* v___x_1419_; 
v___x_1417_ = lean_array_push(v_snd_1397_, v_a_1416_);
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 1, v___x_1417_);
lean_ctor_set(v___x_1399_, 0, v___x_1414_);
v___x_1419_ = v___x_1399_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1414_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v___x_1417_);
v___x_1419_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1420_ = lean_unsigned_to_nat(1u);
v___x_1421_ = lean_nat_add(v_a_1385_, v___x_1420_);
v___x_1422_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6___redArg(v_upperBound_1379_, v_header_1380_, v_xs_1381_, v_indVal_1382_, v_auxFunName_1383_, v_levelInsts_1384_, v___x_1421_, v___x_1419_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
return v___x_1422_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1379_ = stack[0].m_obj;
lean_object* v_header_1380_ = stack[1].m_obj;
lean_object* v_xs_1381_ = stack[2].m_obj;
lean_object* v_indVal_1382_ = stack[3].m_obj;
lean_object* v_auxFunName_1383_ = stack[4].m_obj;
lean_object* v_levelInsts_1384_ = stack[5].m_obj;
lean_object* v_a_1385_ = stack[6].m_obj;
lean_object* v_b_1386_ = stack[7].m_obj;
lean_object* v___y_1387_ = stack[8].m_obj;
lean_object* v___y_1388_ = stack[9].m_obj;
lean_object* v___y_1389_ = stack[10].m_obj;
lean_object* v___y_1390_ = stack[11].m_obj;
lean_object* v___y_1391_ = stack[12].m_obj;
lean_object* v___y_1392_ = stack[13].m_obj;
lean_object* v_res_1491_;
v_res_1491_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4___redArg(v_upperBound_1379_, v_header_1380_, v_xs_1381_, v_indVal_1382_, v_auxFunName_1383_, v_levelInsts_1384_, v_a_1385_, v_b_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
stack->m_obj
 = v_res_1491_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4___redArg___boxed(lean_object* v_upperBound_1492_, lean_object* v_header_1493_, lean_object* v_xs_1494_, lean_object* v_indVal_1495_, lean_object* v_auxFunName_1496_, lean_object* v_levelInsts_1497_, lean_object* v_a_1498_, lean_object* v_b_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4___redArg(v_upperBound_1492_, v_header_1493_, v_xs_1494_, v_indVal_1495_, v_auxFunName_1496_, v_levelInsts_1497_, v_a_1498_, v_b_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec(v_a_1498_);
lean_dec_ref(v_levelInsts_1497_);
lean_dec_ref(v_xs_1494_);
lean_dec_ref(v_header_1493_);
lean_dec(v_upperBound_1492_);
return v_res_1507_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg(lean_object* v_upperBound_1511_, lean_object* v___x_1512_, lean_object* v_xs_1513_, lean_object* v_indVal_1514_, lean_object* v_auxFunName_1515_, lean_object* v_levelInsts_1516_, lean_object* v_a_1517_, lean_object* v_b_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
uint8_t v___x_1524_; 
v___x_1524_ = lean_nat_dec_lt(v_a_1517_, v_upperBound_1511_);
if (v___x_1524_ == 0)
{
lean_object* v___x_1525_; 
lean_dec(v_a_1517_);
lean_dec(v_auxFunName_1515_);
lean_dec_ref(v_indVal_1514_);
v___x_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1525_, 0, v_b_1518_);
return v___x_1525_;
}
else
{
lean_object* v_fst_1526_; lean_object* v_snd_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1628_; 
v_fst_1526_ = lean_ctor_get(v_b_1518_, 0);
v_snd_1527_ = lean_ctor_get(v_b_1518_, 1);
v_isSharedCheck_1628_ = !lean_is_exclusive(v_b_1518_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1529_ = v_b_1518_;
v_isShared_1530_ = v_isSharedCheck_1628_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_snd_1527_);
lean_inc(v_fst_1526_);
lean_dec(v_b_1518_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1628_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1531_ = l_Lean_instInhabitedExpr;
v___x_1532_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg___closed__1));
v___x_1533_ = l_Lean_Core_mkFreshUserName(v___x_1532_, v___y_1521_, v___y_1522_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v_a_1538_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_a_1534_);
lean_dec_ref_known(v___x_1533_, 1);
v___x_1535_ = l_Lean_mkIdent(v_a_1534_);
lean_inc(v___x_1535_);
v___x_1536_ = lean_array_push(v_fst_1526_, v___x_1535_);
v___x_1546_ = lean_nat_add(v___x_1512_, v_a_1517_);
v___x_1547_ = lean_array_get_borrowed(v___x_1531_, v_xs_1513_, v___x_1546_);
lean_dec(v___x_1546_);
lean_inc(v___y_1522_);
lean_inc_ref(v___y_1521_);
lean_inc(v___y_1520_);
lean_inc_ref(v___y_1519_);
lean_inc(v___x_1547_);
v___x_1548_ = lean_infer_type(v___x_1547_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_toConstantVal_1549_; lean_object* v_a_1550_; lean_object* v_name_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1609_; 
v_toConstantVal_1549_ = lean_ctor_get(v_indVal_1514_, 0);
lean_inc_ref(v_toConstantVal_1549_);
v_a_1550_ = lean_ctor_get(v___x_1548_, 0);
lean_inc(v_a_1550_);
lean_dec_ref_known(v___x_1548_, 1);
v_name_1551_ = lean_ctor_get(v_toConstantVal_1549_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v_toConstantVal_1549_);
if (v_isSharedCheck_1609_ == 0)
{
lean_object* v_unused_1610_; lean_object* v_unused_1611_; 
v_unused_1610_ = lean_ctor_get(v_toConstantVal_1549_, 2);
lean_dec(v_unused_1610_);
v_unused_1611_ = lean_ctor_get(v_toConstantVal_1549_, 1);
lean_dec(v_unused_1611_);
v___x_1553_ = v_toConstantVal_1549_;
v_isShared_1554_ = v_isSharedCheck_1609_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_name_1551_);
lean_dec(v_toConstantVal_1549_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1609_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
uint8_t v___x_1555_; 
v___x_1555_ = l_Lean_Expr_isAppOf(v_a_1550_, v_name_1551_);
lean_dec(v_name_1551_);
lean_dec(v_a_1550_);
if (v___x_1555_ == 0)
{
lean_object* v___x_1556_; 
lean_del_object(v___x_1553_);
lean_inc(v___x_1547_);
v___x_1556_ = l_Lean_Meta_isType(v___x_1547_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; uint8_t v___x_1558_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1557_);
lean_dec_ref_known(v___x_1556_, 1);
v___x_1558_ = lean_unbox(v_a_1557_);
if (v___x_1558_ == 0)
{
lean_object* v_toCold_1559_; lean_object* v_ref_1560_; lean_object* v_quotContext_1561_; lean_object* v_currMacroScope_1562_; uint8_t v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v_toCold_1559_ = lean_ctor_get(v___y_1521_, 0);
v_ref_1560_ = lean_ctor_get(v___y_1521_, 2);
v_quotContext_1561_ = lean_ctor_get(v_toCold_1559_, 8);
v_currMacroScope_1562_ = lean_ctor_get(v_toCold_1559_, 9);
v___x_1563_ = lean_unbox(v_a_1557_);
lean_dec(v_a_1557_);
v___x_1564_ = l_Lean_SourceInfo_fromRef(v_ref_1560_, v___x_1563_);
v___x_1565_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1566_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1);
v___x_1567_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__2));
lean_inc(v_currMacroScope_1562_);
lean_inc(v_quotContext_1561_);
v___x_1568_ = l_Lean_addMacroScope(v_quotContext_1561_, v___x_1567_, v_currMacroScope_1562_);
v___x_1569_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__6));
lean_inc_n(v___x_1564_, 2);
v___x_1570_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1564_);
lean_ctor_set(v___x_1570_, 1, v___x_1566_);
lean_ctor_set(v___x_1570_, 2, v___x_1568_);
lean_ctor_set(v___x_1570_, 3, v___x_1569_);
v___x_1571_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1572_ = l_Lean_Syntax_node1(v___x_1564_, v___x_1571_, v___x_1535_);
v___x_1573_ = l_Lean_Syntax_node2(v___x_1564_, v___x_1565_, v___x_1570_, v___x_1572_);
v_a_1538_ = v___x_1573_;
goto v___jp_1537_;
}
else
{
lean_object* v_toCold_1574_; lean_object* v_ref_1575_; lean_object* v_quotContext_1576_; lean_object* v_currMacroScope_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
lean_dec(v_a_1557_);
v_toCold_1574_ = lean_ctor_get(v___y_1521_, 0);
v_ref_1575_ = lean_ctor_get(v___y_1521_, 2);
v_quotContext_1576_ = lean_ctor_get(v_toCold_1574_, 8);
v_currMacroScope_1577_ = lean_ctor_get(v_toCold_1574_, 9);
v___x_1578_ = l_Lean_SourceInfo_fromRef(v_ref_1575_, v___x_1555_);
v___x_1579_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1580_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8);
v___x_1581_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__9));
lean_inc(v_currMacroScope_1577_);
lean_inc(v_quotContext_1576_);
v___x_1582_ = l_Lean_addMacroScope(v_quotContext_1576_, v___x_1581_, v_currMacroScope_1577_);
v___x_1583_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__12));
lean_inc_n(v___x_1578_, 2);
v___x_1584_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1578_);
lean_ctor_set(v___x_1584_, 1, v___x_1580_);
lean_ctor_set(v___x_1584_, 2, v___x_1582_);
lean_ctor_set(v___x_1584_, 3, v___x_1583_);
v___x_1585_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1586_ = l_Lean_Syntax_node1(v___x_1578_, v___x_1585_, v___x_1535_);
v___x_1587_ = l_Lean_Syntax_node2(v___x_1578_, v___x_1579_, v___x_1584_, v___x_1586_);
v_a_1538_ = v___x_1587_;
goto v___jp_1537_;
}
}
else
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
lean_dec_ref(v___x_1536_);
lean_dec(v___x_1535_);
lean_del_object(v___x_1529_);
lean_dec(v_snd_1527_);
lean_dec(v_a_1517_);
lean_dec(v_auxFunName_1515_);
lean_dec_ref(v_indVal_1514_);
v_a_1588_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1590_ = v___x_1556_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1556_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1591_ == 0)
{
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_a_1588_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
else
{
lean_object* v_ref_1596_; uint8_t v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1606_; 
v_ref_1596_ = lean_ctor_get(v___y_1521_, 2);
v___x_1597_ = 0;
v___x_1598_ = l_Lean_SourceInfo_fromRef(v_ref_1596_, v___x_1597_);
v___x_1599_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
lean_inc(v_auxFunName_1515_);
v___x_1600_ = l_Lean_mkIdent(v_auxFunName_1515_);
v___x_1601_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1602_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_1603_ = l_Array_append___redArg(v___x_1602_, v_levelInsts_1516_);
v___x_1604_ = lean_array_push(v___x_1603_, v___x_1535_);
lean_inc(v___x_1598_);
if (v_isShared_1554_ == 0)
{
lean_ctor_set_tag(v___x_1553_, 1);
lean_ctor_set(v___x_1553_, 2, v___x_1604_);
lean_ctor_set(v___x_1553_, 1, v___x_1601_);
lean_ctor_set(v___x_1553_, 0, v___x_1598_);
v___x_1606_ = v___x_1553_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1598_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v___x_1601_);
lean_ctor_set(v_reuseFailAlloc_1608_, 2, v___x_1604_);
v___x_1606_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
lean_object* v___x_1607_; 
v___x_1607_ = l_Lean_Syntax_node2(v___x_1598_, v___x_1599_, v___x_1600_, v___x_1606_);
v_a_1538_ = v___x_1607_;
goto v___jp_1537_;
}
}
}
}
else
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
lean_dec_ref(v___x_1536_);
lean_dec(v___x_1535_);
lean_del_object(v___x_1529_);
lean_dec(v_snd_1527_);
lean_dec(v_a_1517_);
lean_dec(v_auxFunName_1515_);
lean_dec_ref(v_indVal_1514_);
v_a_1612_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___x_1548_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1548_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
v___jp_1537_:
{
lean_object* v___x_1539_; lean_object* v___x_1541_; 
v___x_1539_ = lean_array_push(v_snd_1527_, v_a_1538_);
if (v_isShared_1530_ == 0)
{
lean_ctor_set(v___x_1529_, 1, v___x_1539_);
lean_ctor_set(v___x_1529_, 0, v___x_1536_);
v___x_1541_ = v___x_1529_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v___x_1539_);
v___x_1541_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = lean_unsigned_to_nat(1u);
v___x_1543_ = lean_nat_add(v_a_1517_, v___x_1542_);
lean_dec(v_a_1517_);
v_a_1517_ = v___x_1543_;
v_b_1518_ = v___x_1541_;
goto _start;
}
}
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
lean_del_object(v___x_1529_);
lean_dec(v_snd_1527_);
lean_dec(v_fst_1526_);
lean_dec(v_a_1517_);
lean_dec(v_auxFunName_1515_);
lean_dec_ref(v_indVal_1514_);
v_a_1620_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1533_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1533_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1511_ = stack[0].m_obj;
lean_object* v___x_1512_ = stack[1].m_obj;
lean_object* v_xs_1513_ = stack[2].m_obj;
lean_object* v_indVal_1514_ = stack[3].m_obj;
lean_object* v_auxFunName_1515_ = stack[4].m_obj;
lean_object* v_levelInsts_1516_ = stack[5].m_obj;
lean_object* v_a_1517_ = stack[6].m_obj;
lean_object* v_b_1518_ = stack[7].m_obj;
lean_object* v___y_1519_ = stack[8].m_obj;
lean_object* v___y_1520_ = stack[9].m_obj;
lean_object* v___y_1521_ = stack[10].m_obj;
lean_object* v___y_1522_ = stack[11].m_obj;
lean_object* v_res_1629_;
v_res_1629_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg(v_upperBound_1511_, v___x_1512_, v_xs_1513_, v_indVal_1514_, v_auxFunName_1515_, v_levelInsts_1516_, v_a_1517_, v_b_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
stack->m_obj
 = v_res_1629_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg___boxed(lean_object* v_upperBound_1630_, lean_object* v___x_1631_, lean_object* v_xs_1632_, lean_object* v_indVal_1633_, lean_object* v_auxFunName_1634_, lean_object* v_levelInsts_1635_, lean_object* v_a_1636_, lean_object* v_b_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg(v_upperBound_1630_, v___x_1631_, v_xs_1632_, v_indVal_1633_, v_auxFunName_1634_, v_levelInsts_1635_, v_a_1636_, v_b_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec_ref(v_levelInsts_1635_);
lean_dec_ref(v_xs_1632_);
lean_dec(v___x_1631_);
lean_dec(v_upperBound_1630_);
return v_res_1643_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3___redArg(lean_object* v_upperBound_1644_, lean_object* v___x_1645_, lean_object* v_xs_1646_, lean_object* v_indVal_1647_, lean_object* v_auxFunName_1648_, lean_object* v_levelInsts_1649_, lean_object* v_a_1650_, lean_object* v_b_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
uint8_t v___x_1659_; 
v___x_1659_ = lean_nat_dec_lt(v_a_1650_, v_upperBound_1644_);
if (v___x_1659_ == 0)
{
lean_object* v___x_1660_; 
lean_dec(v_auxFunName_1648_);
lean_dec_ref(v_indVal_1647_);
v___x_1660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1660_, 0, v_b_1651_);
return v___x_1660_;
}
else
{
lean_object* v_fst_1661_; lean_object* v_snd_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1763_; 
v_fst_1661_ = lean_ctor_get(v_b_1651_, 0);
v_snd_1662_ = lean_ctor_get(v_b_1651_, 1);
v_isSharedCheck_1763_ = !lean_is_exclusive(v_b_1651_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1664_ = v_b_1651_;
v_isShared_1665_ = v_isSharedCheck_1763_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_snd_1662_);
lean_inc(v_fst_1661_);
lean_dec(v_b_1651_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1763_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1666_ = l_Lean_instInhabitedExpr;
v___x_1667_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg___closed__1));
v___x_1668_ = l_Lean_Core_mkFreshUserName(v___x_1667_, v___y_1656_, v___y_1657_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v_a_1673_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
lean_inc(v_a_1669_);
lean_dec_ref_known(v___x_1668_, 1);
v___x_1670_ = l_Lean_mkIdent(v_a_1669_);
lean_inc(v___x_1670_);
v___x_1671_ = lean_array_push(v_fst_1661_, v___x_1670_);
v___x_1681_ = lean_nat_add(v___x_1645_, v_a_1650_);
v___x_1682_ = lean_array_get_borrowed(v___x_1666_, v_xs_1646_, v___x_1681_);
lean_dec(v___x_1681_);
lean_inc(v___y_1657_);
lean_inc_ref(v___y_1656_);
lean_inc(v___y_1655_);
lean_inc_ref(v___y_1654_);
lean_inc(v___x_1682_);
v___x_1683_ = lean_infer_type(v___x_1682_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_toConstantVal_1684_; lean_object* v_a_1685_; lean_object* v_name_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1744_; 
v_toConstantVal_1684_ = lean_ctor_get(v_indVal_1647_, 0);
lean_inc_ref(v_toConstantVal_1684_);
v_a_1685_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_a_1685_);
lean_dec_ref_known(v___x_1683_, 1);
v_name_1686_ = lean_ctor_get(v_toConstantVal_1684_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v_toConstantVal_1684_);
if (v_isSharedCheck_1744_ == 0)
{
lean_object* v_unused_1745_; lean_object* v_unused_1746_; 
v_unused_1745_ = lean_ctor_get(v_toConstantVal_1684_, 2);
lean_dec(v_unused_1745_);
v_unused_1746_ = lean_ctor_get(v_toConstantVal_1684_, 1);
lean_dec(v_unused_1746_);
v___x_1688_ = v_toConstantVal_1684_;
v_isShared_1689_ = v_isSharedCheck_1744_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_name_1686_);
lean_dec(v_toConstantVal_1684_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1744_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
uint8_t v___x_1690_; 
v___x_1690_ = l_Lean_Expr_isAppOf(v_a_1685_, v_name_1686_);
lean_dec(v_name_1686_);
lean_dec(v_a_1685_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; 
lean_del_object(v___x_1688_);
lean_inc(v___x_1682_);
v___x_1691_ = l_Lean_Meta_isType(v___x_1682_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v_a_1692_; uint8_t v___x_1693_; 
v_a_1692_ = lean_ctor_get(v___x_1691_, 0);
lean_inc(v_a_1692_);
lean_dec_ref_known(v___x_1691_, 1);
v___x_1693_ = lean_unbox(v_a_1692_);
if (v___x_1693_ == 0)
{
lean_object* v_toCold_1694_; lean_object* v_ref_1695_; lean_object* v_quotContext_1696_; lean_object* v_currMacroScope_1697_; uint8_t v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v_toCold_1694_ = lean_ctor_get(v___y_1656_, 0);
v_ref_1695_ = lean_ctor_get(v___y_1656_, 2);
v_quotContext_1696_ = lean_ctor_get(v_toCold_1694_, 8);
v_currMacroScope_1697_ = lean_ctor_get(v_toCold_1694_, 9);
v___x_1698_ = lean_unbox(v_a_1692_);
lean_dec(v_a_1692_);
v___x_1699_ = l_Lean_SourceInfo_fromRef(v_ref_1695_, v___x_1698_);
v___x_1700_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1701_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1);
v___x_1702_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__2));
lean_inc(v_currMacroScope_1697_);
lean_inc(v_quotContext_1696_);
v___x_1703_ = l_Lean_addMacroScope(v_quotContext_1696_, v___x_1702_, v_currMacroScope_1697_);
v___x_1704_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__6));
lean_inc_n(v___x_1699_, 2);
v___x_1705_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1699_);
lean_ctor_set(v___x_1705_, 1, v___x_1701_);
lean_ctor_set(v___x_1705_, 2, v___x_1703_);
lean_ctor_set(v___x_1705_, 3, v___x_1704_);
v___x_1706_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1707_ = l_Lean_Syntax_node1(v___x_1699_, v___x_1706_, v___x_1670_);
v___x_1708_ = l_Lean_Syntax_node2(v___x_1699_, v___x_1700_, v___x_1705_, v___x_1707_);
v_a_1673_ = v___x_1708_;
goto v___jp_1672_;
}
else
{
lean_object* v_toCold_1709_; lean_object* v_ref_1710_; lean_object* v_quotContext_1711_; lean_object* v_currMacroScope_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
lean_dec(v_a_1692_);
v_toCold_1709_ = lean_ctor_get(v___y_1656_, 0);
v_ref_1710_ = lean_ctor_get(v___y_1656_, 2);
v_quotContext_1711_ = lean_ctor_get(v_toCold_1709_, 8);
v_currMacroScope_1712_ = lean_ctor_get(v_toCold_1709_, 9);
v___x_1713_ = l_Lean_SourceInfo_fromRef(v_ref_1710_, v___x_1690_);
v___x_1714_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1715_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8);
v___x_1716_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__9));
lean_inc(v_currMacroScope_1712_);
lean_inc(v_quotContext_1711_);
v___x_1717_ = l_Lean_addMacroScope(v_quotContext_1711_, v___x_1716_, v_currMacroScope_1712_);
v___x_1718_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__12));
lean_inc_n(v___x_1713_, 2);
v___x_1719_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1713_);
lean_ctor_set(v___x_1719_, 1, v___x_1715_);
lean_ctor_set(v___x_1719_, 2, v___x_1717_);
lean_ctor_set(v___x_1719_, 3, v___x_1718_);
v___x_1720_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1721_ = l_Lean_Syntax_node1(v___x_1713_, v___x_1720_, v___x_1670_);
v___x_1722_ = l_Lean_Syntax_node2(v___x_1713_, v___x_1714_, v___x_1719_, v___x_1721_);
v_a_1673_ = v___x_1722_;
goto v___jp_1672_;
}
}
else
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1730_; 
lean_dec_ref(v___x_1671_);
lean_dec(v___x_1670_);
lean_del_object(v___x_1664_);
lean_dec(v_snd_1662_);
lean_dec(v_auxFunName_1648_);
lean_dec_ref(v_indVal_1647_);
v_a_1723_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1725_ = v___x_1691_;
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1691_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1728_; 
if (v_isShared_1726_ == 0)
{
v___x_1728_ = v___x_1725_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_a_1723_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
}
else
{
lean_object* v_ref_1731_; uint8_t v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1741_; 
v_ref_1731_ = lean_ctor_get(v___y_1656_, 2);
v___x_1732_ = 0;
v___x_1733_ = l_Lean_SourceInfo_fromRef(v_ref_1731_, v___x_1732_);
v___x_1734_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
lean_inc(v_auxFunName_1648_);
v___x_1735_ = l_Lean_mkIdent(v_auxFunName_1648_);
v___x_1736_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1737_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_1738_ = l_Array_append___redArg(v___x_1737_, v_levelInsts_1649_);
v___x_1739_ = lean_array_push(v___x_1738_, v___x_1670_);
lean_inc(v___x_1733_);
if (v_isShared_1689_ == 0)
{
lean_ctor_set_tag(v___x_1688_, 1);
lean_ctor_set(v___x_1688_, 2, v___x_1739_);
lean_ctor_set(v___x_1688_, 1, v___x_1736_);
lean_ctor_set(v___x_1688_, 0, v___x_1733_);
v___x_1741_ = v___x_1688_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1733_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v___x_1736_);
lean_ctor_set(v_reuseFailAlloc_1743_, 2, v___x_1739_);
v___x_1741_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Lean_Syntax_node2(v___x_1733_, v___x_1734_, v___x_1735_, v___x_1741_);
v_a_1673_ = v___x_1742_;
goto v___jp_1672_;
}
}
}
}
else
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
lean_dec_ref(v___x_1671_);
lean_dec(v___x_1670_);
lean_del_object(v___x_1664_);
lean_dec(v_snd_1662_);
lean_dec(v_auxFunName_1648_);
lean_dec_ref(v_indVal_1647_);
v_a_1747_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___x_1683_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1683_);
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
v___jp_1672_:
{
lean_object* v___x_1674_; lean_object* v___x_1676_; 
v___x_1674_ = lean_array_push(v_snd_1662_, v_a_1673_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 1, v___x_1674_);
lean_ctor_set(v___x_1664_, 0, v___x_1671_);
v___x_1676_ = v___x_1664_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1671_);
lean_ctor_set(v_reuseFailAlloc_1680_, 1, v___x_1674_);
v___x_1676_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1677_ = lean_unsigned_to_nat(1u);
v___x_1678_ = lean_nat_add(v_a_1650_, v___x_1677_);
v___x_1679_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg(v_upperBound_1644_, v___x_1645_, v_xs_1646_, v_indVal_1647_, v_auxFunName_1648_, v_levelInsts_1649_, v___x_1678_, v___x_1676_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
return v___x_1679_;
}
}
}
else
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1762_; 
lean_del_object(v___x_1664_);
lean_dec(v_snd_1662_);
lean_dec(v_fst_1661_);
lean_dec(v_auxFunName_1648_);
lean_dec_ref(v_indVal_1647_);
v_a_1755_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1757_ = v___x_1668_;
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1668_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1760_; 
if (v_isShared_1758_ == 0)
{
v___x_1760_ = v___x_1757_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_a_1755_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1644_ = stack[0].m_obj;
lean_object* v___x_1645_ = stack[1].m_obj;
lean_object* v_xs_1646_ = stack[2].m_obj;
lean_object* v_indVal_1647_ = stack[3].m_obj;
lean_object* v_auxFunName_1648_ = stack[4].m_obj;
lean_object* v_levelInsts_1649_ = stack[5].m_obj;
lean_object* v_a_1650_ = stack[6].m_obj;
lean_object* v_b_1651_ = stack[7].m_obj;
lean_object* v___y_1652_ = stack[8].m_obj;
lean_object* v___y_1653_ = stack[9].m_obj;
lean_object* v___y_1654_ = stack[10].m_obj;
lean_object* v___y_1655_ = stack[11].m_obj;
lean_object* v___y_1656_ = stack[12].m_obj;
lean_object* v___y_1657_ = stack[13].m_obj;
lean_object* v_res_1764_;
v_res_1764_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3___redArg(v_upperBound_1644_, v___x_1645_, v_xs_1646_, v_indVal_1647_, v_auxFunName_1648_, v_levelInsts_1649_, v_a_1650_, v_b_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
stack->m_obj
 = v_res_1764_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3___redArg___boxed(lean_object* v_upperBound_1765_, lean_object* v___x_1766_, lean_object* v_xs_1767_, lean_object* v_indVal_1768_, lean_object* v_auxFunName_1769_, lean_object* v_levelInsts_1770_, lean_object* v_a_1771_, lean_object* v_b_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3___redArg(v_upperBound_1765_, v___x_1766_, v_xs_1767_, v_indVal_1768_, v_auxFunName_1769_, v_levelInsts_1770_, v_a_1771_, v_b_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec(v_a_1771_);
lean_dec_ref(v_levelInsts_1770_);
lean_dec_ref(v_xs_1767_);
lean_dec(v___x_1766_);
lean_dec(v_upperBound_1765_);
return v_res_1780_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__2(size_t v_sz_1781_, size_t v_i_1782_, lean_object* v_bs_1783_){
_start:
{
uint8_t v___x_1784_; 
v___x_1784_ = lean_usize_dec_lt(v_i_1782_, v_sz_1781_);
if (v___x_1784_ == 0)
{
return v_bs_1783_;
}
else
{
lean_object* v_v_1785_; lean_object* v___x_1786_; lean_object* v_bs_x27_1787_; size_t v___x_1788_; size_t v___x_1789_; lean_object* v___x_1790_; 
v_v_1785_ = lean_array_uget(v_bs_1783_, v_i_1782_);
v___x_1786_ = lean_unsigned_to_nat(0u);
v_bs_x27_1787_ = lean_array_uset(v_bs_1783_, v_i_1782_, v___x_1786_);
v___x_1788_ = ((size_t)1ULL);
v___x_1789_ = lean_usize_add(v_i_1782_, v___x_1788_);
v___x_1790_ = lean_array_uset(v_bs_x27_1787_, v_i_1782_, v_v_1785_);
v_i_1782_ = v___x_1789_;
v_bs_1783_ = v___x_1790_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1781_ = stack[0].m_num;
size_t v_i_1782_ = stack[1].m_num;
lean_object* v_bs_1783_ = stack[2].m_obj;
lean_object* v_res_1792_;
v_res_1792_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__2(v_sz_1781_, v_i_1782_, v_bs_1783_);
stack->m_obj
 = v_res_1792_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__2___boxed(lean_object* v_sz_1793_, lean_object* v_i_1794_, lean_object* v_bs_1795_){
_start:
{
size_t v_sz_boxed_1796_; size_t v_i_boxed_1797_; lean_object* v_res_1798_; 
v_sz_boxed_1796_ = lean_unbox_usize(v_sz_1793_);
lean_dec(v_sz_1793_);
v_i_boxed_1797_ = lean_unbox_usize(v_i_1794_);
lean_dec(v_i_1794_);
v_res_1798_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__2(v_sz_boxed_1796_, v_i_boxed_1797_, v_bs_1795_);
return v_res_1798_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1806_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__9));
v___x_1807_ = l_Lean_mkAtom(v___x_1806_);
return v___x_1807_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1(lean_object* v_indVal_1809_, lean_object* v___x_1810_, lean_object* v___x_1811_, lean_object* v_numParams_1812_, lean_object* v_header_1813_, lean_object* v_auxFunName_1814_, lean_object* v_levelInsts_1815_, lean_object* v_numFields_1816_, lean_object* v_head_1817_, lean_object* v___f_1818_, lean_object* v_a_1819_, lean_object* v_name_1820_, lean_object* v_xs_1821_, lean_object* v_x_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
lean_object* v_numIndices_1830_; lean_object* v___x_1831_; 
v_numIndices_1830_ = lean_ctor_get(v_indVal_1809_, 2);
lean_inc_ref(v___x_1811_);
lean_inc(v___x_1810_);
v___x_1831_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg(v_numIndices_1830_, v___x_1810_, v___x_1811_, v___y_1827_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
lean_inc(v_a_1832_);
lean_dec_ref_known(v___x_1831_, 1);
lean_inc_ref(v___x_1811_);
v___x_1833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1811_);
lean_ctor_set(v___x_1833_, 1, v___x_1811_);
lean_inc(v_auxFunName_1814_);
lean_inc_ref(v_indVal_1809_);
v___x_1834_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4___redArg(v_numParams_1812_, v_header_1813_, v_xs_1821_, v_indVal_1809_, v_auxFunName_1814_, v_levelInsts_1815_, v___x_1810_, v___x_1833_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_a_1835_; lean_object* v_fst_1836_; lean_object* v_snd_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1957_; 
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
lean_inc(v_a_1835_);
lean_dec_ref_known(v___x_1834_, 1);
v_fst_1836_ = lean_ctor_get(v_a_1835_, 0);
v_snd_1837_ = lean_ctor_get(v_a_1835_, 1);
v_isSharedCheck_1957_ = !lean_is_exclusive(v_a_1835_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1839_ = v_a_1835_;
v_isShared_1840_ = v_isSharedCheck_1957_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_snd_1837_);
lean_inc(v_fst_1836_);
lean_dec(v_a_1835_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1957_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1842_; 
if (v_isShared_1840_ == 0)
{
v___x_1842_ = v___x_1839_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_fst_1836_);
lean_ctor_set(v_reuseFailAlloc_1956_, 1, v_snd_1837_);
v___x_1842_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
lean_object* v___x_1843_; 
v___x_1843_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3___redArg(v_numFields_1816_, v_numParams_1812_, v_xs_1821_, v_indVal_1809_, v_auxFunName_1814_, v_levelInsts_1815_, v___x_1810_, v___x_1842_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
lean_dec(v___x_1810_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v_fst_1845_; lean_object* v_snd_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1947_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_a_1844_);
lean_dec_ref_known(v___x_1843_, 1);
v_fst_1845_ = lean_ctor_get(v_a_1844_, 0);
v_snd_1846_ = lean_ctor_get(v_a_1844_, 1);
v_isSharedCheck_1947_ = !lean_is_exclusive(v_a_1844_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1848_ = v_a_1844_;
v_isShared_1849_ = v_isSharedCheck_1947_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_snd_1846_);
lean_inc(v_fst_1845_);
lean_dec(v_a_1844_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1947_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v_toCold_1850_; lean_object* v_ref_1851_; uint8_t v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1858_; 
v_toCold_1850_ = lean_ctor_get(v___y_1827_, 0);
v_ref_1851_ = lean_ctor_get(v___y_1827_, 2);
v___x_1852_ = 0;
v___x_1853_ = l_Lean_SourceInfo_fromRef(v_ref_1851_, v___x_1852_);
v___x_1854_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1855_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__3));
v___x_1856_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__4));
lean_inc(v___x_1853_);
if (v_isShared_1849_ == 0)
{
lean_ctor_set_tag(v___x_1848_, 2);
lean_ctor_set(v___x_1848_, 1, v___x_1856_);
lean_ctor_set(v___x_1848_, 0, v___x_1853_);
v___x_1858_ = v___x_1848_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v___x_1853_);
lean_ctor_set(v_reuseFailAlloc_1946_, 1, v___x_1856_);
v___x_1858_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
v___x_1859_ = l_Lean_mkIdent(v_head_1817_);
lean_inc_n(v___x_1853_, 2);
v___x_1860_ = l_Lean_Syntax_node2(v___x_1853_, v___x_1855_, v___x_1858_, v___x_1859_);
v___x_1861_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1862_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_1863_ = l_Array_append___redArg(v___x_1862_, v_fst_1845_);
lean_dec(v_fst_1845_);
v___x_1864_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1853_);
lean_ctor_set(v___x_1864_, 1, v___x_1861_);
lean_ctor_set(v___x_1864_, 2, v___x_1863_);
v___x_1865_ = l_Lean_Syntax_node2(v___x_1853_, v___x_1854_, v___x_1860_, v___x_1864_);
v___x_1866_ = lean_array_push(v_a_1832_, v___x_1865_);
lean_inc_ref(v___f_1818_);
lean_inc(v___y_1828_);
lean_inc_ref(v___y_1827_);
lean_inc(v___y_1826_);
lean_inc_ref(v___y_1825_);
lean_inc(v___y_1824_);
lean_inc_ref(v___y_1823_);
v___x_1867_ = lean_apply_7(v___f_1818_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, lean_box(0));
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v_a_1868_; lean_object* v_quotContext_1869_; lean_object* v_currMacroScope_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___y_1878_; lean_object* v___x_1924_; 
v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
lean_inc_n(v_a_1868_, 2);
lean_dec_ref_known(v___x_1867_, 1);
v_quotContext_1869_ = lean_ctor_get(v_toCold_1850_, 8);
v_currMacroScope_1870_ = lean_ctor_get(v_toCold_1850_, 9);
v___x_1871_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__4));
v___x_1872_ = lean_box(0);
v___x_1873_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__2, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__2_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__2);
lean_inc(v_currMacroScope_1870_);
lean_inc(v_quotContext_1869_);
v___x_1874_ = l_Lean_addMacroScope(v_quotContext_1869_, v___x_1871_, v_currMacroScope_1870_);
v___x_1875_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__10));
v___x_1876_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1876_, 0, v_a_1868_);
lean_ctor_set(v___x_1876_, 1, v___x_1873_);
lean_ctor_set(v___x_1876_, 2, v___x_1874_);
lean_ctor_set(v___x_1876_, 3, v___x_1875_);
lean_inc(v_name_1820_);
v___x_1924_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_1872_, v_name_1820_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v___x_1925_; 
v___x_1925_ = l_Lean_quoteNameMk(v_name_1820_);
v___y_1878_ = v___x_1925_;
goto v___jp_1877_;
}
else
{
lean_object* v_val_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
lean_dec(v_name_1820_);
v_val_1926_ = lean_ctor_get(v___x_1924_, 0);
lean_inc(v_val_1926_);
lean_dec_ref_known(v___x_1924_, 1);
v___x_1927_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__16));
v___x_1928_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__17));
v___x_1929_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__18));
v___x_1930_ = lean_string_intercalate(v___x_1929_, v_val_1926_);
v___x_1931_ = lean_string_append(v___x_1928_, v___x_1930_);
lean_dec_ref(v___x_1930_);
v___x_1932_ = lean_box(2);
v___x_1933_ = l_Lean_Syntax_mkNameLit(v___x_1931_, v___x_1932_);
v___x_1934_ = lean_unsigned_to_nat(1u);
v___x_1935_ = lean_mk_empty_array_with_capacity(v___x_1934_);
v___x_1936_ = lean_array_push(v___x_1935_, v___x_1933_);
v___x_1937_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1932_);
lean_ctor_set(v___x_1937_, 1, v___x_1927_);
lean_ctor_set(v___x_1937_, 2, v___x_1936_);
v___y_1878_ = v___x_1937_;
goto v___jp_1877_;
}
v___jp_1877_:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1879_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__12));
v___x_1880_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__13));
lean_inc_n(v_a_1868_, 5);
v___x_1881_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1881_, 0, v_a_1868_);
lean_ctor_set(v___x_1881_, 1, v___x_1880_);
v___x_1882_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__9));
v___x_1883_ = l_Lean_Syntax_SepArray_ofElems(v___x_1882_, v_a_1819_);
v___x_1884_ = l_Array_append___redArg(v___x_1862_, v___x_1883_);
lean_dec_ref(v___x_1883_);
v___x_1885_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1885_, 0, v_a_1868_);
lean_ctor_set(v___x_1885_, 1, v___x_1861_);
lean_ctor_set(v___x_1885_, 2, v___x_1884_);
v___x_1886_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__14));
v___x_1887_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1887_, 0, v_a_1868_);
lean_ctor_set(v___x_1887_, 1, v___x_1886_);
v___x_1888_ = l_Lean_Syntax_node3(v_a_1868_, v___x_1879_, v___x_1881_, v___x_1885_, v___x_1887_);
v___x_1889_ = l_Lean_Syntax_node2(v_a_1868_, v___x_1861_, v___y_1878_, v___x_1888_);
v___x_1890_ = l_Lean_Syntax_node2(v_a_1868_, v___x_1854_, v___x_1876_, v___x_1889_);
v___x_1891_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm(v___x_1890_, v_snd_1846_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
lean_dec(v_snd_1846_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v_a_1892_; lean_object* v___x_1893_; 
v_a_1892_ = lean_ctor_get(v___x_1891_, 0);
lean_inc(v_a_1892_);
lean_dec_ref_known(v___x_1891_, 1);
lean_inc(v___y_1828_);
lean_inc_ref(v___y_1827_);
lean_inc(v___y_1826_);
lean_inc_ref(v___y_1825_);
lean_inc(v___y_1824_);
lean_inc_ref(v___y_1823_);
v___x_1893_ = lean_apply_7(v___f_1818_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, lean_box(0));
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1915_; 
v_a_1894_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1896_ = v___x_1893_;
v_isShared_1897_ = v_isSharedCheck_1915_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1893_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1915_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; size_t v_sz_1901_; size_t v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1913_; 
v___x_1898_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__1));
v___x_1899_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__2));
lean_inc_n(v_a_1894_, 4);
v___x_1900_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1900_, 0, v_a_1894_);
lean_ctor_set(v___x_1900_, 1, v___x_1899_);
v_sz_1901_ = lean_array_size(v___x_1866_);
v___x_1902_ = ((size_t)0ULL);
v___x_1903_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__2(v_sz_1901_, v___x_1902_, v___x_1866_);
v___x_1904_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__3);
v___x_1905_ = l_Lean_mkSepArray(v___x_1903_, v___x_1904_);
lean_dec_ref(v___x_1903_);
v___x_1906_ = l_Array_append___redArg(v___x_1862_, v___x_1905_);
lean_dec_ref(v___x_1905_);
v___x_1907_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1907_, 0, v_a_1894_);
lean_ctor_set(v___x_1907_, 1, v___x_1861_);
lean_ctor_set(v___x_1907_, 2, v___x_1906_);
v___x_1908_ = l_Lean_Syntax_node1(v_a_1894_, v___x_1861_, v___x_1907_);
v___x_1909_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__4));
v___x_1910_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1910_, 0, v_a_1894_);
lean_ctor_set(v___x_1910_, 1, v___x_1909_);
v___x_1911_ = l_Lean_Syntax_node4(v_a_1894_, v___x_1898_, v___x_1900_, v___x_1908_, v___x_1910_, v_a_1892_);
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 0, v___x_1911_);
v___x_1913_ = v___x_1896_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1911_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
else
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1923_; 
lean_dec(v_a_1892_);
lean_dec_ref(v___x_1866_);
v_a_1916_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1918_ = v___x_1893_;
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1893_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1919_ == 0)
{
v___x_1921_ = v___x_1918_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1916_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
else
{
lean_dec_ref(v___x_1866_);
lean_dec_ref(v___f_1818_);
return v___x_1891_;
}
}
}
else
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
lean_dec_ref(v___x_1866_);
lean_dec(v_snd_1846_);
lean_dec(v_name_1820_);
lean_dec_ref(v___f_1818_);
v_a_1938_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1940_ = v___x_1867_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1867_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1938_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
}
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
lean_dec(v_a_1832_);
lean_dec(v_name_1820_);
lean_dec_ref(v___f_1818_);
lean_dec(v_head_1817_);
v_a_1948_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1843_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1843_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
}
}
else
{
lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
lean_dec(v_a_1832_);
lean_dec(v_name_1820_);
lean_dec_ref(v___f_1818_);
lean_dec(v_head_1817_);
lean_dec(v_auxFunName_1814_);
lean_dec(v___x_1810_);
lean_dec_ref(v_indVal_1809_);
v_a_1958_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1960_ = v___x_1834_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___x_1834_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_a_1958_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
else
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1973_; 
lean_dec(v_name_1820_);
lean_dec_ref(v___f_1818_);
lean_dec(v_head_1817_);
lean_dec(v_auxFunName_1814_);
lean_dec_ref(v___x_1811_);
lean_dec(v___x_1810_);
lean_dec_ref(v_indVal_1809_);
v_a_1966_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1968_ = v___x_1831_;
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1831_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1971_; 
if (v_isShared_1969_ == 0)
{
v___x_1971_ = v___x_1968_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1966_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_indVal_1809_ = stack[0].m_obj;
lean_object* v___x_1810_ = stack[1].m_obj;
lean_object* v___x_1811_ = stack[2].m_obj;
lean_object* v_numParams_1812_ = stack[3].m_obj;
lean_object* v_header_1813_ = stack[4].m_obj;
lean_object* v_auxFunName_1814_ = stack[5].m_obj;
lean_object* v_levelInsts_1815_ = stack[6].m_obj;
lean_object* v_numFields_1816_ = stack[7].m_obj;
lean_object* v_head_1817_ = stack[8].m_obj;
lean_object* v___f_1818_ = stack[9].m_obj;
lean_object* v_a_1819_ = stack[10].m_obj;
lean_object* v_name_1820_ = stack[11].m_obj;
lean_object* v_xs_1821_ = stack[12].m_obj;
lean_object* v_x_1822_ = stack[13].m_obj;
lean_object* v___y_1823_ = stack[14].m_obj;
lean_object* v___y_1824_ = stack[15].m_obj;
lean_object* v___y_1825_ = stack[16].m_obj;
lean_object* v___y_1826_ = stack[17].m_obj;
lean_object* v___y_1827_ = stack[18].m_obj;
lean_object* v___y_1828_ = stack[19].m_obj;
lean_object* v_res_1974_;
v_res_1974_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1(v_indVal_1809_, v___x_1810_, v___x_1811_, v_numParams_1812_, v_header_1813_, v_auxFunName_1814_, v_levelInsts_1815_, v_numFields_1816_, v_head_1817_, v___f_1818_, v_a_1819_, v_name_1820_, v_xs_1821_, v_x_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
stack->m_obj
 = v_res_1974_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_indVal_1975_ = _args[0];
lean_object* v___x_1976_ = _args[1];
lean_object* v___x_1977_ = _args[2];
lean_object* v_numParams_1978_ = _args[3];
lean_object* v_header_1979_ = _args[4];
lean_object* v_auxFunName_1980_ = _args[5];
lean_object* v_levelInsts_1981_ = _args[6];
lean_object* v_numFields_1982_ = _args[7];
lean_object* v_head_1983_ = _args[8];
lean_object* v___f_1984_ = _args[9];
lean_object* v_a_1985_ = _args[10];
lean_object* v_name_1986_ = _args[11];
lean_object* v_xs_1987_ = _args[12];
lean_object* v_x_1988_ = _args[13];
lean_object* v___y_1989_ = _args[14];
lean_object* v___y_1990_ = _args[15];
lean_object* v___y_1991_ = _args[16];
lean_object* v___y_1992_ = _args[17];
lean_object* v___y_1993_ = _args[18];
lean_object* v___y_1994_ = _args[19];
lean_object* v___y_1995_ = _args[20];
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1(v_indVal_1975_, v___x_1976_, v___x_1977_, v_numParams_1978_, v_header_1979_, v_auxFunName_1980_, v_levelInsts_1981_, v_numFields_1982_, v_head_1983_, v___f_1984_, v_a_1985_, v_name_1986_, v_xs_1987_, v_x_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
lean_dec_ref(v_x_1988_);
lean_dec_ref(v_xs_1987_);
lean_dec_ref(v_a_1985_);
lean_dec(v_numFields_1982_);
lean_dec_ref(v_levelInsts_1981_);
lean_dec_ref(v_header_1979_);
lean_dec(v_numParams_1978_);
return v_res_1996_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg(lean_object* v_a_1998_, lean_object* v_indVal_1999_, lean_object* v_auxFunName_2000_, lean_object* v_levelInsts_2001_, lean_object* v_header_2002_, lean_object* v_as_x27_2003_, lean_object* v_b_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
if (lean_obj_tag(v_as_x27_2003_) == 0)
{
lean_object* v___x_2012_; 
lean_dec_ref(v_header_2002_);
lean_dec_ref(v_levelInsts_2001_);
lean_dec(v_auxFunName_2000_);
lean_dec_ref(v_indVal_1999_);
lean_dec_ref(v_a_1998_);
v___x_2012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2012_, 0, v_b_2004_);
return v___x_2012_;
}
else
{
lean_object* v_head_2013_; lean_object* v_tail_2014_; lean_object* v___f_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v_head_2013_ = lean_ctor_get(v_as_x27_2003_, 0);
v_tail_2014_ = lean_ctor_get(v_as_x27_2003_, 1);
v___f_2015_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___closed__0));
v___x_2016_ = lean_unsigned_to_nat(0u);
v___x_2017_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__0));
lean_inc(v_head_2013_);
v___x_2018_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1(v_head_2013_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_a_2019_; lean_object* v_toConstantVal_2020_; lean_object* v_numParams_2021_; lean_object* v_numFields_2022_; lean_object* v_name_2023_; lean_object* v_type_2024_; lean_object* v___f_2025_; uint8_t v___x_2026_; lean_object* v___x_2027_; 
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_a_2019_);
lean_dec_ref_known(v___x_2018_, 1);
v_toConstantVal_2020_ = lean_ctor_get(v_a_2019_, 0);
lean_inc_ref(v_toConstantVal_2020_);
v_numParams_2021_ = lean_ctor_get(v_a_2019_, 3);
lean_inc(v_numParams_2021_);
v_numFields_2022_ = lean_ctor_get(v_a_2019_, 4);
lean_inc(v_numFields_2022_);
lean_dec(v_a_2019_);
v_name_2023_ = lean_ctor_get(v_toConstantVal_2020_, 0);
lean_inc(v_name_2023_);
v_type_2024_ = lean_ctor_get(v_toConstantVal_2020_, 2);
lean_inc_ref(v_type_2024_);
lean_dec_ref(v_toConstantVal_2020_);
lean_inc_ref(v_a_1998_);
lean_inc(v_head_2013_);
lean_inc_ref(v_levelInsts_2001_);
lean_inc(v_auxFunName_2000_);
lean_inc_ref(v_header_2002_);
lean_inc_ref(v_indVal_1999_);
v___f_2025_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___boxed), 21, 12);
lean_closure_set(v___f_2025_, 0, v_indVal_1999_);
lean_closure_set(v___f_2025_, 1, v___x_2016_);
lean_closure_set(v___f_2025_, 2, v___x_2017_);
lean_closure_set(v___f_2025_, 3, v_numParams_2021_);
lean_closure_set(v___f_2025_, 4, v_header_2002_);
lean_closure_set(v___f_2025_, 5, v_auxFunName_2000_);
lean_closure_set(v___f_2025_, 6, v_levelInsts_2001_);
lean_closure_set(v___f_2025_, 7, v_numFields_2022_);
lean_closure_set(v___f_2025_, 8, v_head_2013_);
lean_closure_set(v___f_2025_, 9, v___f_2015_);
lean_closure_set(v___f_2025_, 10, v_a_1998_);
lean_closure_set(v___f_2025_, 11, v_name_2023_);
v___x_2026_ = 0;
v___x_2027_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg(v_type_2024_, v___f_2025_, v___x_2026_, v___x_2026_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2029_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_a_2028_);
lean_dec_ref_known(v___x_2027_, 1);
v___x_2029_ = lean_array_push(v_b_2004_, v_a_2028_);
v_as_x27_2003_ = v_tail_2014_;
v_b_2004_ = v___x_2029_;
goto _start;
}
else
{
lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2038_; 
lean_dec_ref(v_b_2004_);
lean_dec_ref(v_header_2002_);
lean_dec_ref(v_levelInsts_2001_);
lean_dec(v_auxFunName_2000_);
lean_dec_ref(v_indVal_1999_);
lean_dec_ref(v_a_1998_);
v_a_2031_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2033_ = v___x_2027_;
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___x_2027_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2036_; 
if (v_isShared_2034_ == 0)
{
v___x_2036_ = v___x_2033_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2031_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
}
else
{
lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
lean_dec_ref(v_b_2004_);
lean_dec_ref(v_header_2002_);
lean_dec_ref(v_levelInsts_2001_);
lean_dec(v_auxFunName_2000_);
lean_dec_ref(v_indVal_1999_);
lean_dec_ref(v_a_1998_);
v_a_2039_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2041_ = v___x_2018_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_2018_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2042_ == 0)
{
v___x_2044_ = v___x_2041_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2039_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1998_ = stack[0].m_obj;
lean_object* v_indVal_1999_ = stack[1].m_obj;
lean_object* v_auxFunName_2000_ = stack[2].m_obj;
lean_object* v_levelInsts_2001_ = stack[3].m_obj;
lean_object* v_header_2002_ = stack[4].m_obj;
lean_object* v_as_x27_2003_ = stack[5].m_obj;
lean_object* v_b_2004_ = stack[6].m_obj;
lean_object* v___y_2005_ = stack[7].m_obj;
lean_object* v___y_2006_ = stack[8].m_obj;
lean_object* v___y_2007_ = stack[9].m_obj;
lean_object* v___y_2008_ = stack[10].m_obj;
lean_object* v___y_2009_ = stack[11].m_obj;
lean_object* v___y_2010_ = stack[12].m_obj;
lean_object* v_res_2047_;
v_res_2047_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg(v_a_1998_, v_indVal_1999_, v_auxFunName_2000_, v_levelInsts_2001_, v_header_2002_, v_as_x27_2003_, v_b_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_);
stack->m_obj
 = v_res_2047_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___boxed(lean_object* v_a_2048_, lean_object* v_indVal_2049_, lean_object* v_auxFunName_2050_, lean_object* v_levelInsts_2051_, lean_object* v_header_2052_, lean_object* v_as_x27_2053_, lean_object* v_b_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg(v_a_2048_, v_indVal_2049_, v_auxFunName_2050_, v_levelInsts_2051_, v_header_2052_, v_as_x27_2053_, v_b_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec(v_as_x27_2053_);
return v_res_2062_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__7(size_t v_sz_2063_, size_t v_i_2064_, lean_object* v_bs_2065_){
_start:
{
uint8_t v___x_2066_; 
v___x_2066_ = lean_usize_dec_lt(v_i_2064_, v_sz_2063_);
if (v___x_2066_ == 0)
{
return v_bs_2065_;
}
else
{
lean_object* v_v_2067_; lean_object* v___x_2068_; lean_object* v_bs_x27_2069_; size_t v___x_2070_; size_t v___x_2071_; lean_object* v___x_2072_; 
v_v_2067_ = lean_array_uget(v_bs_2065_, v_i_2064_);
v___x_2068_ = lean_unsigned_to_nat(0u);
v_bs_x27_2069_ = lean_array_uset(v_bs_2065_, v_i_2064_, v___x_2068_);
v___x_2070_ = ((size_t)1ULL);
v___x_2071_ = lean_usize_add(v_i_2064_, v___x_2070_);
v___x_2072_ = lean_array_uset(v_bs_x27_2069_, v_i_2064_, v_v_2067_);
v_i_2064_ = v___x_2071_;
v_bs_2065_ = v___x_2072_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__7_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2063_ = stack[0].m_num;
size_t v_i_2064_ = stack[1].m_num;
lean_object* v_bs_2065_ = stack[2].m_obj;
lean_object* v_res_2074_;
v_res_2074_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__7(v_sz_2063_, v_i_2064_, v_bs_2065_);
stack->m_obj
 = v_res_2074_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__7___boxed(lean_object* v_sz_2075_, lean_object* v_i_2076_, lean_object* v_bs_2077_){
_start:
{
size_t v_sz_boxed_2078_; size_t v_i_boxed_2079_; lean_object* v_res_2080_; 
v_sz_boxed_2078_ = lean_unbox_usize(v_sz_2075_);
lean_dec(v_sz_2075_);
v_i_boxed_2079_ = lean_unbox_usize(v_i_2076_);
lean_dec(v_i_2076_);
v_res_2080_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__7(v_sz_boxed_2078_, v_i_boxed_2079_, v_bs_2077_);
return v_res_2080_;
}
}
lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts(lean_object* v_header_2081_, lean_object* v_indVal_2082_, lean_object* v_auxFunName_2083_, lean_object* v_levelInsts_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_){
_start:
{
size_t v_sz_2092_; size_t v___x_2093_; lean_object* v___x_2094_; 
v_sz_2092_ = lean_array_size(v_levelInsts_2084_);
v___x_2093_ = ((size_t)0ULL);
lean_inc_ref(v_levelInsts_2084_);
v___x_2094_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg(v_sz_2092_, v___x_2093_, v_levelInsts_2084_, v_a_2089_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v_ctors_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2095_);
lean_dec_ref_known(v___x_2094_, 1);
v_ctors_2096_ = lean_ctor_get(v_indVal_2082_, 4);
lean_inc(v_ctors_2096_);
v___x_2097_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__0));
v___x_2098_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg(v_a_2095_, v_indVal_2082_, v_auxFunName_2083_, v_levelInsts_2084_, v_header_2081_, v_ctors_2096_, v___x_2097_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_);
lean_dec(v_ctors_2096_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2108_; 
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2101_ = v___x_2098_;
v_isShared_2102_ = v_isSharedCheck_2108_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2098_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2108_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
size_t v_sz_2103_; lean_object* v___x_2104_; lean_object* v___x_2106_; 
v_sz_2103_ = lean_array_size(v_a_2099_);
v___x_2104_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__7(v_sz_2103_, v___x_2093_, v_a_2099_);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 0, v___x_2104_);
v___x_2106_ = v___x_2101_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2104_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
else
{
return v___x_2098_;
}
}
else
{
lean_dec_ref(v_levelInsts_2084_);
lean_dec(v_auxFunName_2083_);
lean_dec_ref(v_indVal_2082_);
lean_dec_ref(v_header_2081_);
return v___x_2094_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_0interp(lean_interpreter_value* stack)
{
lean_object* v_header_2081_ = stack[0].m_obj;
lean_object* v_indVal_2082_ = stack[1].m_obj;
lean_object* v_auxFunName_2083_ = stack[2].m_obj;
lean_object* v_levelInsts_2084_ = stack[3].m_obj;
lean_object* v_a_2085_ = stack[4].m_obj;
lean_object* v_a_2086_ = stack[5].m_obj;
lean_object* v_a_2087_ = stack[6].m_obj;
lean_object* v_a_2088_ = stack[7].m_obj;
lean_object* v_a_2089_ = stack[8].m_obj;
lean_object* v_a_2090_ = stack[9].m_obj;
lean_object* v_res_2109_;
v_res_2109_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts(v_header_2081_, v_indVal_2082_, v_auxFunName_2083_, v_levelInsts_2084_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_);
stack->m_obj
 = v_res_2109_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts___boxed(lean_object* v_header_2110_, lean_object* v_indVal_2111_, lean_object* v_auxFunName_2112_, lean_object* v_levelInsts_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_){
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts(v_header_2110_, v_indVal_2111_, v_auxFunName_2112_, v_levelInsts_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
lean_dec(v_a_2119_);
lean_dec_ref(v_a_2118_);
lean_dec(v_a_2117_);
lean_dec_ref(v_a_2116_);
lean_dec(v_a_2115_);
lean_dec_ref(v_a_2114_);
return v_res_2121_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0(size_t v_sz_2122_, size_t v_i_2123_, lean_object* v_bs_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v___x_2132_; 
v___x_2132_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg(v_sz_2122_, v_i_2123_, v_bs_2124_, v___y_2129_);
return v___x_2132_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2122_ = stack[0].m_num;
size_t v_i_2123_ = stack[1].m_num;
lean_object* v_bs_2124_ = stack[2].m_obj;
lean_object* v___y_2125_ = stack[3].m_obj;
lean_object* v___y_2126_ = stack[4].m_obj;
lean_object* v___y_2127_ = stack[5].m_obj;
lean_object* v___y_2128_ = stack[6].m_obj;
lean_object* v___y_2129_ = stack[7].m_obj;
lean_object* v___y_2130_ = stack[8].m_obj;
lean_object* v_res_2133_;
v_res_2133_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0(v_sz_2122_, v_i_2123_, v_bs_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
stack->m_obj
 = v_res_2133_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___boxed(lean_object* v_sz_2134_, lean_object* v_i_2135_, lean_object* v_bs_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_){
_start:
{
size_t v_sz_boxed_2144_; size_t v_i_boxed_2145_; lean_object* v_res_2146_; 
v_sz_boxed_2144_ = lean_unbox_usize(v_sz_2134_);
lean_dec(v_sz_2134_);
v_i_boxed_2145_ = lean_unbox_usize(v_i_2135_);
lean_dec(v_i_2135_);
v_res_2146_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0(v_sz_boxed_2144_, v_i_boxed_2145_, v_bs_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_);
lean_dec(v___y_2142_);
lean_dec_ref(v___y_2141_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
return v_res_2146_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3(lean_object* v_upperBound_2147_, lean_object* v___x_2148_, lean_object* v_xs_2149_, lean_object* v_indVal_2150_, lean_object* v_auxFunName_2151_, lean_object* v_levelInsts_2152_, lean_object* v_inst_2153_, lean_object* v_R_2154_, lean_object* v_a_2155_, lean_object* v_b_2156_, lean_object* v_c_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
lean_object* v___x_2165_; 
v___x_2165_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3___redArg(v_upperBound_2147_, v___x_2148_, v_xs_2149_, v_indVal_2150_, v_auxFunName_2151_, v_levelInsts_2152_, v_a_2155_, v_b_2156_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
return v___x_2165_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2147_ = stack[0].m_obj;
lean_object* v___x_2148_ = stack[1].m_obj;
lean_object* v_xs_2149_ = stack[2].m_obj;
lean_object* v_indVal_2150_ = stack[3].m_obj;
lean_object* v_auxFunName_2151_ = stack[4].m_obj;
lean_object* v_levelInsts_2152_ = stack[5].m_obj;
lean_object* v_a_2155_ = stack[8].m_obj;
lean_object* v_b_2156_ = stack[9].m_obj;
lean_object* v___y_2158_ = stack[11].m_obj;
lean_object* v___y_2159_ = stack[12].m_obj;
lean_object* v___y_2160_ = stack[13].m_obj;
lean_object* v___y_2161_ = stack[14].m_obj;
lean_object* v___y_2162_ = stack[15].m_obj;
lean_object* v___y_2163_ = stack[16].m_obj;
lean_object* v_res_2166_;
v_res_2166_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3(v_upperBound_2147_, v___x_2148_, v_xs_2149_, v_indVal_2150_, v_auxFunName_2151_, v_levelInsts_2152_, lean_box(0), lean_box(0), v_a_2155_, v_b_2156_, lean_box(0), v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
stack->m_obj
 = v_res_2166_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3___boxed(lean_object** _args){
lean_object* v_upperBound_2167_ = _args[0];
lean_object* v___x_2168_ = _args[1];
lean_object* v_xs_2169_ = _args[2];
lean_object* v_indVal_2170_ = _args[3];
lean_object* v_auxFunName_2171_ = _args[4];
lean_object* v_levelInsts_2172_ = _args[5];
lean_object* v_inst_2173_ = _args[6];
lean_object* v_R_2174_ = _args[7];
lean_object* v_a_2175_ = _args[8];
lean_object* v_b_2176_ = _args[9];
lean_object* v_c_2177_ = _args[10];
lean_object* v___y_2178_ = _args[11];
lean_object* v___y_2179_ = _args[12];
lean_object* v___y_2180_ = _args[13];
lean_object* v___y_2181_ = _args[14];
lean_object* v___y_2182_ = _args[15];
lean_object* v___y_2183_ = _args[16];
lean_object* v___y_2184_ = _args[17];
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3(v_upperBound_2167_, v___x_2168_, v_xs_2169_, v_indVal_2170_, v_auxFunName_2171_, v_levelInsts_2172_, v_inst_2173_, v_R_2174_, v_a_2175_, v_b_2176_, v_c_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v_a_2175_);
lean_dec_ref(v_levelInsts_2172_);
lean_dec_ref(v_xs_2169_);
lean_dec(v___x_2168_);
lean_dec(v_upperBound_2167_);
return v_res_2185_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4(lean_object* v_upperBound_2186_, lean_object* v_header_2187_, lean_object* v_xs_2188_, lean_object* v_indVal_2189_, lean_object* v_auxFunName_2190_, lean_object* v_levelInsts_2191_, lean_object* v_inst_2192_, lean_object* v_R_2193_, lean_object* v_a_2194_, lean_object* v_b_2195_, lean_object* v_c_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4___redArg(v_upperBound_2186_, v_header_2187_, v_xs_2188_, v_indVal_2189_, v_auxFunName_2190_, v_levelInsts_2191_, v_a_2194_, v_b_2195_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
return v___x_2204_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2186_ = stack[0].m_obj;
lean_object* v_header_2187_ = stack[1].m_obj;
lean_object* v_xs_2188_ = stack[2].m_obj;
lean_object* v_indVal_2189_ = stack[3].m_obj;
lean_object* v_auxFunName_2190_ = stack[4].m_obj;
lean_object* v_levelInsts_2191_ = stack[5].m_obj;
lean_object* v_a_2194_ = stack[8].m_obj;
lean_object* v_b_2195_ = stack[9].m_obj;
lean_object* v___y_2197_ = stack[11].m_obj;
lean_object* v___y_2198_ = stack[12].m_obj;
lean_object* v___y_2199_ = stack[13].m_obj;
lean_object* v___y_2200_ = stack[14].m_obj;
lean_object* v___y_2201_ = stack[15].m_obj;
lean_object* v___y_2202_ = stack[16].m_obj;
lean_object* v_res_2205_;
v_res_2205_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4(v_upperBound_2186_, v_header_2187_, v_xs_2188_, v_indVal_2189_, v_auxFunName_2190_, v_levelInsts_2191_, lean_box(0), lean_box(0), v_a_2194_, v_b_2195_, lean_box(0), v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
stack->m_obj
 = v_res_2205_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_2206_ = _args[0];
lean_object* v_header_2207_ = _args[1];
lean_object* v_xs_2208_ = _args[2];
lean_object* v_indVal_2209_ = _args[3];
lean_object* v_auxFunName_2210_ = _args[4];
lean_object* v_levelInsts_2211_ = _args[5];
lean_object* v_inst_2212_ = _args[6];
lean_object* v_R_2213_ = _args[7];
lean_object* v_a_2214_ = _args[8];
lean_object* v_b_2215_ = _args[9];
lean_object* v_c_2216_ = _args[10];
lean_object* v___y_2217_ = _args[11];
lean_object* v___y_2218_ = _args[12];
lean_object* v___y_2219_ = _args[13];
lean_object* v___y_2220_ = _args[14];
lean_object* v___y_2221_ = _args[15];
lean_object* v___y_2222_ = _args[16];
lean_object* v___y_2223_ = _args[17];
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4(v_upperBound_2206_, v_header_2207_, v_xs_2208_, v_indVal_2209_, v_auxFunName_2210_, v_levelInsts_2211_, v_inst_2212_, v_R_2213_, v_a_2214_, v_b_2215_, v_c_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec(v_a_2214_);
lean_dec_ref(v_levelInsts_2211_);
lean_dec_ref(v_xs_2208_);
lean_dec_ref(v_header_2207_);
lean_dec(v_upperBound_2206_);
return v_res_2224_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5(lean_object* v_upperBound_2225_, lean_object* v_inst_2226_, lean_object* v_R_2227_, lean_object* v_a_2228_, lean_object* v_b_2229_, lean_object* v_c_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
lean_object* v___x_2238_; 
v___x_2238_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg(v_upperBound_2225_, v_a_2228_, v_b_2229_, v___y_2235_);
return v___x_2238_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2225_ = stack[0].m_obj;
lean_object* v_a_2228_ = stack[3].m_obj;
lean_object* v_b_2229_ = stack[4].m_obj;
lean_object* v___y_2231_ = stack[6].m_obj;
lean_object* v___y_2232_ = stack[7].m_obj;
lean_object* v___y_2233_ = stack[8].m_obj;
lean_object* v___y_2234_ = stack[9].m_obj;
lean_object* v___y_2235_ = stack[10].m_obj;
lean_object* v___y_2236_ = stack[11].m_obj;
lean_object* v_res_2239_;
v_res_2239_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5(v_upperBound_2225_, lean_box(0), lean_box(0), v_a_2228_, v_b_2229_, lean_box(0), v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
stack->m_obj
 = v_res_2239_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___boxed(lean_object* v_upperBound_2240_, lean_object* v_inst_2241_, lean_object* v_R_2242_, lean_object* v_a_2243_, lean_object* v_b_2244_, lean_object* v_c_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
lean_object* v_res_2253_; 
v_res_2253_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5(v_upperBound_2240_, v_inst_2241_, v_R_2242_, v_a_2243_, v_b_2244_, v_c_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v_upperBound_2240_);
return v_res_2253_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6(lean_object* v_a_2254_, lean_object* v_indVal_2255_, lean_object* v_auxFunName_2256_, lean_object* v_levelInsts_2257_, lean_object* v_header_2258_, lean_object* v_as_2259_, lean_object* v_as_x27_2260_, lean_object* v_b_2261_, lean_object* v_a_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v___x_2270_; 
v___x_2270_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg(v_a_2254_, v_indVal_2255_, v_auxFunName_2256_, v_levelInsts_2257_, v_header_2258_, v_as_x27_2260_, v_b_2261_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_);
return v___x_2270_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2254_ = stack[0].m_obj;
lean_object* v_indVal_2255_ = stack[1].m_obj;
lean_object* v_auxFunName_2256_ = stack[2].m_obj;
lean_object* v_levelInsts_2257_ = stack[3].m_obj;
lean_object* v_header_2258_ = stack[4].m_obj;
lean_object* v_as_2259_ = stack[5].m_obj;
lean_object* v_as_x27_2260_ = stack[6].m_obj;
lean_object* v_b_2261_ = stack[7].m_obj;
lean_object* v___y_2263_ = stack[9].m_obj;
lean_object* v___y_2264_ = stack[10].m_obj;
lean_object* v___y_2265_ = stack[11].m_obj;
lean_object* v___y_2266_ = stack[12].m_obj;
lean_object* v___y_2267_ = stack[13].m_obj;
lean_object* v___y_2268_ = stack[14].m_obj;
lean_object* v_res_2271_;
v_res_2271_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6(v_a_2254_, v_indVal_2255_, v_auxFunName_2256_, v_levelInsts_2257_, v_header_2258_, v_as_2259_, v_as_x27_2260_, v_b_2261_, lean_box(0), v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_);
stack->m_obj
 = v_res_2271_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___boxed(lean_object* v_a_2272_, lean_object* v_indVal_2273_, lean_object* v_auxFunName_2274_, lean_object* v_levelInsts_2275_, lean_object* v_header_2276_, lean_object* v_as_2277_, lean_object* v_as_x27_2278_, lean_object* v_b_2279_, lean_object* v_a_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6(v_a_2272_, v_indVal_2273_, v_auxFunName_2274_, v_levelInsts_2275_, v_header_2276_, v_as_2277_, v_as_x27_2278_, v_b_2279_, v_a_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v_as_x27_2278_);
lean_dec(v_as_2277_);
return v_res_2288_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4(lean_object* v_upperBound_2289_, lean_object* v___x_2290_, lean_object* v_xs_2291_, lean_object* v_indVal_2292_, lean_object* v_auxFunName_2293_, lean_object* v_levelInsts_2294_, lean_object* v_inst_2295_, lean_object* v_R_2296_, lean_object* v_a_2297_, lean_object* v_b_2298_, lean_object* v_c_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v___x_2307_; 
v___x_2307_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg(v_upperBound_2289_, v___x_2290_, v_xs_2291_, v_indVal_2292_, v_auxFunName_2293_, v_levelInsts_2294_, v_a_2297_, v_b_2298_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
return v___x_2307_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2289_ = stack[0].m_obj;
lean_object* v___x_2290_ = stack[1].m_obj;
lean_object* v_xs_2291_ = stack[2].m_obj;
lean_object* v_indVal_2292_ = stack[3].m_obj;
lean_object* v_auxFunName_2293_ = stack[4].m_obj;
lean_object* v_levelInsts_2294_ = stack[5].m_obj;
lean_object* v_a_2297_ = stack[8].m_obj;
lean_object* v_b_2298_ = stack[9].m_obj;
lean_object* v___y_2300_ = stack[11].m_obj;
lean_object* v___y_2301_ = stack[12].m_obj;
lean_object* v___y_2302_ = stack[13].m_obj;
lean_object* v___y_2303_ = stack[14].m_obj;
lean_object* v___y_2304_ = stack[15].m_obj;
lean_object* v___y_2305_ = stack[16].m_obj;
lean_object* v_res_2308_;
v_res_2308_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4(v_upperBound_2289_, v___x_2290_, v_xs_2291_, v_indVal_2292_, v_auxFunName_2293_, v_levelInsts_2294_, lean_box(0), lean_box(0), v_a_2297_, v_b_2298_, lean_box(0), v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
stack->m_obj
 = v_res_2308_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_2309_ = _args[0];
lean_object* v___x_2310_ = _args[1];
lean_object* v_xs_2311_ = _args[2];
lean_object* v_indVal_2312_ = _args[3];
lean_object* v_auxFunName_2313_ = _args[4];
lean_object* v_levelInsts_2314_ = _args[5];
lean_object* v_inst_2315_ = _args[6];
lean_object* v_R_2316_ = _args[7];
lean_object* v_a_2317_ = _args[8];
lean_object* v_b_2318_ = _args[9];
lean_object* v_c_2319_ = _args[10];
lean_object* v___y_2320_ = _args[11];
lean_object* v___y_2321_ = _args[12];
lean_object* v___y_2322_ = _args[13];
lean_object* v___y_2323_ = _args[14];
lean_object* v___y_2324_ = _args[15];
lean_object* v___y_2325_ = _args[16];
lean_object* v___y_2326_ = _args[17];
_start:
{
lean_object* v_res_2327_; 
v_res_2327_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4(v_upperBound_2309_, v___x_2310_, v_xs_2311_, v_indVal_2312_, v_auxFunName_2313_, v_levelInsts_2314_, v_inst_2315_, v_R_2316_, v_a_2317_, v_b_2318_, v_c_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec_ref(v_levelInsts_2314_);
lean_dec_ref(v_xs_2311_);
lean_dec(v___x_2310_);
lean_dec(v_upperBound_2309_);
return v_res_2327_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6(lean_object* v_upperBound_2328_, lean_object* v_header_2329_, lean_object* v_xs_2330_, lean_object* v_indVal_2331_, lean_object* v_auxFunName_2332_, lean_object* v_levelInsts_2333_, lean_object* v_inst_2334_, lean_object* v_R_2335_, lean_object* v_a_2336_, lean_object* v_b_2337_, lean_object* v_c_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v___x_2346_; 
v___x_2346_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6___redArg(v_upperBound_2328_, v_header_2329_, v_xs_2330_, v_indVal_2331_, v_auxFunName_2332_, v_levelInsts_2333_, v_a_2336_, v_b_2337_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
return v___x_2346_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2328_ = stack[0].m_obj;
lean_object* v_header_2329_ = stack[1].m_obj;
lean_object* v_xs_2330_ = stack[2].m_obj;
lean_object* v_indVal_2331_ = stack[3].m_obj;
lean_object* v_auxFunName_2332_ = stack[4].m_obj;
lean_object* v_levelInsts_2333_ = stack[5].m_obj;
lean_object* v_a_2336_ = stack[8].m_obj;
lean_object* v_b_2337_ = stack[9].m_obj;
lean_object* v___y_2339_ = stack[11].m_obj;
lean_object* v___y_2340_ = stack[12].m_obj;
lean_object* v___y_2341_ = stack[13].m_obj;
lean_object* v___y_2342_ = stack[14].m_obj;
lean_object* v___y_2343_ = stack[15].m_obj;
lean_object* v___y_2344_ = stack[16].m_obj;
lean_object* v_res_2347_;
v_res_2347_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6(v_upperBound_2328_, v_header_2329_, v_xs_2330_, v_indVal_2331_, v_auxFunName_2332_, v_levelInsts_2333_, lean_box(0), lean_box(0), v_a_2336_, v_b_2337_, lean_box(0), v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
stack->m_obj
 = v_res_2347_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6___boxed(lean_object** _args){
lean_object* v_upperBound_2348_ = _args[0];
lean_object* v_header_2349_ = _args[1];
lean_object* v_xs_2350_ = _args[2];
lean_object* v_indVal_2351_ = _args[3];
lean_object* v_auxFunName_2352_ = _args[4];
lean_object* v_levelInsts_2353_ = _args[5];
lean_object* v_inst_2354_ = _args[6];
lean_object* v_R_2355_ = _args[7];
lean_object* v_a_2356_ = _args[8];
lean_object* v_b_2357_ = _args[9];
lean_object* v_c_2358_ = _args[10];
lean_object* v___y_2359_ = _args[11];
lean_object* v___y_2360_ = _args[12];
lean_object* v___y_2361_ = _args[13];
lean_object* v___y_2362_ = _args[14];
lean_object* v___y_2363_ = _args[15];
lean_object* v___y_2364_ = _args[16];
lean_object* v___y_2365_ = _args[17];
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6(v_upperBound_2348_, v_header_2349_, v_xs_2350_, v_indVal_2351_, v_auxFunName_2352_, v_levelInsts_2353_, v_inst_2354_, v_R_2355_, v_a_2356_, v_b_2357_, v_c_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
lean_dec_ref(v_levelInsts_2353_);
lean_dec_ref(v_xs_2350_);
lean_dec_ref(v_header_2349_);
lean_dec(v_upperBound_2348_);
return v_res_2366_;
}
}
lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody(lean_object* v_header_2380_, lean_object* v_indVal_2381_, lean_object* v_auxFunName_2382_, lean_object* v_levelInsts_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_){
_start:
{
lean_object* v___x_2391_; 
lean_inc_ref(v_indVal_2381_);
lean_inc_ref(v_header_2380_);
v___x_2391_ = l_Lean_Elab_Deriving_mkDiscrs(v_header_2380_, v_indVal_2381_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v_a_2392_; lean_object* v___x_2393_; 
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
lean_inc(v_a_2392_);
lean_dec_ref_known(v___x_2391_, 1);
v___x_2393_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts(v_header_2380_, v_indVal_2381_, v_auxFunName_2382_, v_levelInsts_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2424_; 
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2396_ = v___x_2393_;
v_isShared_2397_ = v_isSharedCheck_2424_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v___x_2393_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2424_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v_ref_2398_; uint8_t v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; size_t v_sz_2407_; size_t v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2422_; 
v_ref_2398_ = lean_ctor_get(v_a_2388_, 2);
v___x_2399_ = 0;
v___x_2400_ = l_Lean_SourceInfo_fromRef(v_ref_2398_, v___x_2399_);
v___x_2401_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__0));
v___x_2402_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__1));
lean_inc_n(v___x_2400_, 6);
v___x_2403_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2400_);
lean_ctor_set(v___x_2403_, 1, v___x_2401_);
v___x_2404_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_2405_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_2406_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2400_);
lean_ctor_set(v___x_2406_, 1, v___x_2404_);
lean_ctor_set(v___x_2406_, 2, v___x_2405_);
v_sz_2407_ = lean_array_size(v_a_2392_);
v___x_2408_ = ((size_t)0ULL);
v___x_2409_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__2(v_sz_2407_, v___x_2408_, v_a_2392_);
v___x_2410_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__3);
v___x_2411_ = l_Lean_mkSepArray(v___x_2409_, v___x_2410_);
lean_dec_ref(v___x_2409_);
v___x_2412_ = l_Array_append___redArg(v___x_2405_, v___x_2411_);
lean_dec_ref(v___x_2411_);
v___x_2413_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2400_);
lean_ctor_set(v___x_2413_, 1, v___x_2404_);
lean_ctor_set(v___x_2413_, 2, v___x_2412_);
v___x_2414_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__2));
v___x_2415_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2400_);
lean_ctor_set(v___x_2415_, 1, v___x_2414_);
v___x_2416_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__4));
v___x_2417_ = l_Array_append___redArg(v___x_2405_, v_a_2394_);
lean_dec(v_a_2394_);
v___x_2418_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2400_);
lean_ctor_set(v___x_2418_, 1, v___x_2404_);
lean_ctor_set(v___x_2418_, 2, v___x_2417_);
v___x_2419_ = l_Lean_Syntax_node1(v___x_2400_, v___x_2416_, v___x_2418_);
lean_inc_ref(v___x_2406_);
v___x_2420_ = l_Lean_Syntax_node6(v___x_2400_, v___x_2402_, v___x_2403_, v___x_2406_, v___x_2406_, v___x_2413_, v___x_2415_, v___x_2419_);
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 0, v___x_2420_);
v___x_2422_ = v___x_2396_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v___x_2420_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
else
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2432_; 
lean_dec(v_a_2392_);
v_a_2425_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2427_ = v___x_2393_;
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2393_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2430_; 
if (v_isShared_2428_ == 0)
{
v___x_2430_ = v___x_2427_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_a_2425_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
}
else
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2440_; 
lean_dec_ref(v_levelInsts_2383_);
lean_dec(v_auxFunName_2382_);
lean_dec_ref(v_indVal_2381_);
lean_dec_ref(v_header_2380_);
v_a_2433_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2435_ = v___x_2391_;
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2391_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2438_; 
if (v_isShared_2436_ == 0)
{
v___x_2438_ = v___x_2435_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2433_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_0interp(lean_interpreter_value* stack)
{
lean_object* v_header_2380_ = stack[0].m_obj;
lean_object* v_indVal_2381_ = stack[1].m_obj;
lean_object* v_auxFunName_2382_ = stack[2].m_obj;
lean_object* v_levelInsts_2383_ = stack[3].m_obj;
lean_object* v_a_2384_ = stack[4].m_obj;
lean_object* v_a_2385_ = stack[5].m_obj;
lean_object* v_a_2386_ = stack[6].m_obj;
lean_object* v_a_2387_ = stack[7].m_obj;
lean_object* v_a_2388_ = stack[8].m_obj;
lean_object* v_a_2389_ = stack[9].m_obj;
lean_object* v_res_2441_;
v_res_2441_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody(v_header_2380_, v_indVal_2381_, v_auxFunName_2382_, v_levelInsts_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_);
stack->m_obj
 = v_res_2441_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___boxed(lean_object* v_header_2442_, lean_object* v_indVal_2443_, lean_object* v_auxFunName_2444_, lean_object* v_levelInsts_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_){
_start:
{
lean_object* v_res_2453_; 
v_res_2453_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody(v_header_2442_, v_indVal_2443_, v_auxFunName_2444_, v_levelInsts_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_);
lean_dec(v_a_2451_);
lean_dec_ref(v_a_2450_);
lean_dec(v_a_2449_);
lean_dec_ref(v_a_2448_);
lean_dec(v_a_2447_);
lean_dec_ref(v_a_2446_);
return v_res_2453_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__0___redArg(lean_object* v_a_2454_, lean_object* v_b_2455_){
_start:
{
lean_object* v_array_2456_; lean_object* v_start_2457_; lean_object* v_stop_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2471_; 
v_array_2456_ = lean_ctor_get(v_a_2454_, 0);
v_start_2457_ = lean_ctor_get(v_a_2454_, 1);
v_stop_2458_ = lean_ctor_get(v_a_2454_, 2);
v_isSharedCheck_2471_ = !lean_is_exclusive(v_a_2454_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2460_ = v_a_2454_;
v_isShared_2461_ = v_isSharedCheck_2471_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_stop_2458_);
lean_inc(v_start_2457_);
lean_inc(v_array_2456_);
lean_dec(v_a_2454_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2471_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
uint8_t v___x_2462_; 
v___x_2462_ = lean_nat_dec_lt(v_start_2457_, v_stop_2458_);
if (v___x_2462_ == 0)
{
lean_del_object(v___x_2460_);
lean_dec(v_stop_2458_);
lean_dec(v_start_2457_);
lean_dec_ref(v_array_2456_);
return v_b_2455_;
}
else
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2466_; 
v___x_2463_ = lean_unsigned_to_nat(1u);
v___x_2464_ = lean_nat_add(v_start_2457_, v___x_2463_);
lean_inc_ref(v_array_2456_);
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 1, v___x_2464_);
v___x_2466_ = v___x_2460_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_array_2456_);
lean_ctor_set(v_reuseFailAlloc_2470_, 1, v___x_2464_);
lean_ctor_set(v_reuseFailAlloc_2470_, 2, v_stop_2458_);
v___x_2466_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2467_ = lean_array_fget(v_array_2456_, v_start_2457_);
lean_dec(v_start_2457_);
lean_dec_ref(v_array_2456_);
v___x_2468_ = lean_array_push(v_b_2455_, v___x_2467_);
v_a_2454_ = v___x_2466_;
v_b_2455_ = v___x_2468_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__12(void){
_start:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2502_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__3));
v___x_2503_ = l_String_toRawSubstring_x27(v___x_2502_);
return v___x_2503_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1(lean_object* v_argNames_2579_, lean_object* v_levelInsts_2580_, lean_object* v_as_2581_, size_t v_sz_2582_, size_t v_i_2583_, lean_object* v_b_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_){
_start:
{
uint8_t v___x_2592_; 
v___x_2592_ = lean_usize_dec_lt(v_i_2583_, v_sz_2582_);
if (v___x_2592_ == 0)
{
lean_object* v___x_2593_; 
lean_dec_ref(v_argNames_2579_);
v___x_2593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2593_, 0, v_b_2584_);
return v___x_2593_;
}
else
{
lean_object* v_snd_2594_; lean_object* v_fst_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2768_; 
v_snd_2594_ = lean_ctor_get(v_b_2584_, 1);
v_fst_2595_ = lean_ctor_get(v_b_2584_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v_b_2584_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2597_ = v_b_2584_;
v_isShared_2598_ = v_isSharedCheck_2768_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_snd_2594_);
lean_inc(v_fst_2595_);
lean_dec(v_b_2584_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2768_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v_array_2599_; lean_object* v_start_2600_; lean_object* v_stop_2601_; uint8_t v___x_2602_; 
v_array_2599_ = lean_ctor_get(v_snd_2594_, 0);
v_start_2600_ = lean_ctor_get(v_snd_2594_, 1);
v_stop_2601_ = lean_ctor_get(v_snd_2594_, 2);
v___x_2602_ = lean_nat_dec_lt(v_start_2600_, v_stop_2601_);
if (v___x_2602_ == 0)
{
lean_object* v___x_2604_; 
lean_dec_ref(v_argNames_2579_);
if (v_isShared_2598_ == 0)
{
v___x_2604_ = v___x_2597_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_fst_2595_);
lean_ctor_set(v_reuseFailAlloc_2606_, 1, v_snd_2594_);
v___x_2604_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
lean_object* v___x_2605_; 
v___x_2605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2605_, 0, v___x_2604_);
return v___x_2605_;
}
}
else
{
lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2764_; 
lean_inc(v_stop_2601_);
lean_inc(v_start_2600_);
lean_inc_ref(v_array_2599_);
v_isSharedCheck_2764_ = !lean_is_exclusive(v_snd_2594_);
if (v_isSharedCheck_2764_ == 0)
{
lean_object* v_unused_2765_; lean_object* v_unused_2766_; lean_object* v_unused_2767_; 
v_unused_2765_ = lean_ctor_get(v_snd_2594_, 2);
lean_dec(v_unused_2765_);
v_unused_2766_ = lean_ctor_get(v_snd_2594_, 1);
lean_dec(v_unused_2766_);
v_unused_2767_ = lean_ctor_get(v_snd_2594_, 0);
lean_dec(v_unused_2767_);
v___x_2608_ = v_snd_2594_;
v_isShared_2609_ = v_isSharedCheck_2764_;
goto v_resetjp_2607_;
}
else
{
lean_dec(v_snd_2594_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2764_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v_a_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2615_; 
v_a_2610_ = lean_array_uget_borrowed(v_as_2581_, v_i_2583_);
v___x_2611_ = lean_array_fget(v_array_2599_, v_start_2600_);
v___x_2612_ = lean_unsigned_to_nat(1u);
v___x_2613_ = lean_nat_add(v_start_2600_, v___x_2612_);
lean_dec(v_start_2600_);
if (v_isShared_2609_ == 0)
{
lean_ctor_set(v___x_2608_, 1, v___x_2613_);
v___x_2615_ = v___x_2608_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_array_2599_);
lean_ctor_set(v_reuseFailAlloc_2763_, 1, v___x_2613_);
lean_ctor_set(v_reuseFailAlloc_2763_, 2, v_stop_2601_);
v___x_2615_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
lean_object* v___x_2616_; 
lean_inc(v_a_2610_);
v___x_2616_ = l_Lean_Elab_Deriving_mkInductArgNames(v_a_2610_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v_a_2617_; lean_object* v_numParams_2618_; lean_object* v_lower_2620_; lean_object* v_upper_2621_; lean_object* v___x_2752_; lean_object* v___x_2753_; uint8_t v___x_2754_; 
v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_a_2617_);
lean_dec_ref_known(v___x_2616_, 1);
v_numParams_2618_ = lean_ctor_get(v_a_2610_, 1);
v___x_2752_ = lean_unsigned_to_nat(0u);
v___x_2753_ = lean_array_get_size(v_a_2617_);
v___x_2754_ = lean_nat_dec_le(v_numParams_2618_, v___x_2752_);
if (v___x_2754_ == 0)
{
lean_inc(v_numParams_2618_);
v_lower_2620_ = v_numParams_2618_;
v_upper_2621_ = v___x_2753_;
goto v___jp_2619_;
}
else
{
v_lower_2620_ = v___x_2752_;
v_upper_2621_ = v___x_2753_;
goto v___jp_2619_;
}
v___jp_2619_:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2622_ = l_Array_toSubarray___redArg(v_a_2617_, v_lower_2620_, v_upper_2621_);
lean_inc_ref(v___x_2622_);
v___x_2623_ = l_Subarray_copy___redArg(v___x_2622_);
v___x_2624_ = l_Lean_Elab_Deriving_mkImplicitBinders(v___x_2623_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
if (lean_obj_tag(v___x_2624_) == 0)
{
lean_object* v_a_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v_a_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
v_a_2625_ = lean_ctor_get(v___x_2624_, 0);
lean_inc(v_a_2625_);
lean_dec_ref_known(v___x_2624_, 1);
v___x_2626_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2618_);
lean_inc_ref(v_argNames_2579_);
v___x_2627_ = l_Array_toSubarray___redArg(v_argNames_2579_, v___x_2626_, v_numParams_2618_);
v___x_2628_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__0));
v___x_2629_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__0___redArg(v___x_2627_, v___x_2628_);
v___x_2630_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__0___redArg(v___x_2622_, v___x_2628_);
v_a_2631_ = l_Array_append___redArg(v___x_2629_, v___x_2630_);
lean_dec_ref(v___x_2630_);
v___x_2632_ = lean_array_get_size(v_a_2631_);
v___x_2633_ = l_Array_toSubarray___redArg(v_a_2631_, v___x_2626_, v___x_2632_);
v___x_2634_ = l_Subarray_copy___redArg(v___x_2633_);
lean_inc(v_a_2610_);
v___x_2635_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v_a_2610_, v___x_2634_, v___y_2589_);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_object* v_a_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; 
v_a_2636_ = lean_ctor_get(v___x_2635_, 0);
lean_inc(v_a_2636_);
lean_dec_ref_known(v___x_2635_, 1);
v___x_2637_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__2));
v___x_2638_ = l_Lean_Core_mkFreshUserName(v___x_2637_, v___y_2589_, v___y_2590_);
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_object* v_a_2639_; lean_object* v___x_2640_; 
v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
lean_inc(v_a_2639_);
lean_dec_ref_known(v___x_2638_, 1);
lean_inc_ref(v_argNames_2579_);
lean_inc(v_a_2610_);
v___x_2640_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr(v_a_2610_, v_argNames_2579_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v_toCold_2641_; lean_object* v_a_2642_; lean_object* v_ref_2643_; lean_object* v_quotContext_2644_; lean_object* v_currMacroScope_2645_; uint8_t v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2715_; 
v_toCold_2641_ = lean_ctor_get(v___y_2589_, 0);
v_a_2642_ = lean_ctor_get(v___x_2640_, 0);
lean_inc(v_a_2642_);
lean_dec_ref_known(v___x_2640_, 1);
v_ref_2643_ = lean_ctor_get(v___y_2589_, 2);
v_quotContext_2644_ = lean_ctor_get(v_toCold_2641_, 8);
v_currMacroScope_2645_ = lean_ctor_get(v_toCold_2641_, 9);
v___x_2646_ = 0;
v___x_2647_ = l_Lean_SourceInfo_fromRef(v_ref_2643_, v___x_2646_);
v___x_2648_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__4));
v___x_2649_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__6));
v___x_2650_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__8));
v___x_2651_ = l_Lean_mkIdent(v_a_2639_);
lean_inc_n(v___x_2647_, 30);
v___x_2652_ = l_Lean_Syntax_node1(v___x_2647_, v___x_2650_, v___x_2651_);
v___x_2653_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_2654_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_2655_ = l_Array_append___redArg(v___x_2654_, v_a_2625_);
lean_dec(v_a_2625_);
v___x_2656_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2647_);
lean_ctor_set(v___x_2656_, 1, v___x_2653_);
lean_ctor_set(v___x_2656_, 2, v___x_2655_);
v___x_2657_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__10));
v___x_2658_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__11));
v___x_2659_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2647_);
lean_ctor_set(v___x_2659_, 1, v___x_2658_);
v___x_2660_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_2661_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__12);
v___x_2662_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__13));
lean_inc_n(v_currMacroScope_2645_, 3);
lean_inc_n(v_quotContext_2644_, 3);
v___x_2663_ = l_Lean_addMacroScope(v_quotContext_2644_, v___x_2662_, v_currMacroScope_2645_);
v___x_2664_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__26));
v___x_2665_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2647_);
lean_ctor_set(v___x_2665_, 1, v___x_2661_);
lean_ctor_set(v___x_2665_, 2, v___x_2663_);
lean_ctor_set(v___x_2665_, 3, v___x_2664_);
v___x_2666_ = l_Lean_Syntax_node1(v___x_2647_, v___x_2653_, v_a_2636_);
v___x_2667_ = l_Lean_Syntax_node2(v___x_2647_, v___x_2660_, v___x_2665_, v___x_2666_);
v___x_2668_ = l_Lean_Syntax_node2(v___x_2647_, v___x_2657_, v___x_2659_, v___x_2667_);
v___x_2669_ = l_Lean_Syntax_node1(v___x_2647_, v___x_2653_, v___x_2668_);
v___x_2670_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__27));
v___x_2671_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2647_);
lean_ctor_set(v___x_2671_, 1, v___x_2670_);
v___x_2672_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__29));
v___x_2673_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__30));
v___x_2674_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2647_);
lean_ctor_set(v___x_2674_, 1, v___x_2673_);
v___x_2675_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2647_);
lean_ctor_set(v___x_2675_, 1, v___x_2653_);
lean_ctor_set(v___x_2675_, 2, v___x_2654_);
v___x_2676_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__32));
v___x_2677_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__34));
v___x_2678_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__36));
v___x_2679_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1);
v___x_2680_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__2));
v___x_2681_ = l_Lean_addMacroScope(v_quotContext_2644_, v___x_2680_, v_currMacroScope_2645_);
v___x_2682_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__6));
v___x_2683_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2683_, 0, v___x_2647_);
lean_ctor_set(v___x_2683_, 1, v___x_2679_);
lean_ctor_set(v___x_2683_, 2, v___x_2681_);
lean_ctor_set(v___x_2683_, 3, v___x_2682_);
lean_inc_ref_n(v___x_2675_, 10);
v___x_2684_ = l_Lean_Syntax_node2(v___x_2647_, v___x_2678_, v___x_2683_, v___x_2675_);
v___x_2685_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__38));
v___x_2686_ = l_Lean_mkIdent(v___x_2611_);
v___x_2687_ = l_Array_append___redArg(v___x_2654_, v_levelInsts_2580_);
v___x_2688_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2688_, 0, v___x_2647_);
lean_ctor_set(v___x_2688_, 1, v___x_2653_);
lean_ctor_set(v___x_2688_, 2, v___x_2687_);
v___x_2689_ = l_Lean_Syntax_node2(v___x_2647_, v___x_2660_, v___x_2686_, v___x_2688_);
lean_inc_ref_n(v___x_2671_, 2);
v___x_2690_ = l_Lean_Syntax_node3(v___x_2647_, v___x_2685_, v___x_2671_, v___x_2675_, v___x_2689_);
v___x_2691_ = l_Lean_Syntax_node3(v___x_2647_, v___x_2653_, v___x_2675_, v___x_2675_, v___x_2690_);
v___x_2692_ = l_Lean_Syntax_node2(v___x_2647_, v___x_2677_, v___x_2684_, v___x_2691_);
v___x_2693_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__9));
v___x_2694_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2647_);
lean_ctor_set(v___x_2694_, 1, v___x_2693_);
v___x_2695_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8);
v___x_2696_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__9));
v___x_2697_ = l_Lean_addMacroScope(v_quotContext_2644_, v___x_2696_, v_currMacroScope_2645_);
v___x_2698_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__12));
v___x_2699_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2647_);
lean_ctor_set(v___x_2699_, 1, v___x_2695_);
lean_ctor_set(v___x_2699_, 2, v___x_2697_);
lean_ctor_set(v___x_2699_, 3, v___x_2698_);
v___x_2700_ = l_Lean_Syntax_node2(v___x_2647_, v___x_2678_, v___x_2699_, v___x_2675_);
v___x_2701_ = l_Lean_Syntax_node3(v___x_2647_, v___x_2685_, v___x_2671_, v___x_2675_, v_a_2642_);
v___x_2702_ = l_Lean_Syntax_node3(v___x_2647_, v___x_2653_, v___x_2675_, v___x_2675_, v___x_2701_);
v___x_2703_ = l_Lean_Syntax_node2(v___x_2647_, v___x_2677_, v___x_2700_, v___x_2702_);
v___x_2704_ = l_Lean_Syntax_node3(v___x_2647_, v___x_2653_, v___x_2692_, v___x_2694_, v___x_2703_);
v___x_2705_ = l_Lean_Syntax_node1(v___x_2647_, v___x_2676_, v___x_2704_);
v___x_2706_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__40));
v___x_2707_ = l_Lean_Syntax_node1(v___x_2647_, v___x_2706_, v___x_2675_);
v___x_2708_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__10));
v___x_2709_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2647_);
lean_ctor_set(v___x_2709_, 1, v___x_2708_);
v___x_2710_ = l_Lean_Syntax_node6(v___x_2647_, v___x_2672_, v___x_2674_, v___x_2675_, v___x_2705_, v___x_2707_, v___x_2675_, v___x_2709_);
v___x_2711_ = l_Lean_Syntax_node5(v___x_2647_, v___x_2649_, v___x_2652_, v___x_2656_, v___x_2669_, v___x_2671_, v___x_2710_);
v___x_2712_ = l_Lean_Syntax_node1(v___x_2647_, v___x_2648_, v___x_2711_);
v___x_2713_ = lean_array_push(v_fst_2595_, v___x_2712_);
if (v_isShared_2598_ == 0)
{
lean_ctor_set(v___x_2597_, 1, v___x_2615_);
lean_ctor_set(v___x_2597_, 0, v___x_2713_);
v___x_2715_ = v___x_2597_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v___x_2713_);
lean_ctor_set(v_reuseFailAlloc_2719_, 1, v___x_2615_);
v___x_2715_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
size_t v___x_2716_; size_t v___x_2717_; 
v___x_2716_ = ((size_t)1ULL);
v___x_2717_ = lean_usize_add(v_i_2583_, v___x_2716_);
v_i_2583_ = v___x_2717_;
v_b_2584_ = v___x_2715_;
goto _start;
}
}
else
{
lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
lean_dec(v_a_2639_);
lean_dec(v_a_2636_);
lean_dec(v_a_2625_);
lean_dec_ref(v___x_2615_);
lean_dec(v___x_2611_);
lean_del_object(v___x_2597_);
lean_dec(v_fst_2595_);
lean_dec_ref(v_argNames_2579_);
v_a_2720_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v___x_2640_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2640_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2725_; 
if (v_isShared_2723_ == 0)
{
v___x_2725_ = v___x_2722_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_a_2720_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
}
else
{
lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2735_; 
lean_dec(v_a_2636_);
lean_dec(v_a_2625_);
lean_dec_ref(v___x_2615_);
lean_dec(v___x_2611_);
lean_del_object(v___x_2597_);
lean_dec(v_fst_2595_);
lean_dec_ref(v_argNames_2579_);
v_a_2728_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2730_ = v___x_2638_;
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2638_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2733_; 
if (v_isShared_2731_ == 0)
{
v___x_2733_ = v___x_2730_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_a_2728_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
}
else
{
lean_object* v_a_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2743_; 
lean_dec(v_a_2625_);
lean_dec_ref(v___x_2615_);
lean_dec(v___x_2611_);
lean_del_object(v___x_2597_);
lean_dec(v_fst_2595_);
lean_dec_ref(v_argNames_2579_);
v_a_2736_ = lean_ctor_get(v___x_2635_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2738_ = v___x_2635_;
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_a_2736_);
lean_dec(v___x_2635_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v___x_2741_; 
if (v_isShared_2739_ == 0)
{
v___x_2741_ = v___x_2738_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_a_2736_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
}
}
else
{
lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2751_; 
lean_dec_ref(v___x_2622_);
lean_dec_ref(v___x_2615_);
lean_dec(v___x_2611_);
lean_del_object(v___x_2597_);
lean_dec(v_fst_2595_);
lean_dec_ref(v_argNames_2579_);
v_a_2744_ = lean_ctor_get(v___x_2624_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2746_ = v___x_2624_;
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_dec(v___x_2624_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2749_; 
if (v_isShared_2747_ == 0)
{
v___x_2749_ = v___x_2746_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_a_2744_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
}
}
else
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
lean_dec_ref(v___x_2615_);
lean_dec(v___x_2611_);
lean_del_object(v___x_2597_);
lean_dec(v_fst_2595_);
lean_dec_ref(v_argNames_2579_);
v_a_2755_ = lean_ctor_get(v___x_2616_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___x_2616_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2616_);
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
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_argNames_2579_ = stack[0].m_obj;
lean_object* v_levelInsts_2580_ = stack[1].m_obj;
lean_object* v_as_2581_ = stack[2].m_obj;
size_t v_sz_2582_ = stack[3].m_num;
size_t v_i_2583_ = stack[4].m_num;
lean_object* v_b_2584_ = stack[5].m_obj;
lean_object* v___y_2585_ = stack[6].m_obj;
lean_object* v___y_2586_ = stack[7].m_obj;
lean_object* v___y_2587_ = stack[8].m_obj;
lean_object* v___y_2588_ = stack[9].m_obj;
lean_object* v___y_2589_ = stack[10].m_obj;
lean_object* v___y_2590_ = stack[11].m_obj;
lean_object* v_res_2769_;
v_res_2769_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1(v_argNames_2579_, v_levelInsts_2580_, v_as_2581_, v_sz_2582_, v_i_2583_, v_b_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
stack->m_obj
 = v_res_2769_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___boxed(lean_object* v_argNames_2770_, lean_object* v_levelInsts_2771_, lean_object* v_as_2772_, lean_object* v_sz_2773_, lean_object* v_i_2774_, lean_object* v_b_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_){
_start:
{
size_t v_sz_boxed_2783_; size_t v_i_boxed_2784_; lean_object* v_res_2785_; 
v_sz_boxed_2783_ = lean_unbox_usize(v_sz_2773_);
lean_dec(v_sz_2773_);
v_i_boxed_2784_ = lean_unbox_usize(v_i_2774_);
lean_dec(v_i_2774_);
v_res_2785_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1(v_argNames_2770_, v_levelInsts_2771_, v_as_2772_, v_sz_boxed_2783_, v_i_boxed_2784_, v_b_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_);
lean_dec(v___y_2781_);
lean_dec_ref(v___y_2780_);
lean_dec(v___y_2779_);
lean_dec_ref(v___y_2778_);
lean_dec(v___y_2777_);
lean_dec_ref(v___y_2776_);
lean_dec_ref(v_as_2772_);
lean_dec_ref(v_levelInsts_2771_);
return v_res_2785_;
}
}
lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls(lean_object* v_ctx_2786_, lean_object* v_argNames_2787_, lean_object* v_levelInsts_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_){
_start:
{
lean_object* v_typeInfos_2796_; lean_object* v_auxFunNames_2797_; lean_object* v___x_2798_; lean_object* v_letDecls_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; size_t v_sz_2803_; size_t v___x_2804_; lean_object* v___x_2805_; 
v_typeInfos_2796_ = lean_ctor_get(v_ctx_2786_, 1);
lean_inc_ref(v_typeInfos_2796_);
v_auxFunNames_2797_ = lean_ctor_get(v_ctx_2786_, 2);
lean_inc_ref(v_auxFunNames_2797_);
lean_dec_ref(v_ctx_2786_);
v___x_2798_ = lean_unsigned_to_nat(0u);
v_letDecls_2799_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__0));
v___x_2800_ = lean_array_get_size(v_auxFunNames_2797_);
v___x_2801_ = l_Array_toSubarray___redArg(v_auxFunNames_2797_, v___x_2798_, v___x_2800_);
v___x_2802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2802_, 0, v_letDecls_2799_);
lean_ctor_set(v___x_2802_, 1, v___x_2801_);
v_sz_2803_ = lean_array_size(v_typeInfos_2796_);
v___x_2804_ = ((size_t)0ULL);
v___x_2805_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1(v_argNames_2787_, v_levelInsts_2788_, v_typeInfos_2796_, v_sz_2803_, v___x_2804_, v___x_2802_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_);
lean_dec_ref(v_typeInfos_2796_);
if (lean_obj_tag(v___x_2805_) == 0)
{
lean_object* v_a_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2814_; 
v_a_2806_ = lean_ctor_get(v___x_2805_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2808_ = v___x_2805_;
v_isShared_2809_ = v_isSharedCheck_2814_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_a_2806_);
lean_dec(v___x_2805_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2814_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v_fst_2810_; lean_object* v___x_2812_; 
v_fst_2810_ = lean_ctor_get(v_a_2806_, 0);
lean_inc(v_fst_2810_);
lean_dec(v_a_2806_);
if (v_isShared_2809_ == 0)
{
lean_ctor_set(v___x_2808_, 0, v_fst_2810_);
v___x_2812_ = v___x_2808_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_fst_2810_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
}
else
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2822_; 
v_a_2815_ = lean_ctor_get(v___x_2805_, 0);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2817_ = v___x_2805_;
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2805_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2820_; 
if (v_isShared_2818_ == 0)
{
v___x_2820_ = v___x_2817_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_a_2815_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_2786_ = stack[0].m_obj;
lean_object* v_argNames_2787_ = stack[1].m_obj;
lean_object* v_levelInsts_2788_ = stack[2].m_obj;
lean_object* v_a_2789_ = stack[3].m_obj;
lean_object* v_a_2790_ = stack[4].m_obj;
lean_object* v_a_2791_ = stack[5].m_obj;
lean_object* v_a_2792_ = stack[6].m_obj;
lean_object* v_a_2793_ = stack[7].m_obj;
lean_object* v_a_2794_ = stack[8].m_obj;
lean_object* v_res_2823_;
v_res_2823_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls(v_ctx_2786_, v_argNames_2787_, v_levelInsts_2788_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_);
stack->m_obj
 = v_res_2823_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls___boxed(lean_object* v_ctx_2824_, lean_object* v_argNames_2825_, lean_object* v_levelInsts_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls(v_ctx_2824_, v_argNames_2825_, v_levelInsts_2826_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_);
lean_dec(v_a_2832_);
lean_dec_ref(v_a_2831_);
lean_dec(v_a_2830_);
lean_dec_ref(v_a_2829_);
lean_dec(v_a_2828_);
lean_dec_ref(v_a_2827_);
lean_dec_ref(v_levelInsts_2826_);
return v_res_2834_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__0(lean_object* v_inst_2835_, lean_object* v_R_2836_, lean_object* v_a_2837_, lean_object* v_b_2838_){
_start:
{
lean_object* v___x_2839_; 
v___x_2839_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__0___redArg(v_a_2837_, v_b_2838_);
return v___x_2839_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__2(size_t v_sz_2840_, size_t v_i_2841_, lean_object* v_bs_2842_){
_start:
{
uint8_t v___x_2843_; 
v___x_2843_ = lean_usize_dec_lt(v_i_2841_, v_sz_2840_);
if (v___x_2843_ == 0)
{
return v_bs_2842_;
}
else
{
lean_object* v_v_2844_; lean_object* v___x_2845_; lean_object* v_bs_x27_2846_; size_t v___x_2847_; size_t v___x_2848_; lean_object* v___x_2849_; 
v_v_2844_ = lean_array_uget(v_bs_2842_, v_i_2841_);
v___x_2845_ = lean_unsigned_to_nat(0u);
v_bs_x27_2846_ = lean_array_uset(v_bs_2842_, v_i_2841_, v___x_2845_);
v___x_2847_ = ((size_t)1ULL);
v___x_2848_ = lean_usize_add(v_i_2841_, v___x_2847_);
v___x_2849_ = lean_array_uset(v_bs_x27_2846_, v_i_2841_, v_v_2844_);
v_i_2841_ = v___x_2848_;
v_bs_2842_ = v___x_2849_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2840_ = stack[0].m_num;
size_t v_i_2841_ = stack[1].m_num;
lean_object* v_bs_2842_ = stack[2].m_obj;
lean_object* v_res_2851_;
v_res_2851_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__2(v_sz_2840_, v_i_2841_, v_bs_2842_);
stack->m_obj
 = v_res_2851_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__2___boxed(lean_object* v_sz_2852_, lean_object* v_i_2853_, lean_object* v_bs_2854_){
_start:
{
size_t v_sz_boxed_2855_; size_t v_i_boxed_2856_; lean_object* v_res_2857_; 
v_sz_boxed_2855_ = lean_unbox_usize(v_sz_2852_);
lean_dec(v_sz_2852_);
v_i_boxed_2856_ = lean_unbox_usize(v_i_2853_);
lean_dec(v_i_2853_);
v_res_2857_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__2(v_sz_boxed_2855_, v_i_boxed_2856_, v_bs_2854_);
return v_res_2857_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2868_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__4));
v___x_2869_ = l_String_toRawSubstring_x27(v___x_2868_);
return v___x_2869_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg(size_t v_sz_2890_, size_t v_i_2891_, lean_object* v_bs_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_){
_start:
{
uint8_t v___x_2896_; 
v___x_2896_ = lean_usize_dec_lt(v_i_2891_, v_sz_2890_);
if (v___x_2896_ == 0)
{
lean_object* v___x_2897_; 
v___x_2897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2897_, 0, v_bs_2892_);
return v___x_2897_;
}
else
{
lean_object* v_v_2898_; lean_object* v___x_2899_; lean_object* v_bs_x27_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
v_v_2898_ = lean_array_uget(v_bs_2892_, v_i_2891_);
v___x_2899_ = lean_unsigned_to_nat(0u);
v_bs_x27_2900_ = lean_array_uset(v_bs_2892_, v_i_2891_, v___x_2899_);
v___x_2901_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__1));
v___x_2902_ = l_Lean_Core_mkFreshUserName(v___x_2901_, v___y_2893_, v___y_2894_);
if (lean_obj_tag(v___x_2902_) == 0)
{
lean_object* v_toCold_2903_; lean_object* v_a_2904_; lean_object* v_ref_2905_; lean_object* v_quotContext_2906_; lean_object* v_currMacroScope_2907_; lean_object* v___x_2908_; uint8_t v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; size_t v___x_2938_; size_t v___x_2939_; lean_object* v___x_2940_; 
v_toCold_2903_ = lean_ctor_get(v___y_2893_, 0);
v_a_2904_ = lean_ctor_get(v___x_2902_, 0);
lean_inc(v_a_2904_);
lean_dec_ref_known(v___x_2902_, 1);
v_ref_2905_ = lean_ctor_get(v___y_2893_, 2);
v_quotContext_2906_ = lean_ctor_get(v_toCold_2903_, 8);
v_currMacroScope_2907_ = lean_ctor_get(v_toCold_2903_, 9);
v___x_2908_ = l_Lean_mkIdent(v_a_2904_);
v___x_2909_ = 0;
v___x_2910_ = l_Lean_SourceInfo_fromRef(v_ref_2905_, v___x_2909_);
v___x_2911_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__3));
v___x_2912_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__4));
lean_inc_n(v___x_2910_, 11);
v___x_2913_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2910_);
lean_ctor_set(v___x_2913_, 1, v___x_2912_);
v___x_2914_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
lean_inc(v___x_2908_);
v___x_2915_ = l_Lean_Syntax_node1(v___x_2910_, v___x_2914_, v___x_2908_);
v___x_2916_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__11));
v___x_2917_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2917_, 0, v___x_2910_);
lean_ctor_set(v___x_2917_, 1, v___x_2916_);
v___x_2918_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__6));
v___x_2919_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__5);
v___x_2920_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__6));
lean_inc(v_currMacroScope_2907_);
lean_inc(v_quotContext_2906_);
v___x_2921_ = l_Lean_addMacroScope(v_quotContext_2906_, v___x_2920_, v_currMacroScope_2907_);
v___x_2922_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__12));
v___x_2923_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2910_);
lean_ctor_set(v___x_2923_, 1, v___x_2919_);
lean_ctor_set(v___x_2923_, 2, v___x_2921_);
lean_ctor_set(v___x_2923_, 3, v___x_2922_);
v___x_2924_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__7));
v___x_2925_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2925_, 0, v___x_2910_);
lean_ctor_set(v___x_2925_, 1, v___x_2924_);
v___x_2926_ = l_Lean_mkIdent(v_v_2898_);
v___x_2927_ = l_Lean_Syntax_node1(v___x_2910_, v___x_2914_, v___x_2926_);
v___x_2928_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__10));
v___x_2929_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2929_, 0, v___x_2910_);
lean_ctor_set(v___x_2929_, 1, v___x_2928_);
v___x_2930_ = l_Lean_Syntax_node4(v___x_2910_, v___x_2918_, v___x_2923_, v___x_2925_, v___x_2927_, v___x_2929_);
v___x_2931_ = l_Lean_Syntax_node2(v___x_2910_, v___x_2914_, v___x_2917_, v___x_2930_);
v___x_2932_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_2933_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2933_, 0, v___x_2910_);
lean_ctor_set(v___x_2933_, 1, v___x_2914_);
lean_ctor_set(v___x_2933_, 2, v___x_2932_);
v___x_2934_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__13));
v___x_2935_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2935_, 0, v___x_2910_);
lean_ctor_set(v___x_2935_, 1, v___x_2934_);
v___x_2936_ = l_Lean_Syntax_node5(v___x_2910_, v___x_2911_, v___x_2913_, v___x_2915_, v___x_2931_, v___x_2933_, v___x_2935_);
v___x_2937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2908_);
lean_ctor_set(v___x_2937_, 1, v___x_2936_);
v___x_2938_ = ((size_t)1ULL);
v___x_2939_ = lean_usize_add(v_i_2891_, v___x_2938_);
v___x_2940_ = lean_array_uset(v_bs_x27_2900_, v_i_2891_, v___x_2937_);
v_i_2891_ = v___x_2939_;
v_bs_2892_ = v___x_2940_;
goto _start;
}
else
{
lean_object* v_a_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2949_; 
lean_dec_ref(v_bs_x27_2900_);
lean_dec(v_v_2898_);
v_a_2942_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2944_ = v___x_2902_;
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_a_2942_);
lean_dec(v___x_2902_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2947_; 
if (v_isShared_2945_ == 0)
{
v___x_2947_ = v___x_2944_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_a_2942_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2890_ = stack[0].m_num;
size_t v_i_2891_ = stack[1].m_num;
lean_object* v_bs_2892_ = stack[2].m_obj;
lean_object* v___y_2893_ = stack[3].m_obj;
lean_object* v___y_2894_ = stack[4].m_obj;
lean_object* v_res_2950_;
v_res_2950_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg(v_sz_2890_, v_i_2891_, v_bs_2892_, v___y_2893_, v___y_2894_);
stack->m_obj
 = v_res_2950_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___boxed(lean_object* v_sz_2951_, lean_object* v_i_2952_, lean_object* v_bs_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_){
_start:
{
size_t v_sz_boxed_2957_; size_t v_i_boxed_2958_; lean_object* v_res_2959_; 
v_sz_boxed_2957_ = lean_unbox_usize(v_sz_2951_);
lean_dec(v_sz_2951_);
v_i_boxed_2958_ = lean_unbox_usize(v_i_2952_);
lean_dec(v_i_2952_);
v_res_2959_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg(v_sz_boxed_2957_, v_i_boxed_2958_, v_bs_2953_, v___y_2954_, v___y_2955_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
return v_res_2959_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__1(size_t v_sz_2960_, size_t v_i_2961_, lean_object* v_bs_2962_){
_start:
{
uint8_t v___x_2963_; 
v___x_2963_ = lean_usize_dec_lt(v_i_2961_, v_sz_2960_);
if (v___x_2963_ == 0)
{
return v_bs_2962_;
}
else
{
lean_object* v_v_2964_; lean_object* v___x_2965_; lean_object* v_bs_x27_2966_; size_t v___x_2967_; size_t v___x_2968_; lean_object* v___x_2969_; 
v_v_2964_ = lean_array_uget(v_bs_2962_, v_i_2961_);
v___x_2965_ = lean_unsigned_to_nat(0u);
v_bs_x27_2966_ = lean_array_uset(v_bs_2962_, v_i_2961_, v___x_2965_);
v___x_2967_ = ((size_t)1ULL);
v___x_2968_ = lean_usize_add(v_i_2961_, v___x_2967_);
v___x_2969_ = lean_array_uset(v_bs_x27_2966_, v_i_2961_, v_v_2964_);
v_i_2961_ = v___x_2968_;
v_bs_2962_ = v___x_2969_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2960_ = stack[0].m_num;
size_t v_i_2961_ = stack[1].m_num;
lean_object* v_bs_2962_ = stack[2].m_obj;
lean_object* v_res_2971_;
v_res_2971_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__1(v_sz_2960_, v_i_2961_, v_bs_2962_);
stack->m_obj
 = v_res_2971_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__1___boxed(lean_object* v_sz_2972_, lean_object* v_i_2973_, lean_object* v_bs_2974_){
_start:
{
size_t v_sz_boxed_2975_; size_t v_i_boxed_2976_; lean_object* v_res_2977_; 
v_sz_boxed_2975_ = lean_unbox_usize(v_sz_2972_);
lean_dec(v_sz_2972_);
v_i_boxed_2976_ = lean_unbox_usize(v_i_2973_);
lean_dec(v_i_2973_);
v_res_2977_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__1(v_sz_boxed_2975_, v_i_boxed_2976_, v_bs_2974_);
return v_res_2977_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__7(void){
_start:
{
lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2985_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__7));
v___x_2986_ = l_String_toRawSubstring_x27(v___x_2985_);
return v___x_2986_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20(void){
_start:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3011_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__19));
v___x_3012_ = l_Lean_stringToMessageData(v___x_3011_);
return v___x_3012_;
}
}
lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction(lean_object* v_ctx_3013_, lean_object* v_i_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_){
_start:
{
lean_object* v_typeInfos_3022_; lean_object* v_auxFunNames_3023_; uint8_t v_usePartial_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v_auxFunName_3027_; lean_object* v_indVal_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
v_typeInfos_3022_ = lean_ctor_get(v_ctx_3013_, 1);
v_auxFunNames_3023_ = lean_ctor_get(v_ctx_3013_, 2);
v_usePartial_3024_ = lean_ctor_get_uint8(v_ctx_3013_, sizeof(void*)*3);
v___x_3025_ = lean_box(0);
v___x_3026_ = l_Lean_instInhabitedInductiveVal_default;
v_auxFunName_3027_ = lean_array_get(v___x_3025_, v_auxFunNames_3023_, v_i_3014_);
v_indVal_3028_ = lean_array_get(v___x_3026_, v_typeInfos_3022_, v_i_3014_);
v___x_3029_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0));
v___x_3030_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__14));
v___x_3031_ = lean_unsigned_to_nat(1u);
lean_inc(v_indVal_3028_);
v___x_3032_ = l_Lean_Elab_Deriving_mkHeader(v___x_3030_, v___x_3031_, v_indVal_3028_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v_toConstantVal_3033_; lean_object* v_a_3034_; lean_object* v_levelParams_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3274_; 
v_toConstantVal_3033_ = lean_ctor_get(v_indVal_3028_, 0);
lean_inc_ref(v_toConstantVal_3033_);
v_a_3034_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_a_3034_);
lean_dec_ref_known(v___x_3032_, 1);
v_levelParams_3035_ = lean_ctor_get(v_toConstantVal_3033_, 1);
v_isSharedCheck_3274_ = !lean_is_exclusive(v_toConstantVal_3033_);
if (v_isSharedCheck_3274_ == 0)
{
lean_object* v_unused_3275_; lean_object* v_unused_3276_; 
v_unused_3275_ = lean_ctor_get(v_toConstantVal_3033_, 2);
lean_dec(v_unused_3275_);
v_unused_3276_ = lean_ctor_get(v_toConstantVal_3033_, 0);
lean_dec(v_unused_3276_);
v___x_3037_ = v_toConstantVal_3033_;
v_isShared_3038_ = v_isSharedCheck_3274_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_levelParams_3035_);
lean_dec(v_toConstantVal_3033_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3274_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3039_; size_t v_sz_3040_; size_t v___x_3041_; lean_object* v___x_3042_; 
v___x_3039_ = lean_array_mk(v_levelParams_3035_);
v_sz_3040_ = lean_array_size(v___x_3039_);
v___x_3041_ = ((size_t)0ULL);
v___x_3042_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg(v_sz_3040_, v___x_3041_, v___x_3039_, v_a_3019_, v_a_3020_);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3265_; 
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3045_ = v___x_3042_;
v_isShared_3046_ = v_isSharedCheck_3265_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_3042_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3265_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3047_; lean_object* v_fst_3048_; lean_object* v_snd_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3264_; 
v___x_3047_ = l_Array_unzip___redArg(v_a_3043_);
lean_dec(v_a_3043_);
v_fst_3048_ = lean_ctor_get(v___x_3047_, 0);
v_snd_3049_ = lean_ctor_get(v___x_3047_, 1);
v_isSharedCheck_3264_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3051_ = v___x_3047_;
v_isShared_3052_ = v_isSharedCheck_3264_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_snd_3049_);
lean_inc(v_fst_3048_);
lean_dec(v___x_3047_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3264_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; lean_object* v_a_3059_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v_body_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; size_t v_sz_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
v_sz_3246_ = lean_array_size(v_fst_3048_);
v___x_3247_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__2(v_sz_3246_, v___x_3041_, v_fst_3048_);
lean_inc_ref(v___x_3247_);
lean_inc(v_auxFunName_3027_);
lean_inc(v_indVal_3028_);
lean_inc(v_a_3034_);
v___x_3248_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody(v_a_3034_, v_indVal_3028_, v_auxFunName_3027_, v___x_3247_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_);
if (lean_obj_tag(v___x_3248_) == 0)
{
if (v_usePartial_3024_ == 0)
{
lean_object* v_a_3249_; 
lean_dec_ref(v___x_3247_);
lean_dec_ref(v_ctx_3013_);
v_a_3249_ = lean_ctor_get(v___x_3248_, 0);
lean_inc(v_a_3249_);
lean_dec_ref_known(v___x_3248_, 1);
v_body_3194_ = v_a_3249_;
v___y_3195_ = v_a_3015_;
v___y_3196_ = v_a_3016_;
v___y_3197_ = v_a_3017_;
v___y_3198_ = v_a_3018_;
v___y_3199_ = v_a_3019_;
v___y_3200_ = v_a_3020_;
goto v___jp_3193_;
}
else
{
lean_object* v_a_3250_; lean_object* v_argNames_3251_; lean_object* v___x_3252_; 
v_a_3250_ = lean_ctor_get(v___x_3248_, 0);
lean_inc(v_a_3250_);
lean_dec_ref_known(v___x_3248_, 1);
v_argNames_3251_ = lean_ctor_get(v_a_3034_, 1);
lean_inc_ref(v_argNames_3251_);
v___x_3252_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls(v_ctx_3013_, v_argNames_3251_, v___x_3247_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_);
lean_dec_ref(v___x_3247_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_object* v_a_3253_; lean_object* v___x_3254_; 
v_a_3253_ = lean_ctor_get(v___x_3252_, 0);
lean_inc(v_a_3253_);
lean_dec_ref_known(v___x_3252_, 1);
v___x_3254_ = l_Lean_Elab_Deriving_mkLet(v_a_3253_, v_a_3250_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_);
lean_dec(v_a_3253_);
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_object* v_a_3255_; 
v_a_3255_ = lean_ctor_get(v___x_3254_, 0);
lean_inc(v_a_3255_);
lean_dec_ref_known(v___x_3254_, 1);
v_body_3194_ = v_a_3255_;
v___y_3195_ = v_a_3015_;
v___y_3196_ = v_a_3016_;
v___y_3197_ = v_a_3017_;
v___y_3198_ = v_a_3018_;
v___y_3199_ = v_a_3019_;
v___y_3200_ = v_a_3020_;
goto v___jp_3193_;
}
else
{
lean_del_object(v___x_3051_);
lean_dec(v_snd_3049_);
lean_del_object(v___x_3045_);
lean_del_object(v___x_3037_);
lean_dec(v_a_3034_);
lean_dec(v_indVal_3028_);
lean_dec(v_auxFunName_3027_);
return v___x_3254_;
}
}
else
{
lean_object* v_a_3256_; lean_object* v___x_3258_; uint8_t v_isShared_3259_; uint8_t v_isSharedCheck_3263_; 
lean_dec(v_a_3250_);
lean_del_object(v___x_3051_);
lean_dec(v_snd_3049_);
lean_del_object(v___x_3045_);
lean_del_object(v___x_3037_);
lean_dec(v_a_3034_);
lean_dec(v_indVal_3028_);
lean_dec(v_auxFunName_3027_);
v_a_3256_ = lean_ctor_get(v___x_3252_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3258_ = v___x_3252_;
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
else
{
lean_inc(v_a_3256_);
lean_dec(v___x_3252_);
v___x_3258_ = lean_box(0);
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
v_resetjp_3257_:
{
lean_object* v___x_3261_; 
if (v_isShared_3259_ == 0)
{
v___x_3261_ = v___x_3258_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_a_3256_);
v___x_3261_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
return v___x_3261_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3247_);
lean_del_object(v___x_3051_);
lean_dec(v_snd_3049_);
lean_del_object(v___x_3045_);
lean_del_object(v___x_3037_);
lean_dec(v_a_3034_);
lean_dec(v_indVal_3028_);
lean_dec(v_auxFunName_3027_);
lean_dec_ref(v_ctx_3013_);
return v___x_3248_;
}
v___jp_3053_:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; size_t v_sz_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3060_ = lean_array_pop(v___y_3057_);
v___x_3061_ = l_Array_append___redArg(v___x_3060_, v_snd_3049_);
lean_dec(v_snd_3049_);
v___x_3062_ = lean_mk_empty_array_with_capacity(v___x_3031_);
v___x_3063_ = lean_array_push(v___x_3062_, v_a_3059_);
v_sz_3064_ = lean_array_size(v___x_3063_);
v___x_3065_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__1(v_sz_3064_, v___x_3041_, v___x_3063_);
v___x_3066_ = l_Array_append___redArg(v___x_3061_, v___x_3065_);
lean_dec_ref(v___x_3065_);
if (v_usePartial_3024_ == 0)
{
lean_object* v_toCold_3067_; lean_object* v_ref_3068_; lean_object* v_quotContext_3069_; lean_object* v_currMacroScope_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3080_; 
v_toCold_3067_ = lean_ctor_get(v___y_3054_, 0);
v_ref_3068_ = lean_ctor_get(v___y_3054_, 2);
v_quotContext_3069_ = lean_ctor_get(v_toCold_3067_, 8);
v_currMacroScope_3070_ = lean_ctor_get(v_toCold_3067_, 9);
v___x_3071_ = l_Lean_SourceInfo_fromRef(v_ref_3068_, v_usePartial_3024_);
v___x_3072_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__0));
v___x_3073_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__1));
lean_inc_ref_n(v___y_3056_, 2);
v___x_3074_ = l_Lean_Name_mkStr4(v___x_3029_, v___y_3056_, v___x_3072_, v___x_3073_);
v___x_3075_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__2));
v___x_3076_ = l_Lean_Name_mkStr4(v___x_3029_, v___y_3056_, v___x_3072_, v___x_3075_);
v___x_3077_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_3078_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
lean_inc(v___x_3071_);
if (v_isShared_3038_ == 0)
{
lean_ctor_set_tag(v___x_3037_, 1);
lean_ctor_set(v___x_3037_, 2, v___x_3078_);
lean_ctor_set(v___x_3037_, 1, v___x_3077_);
lean_ctor_set(v___x_3037_, 0, v___x_3071_);
v___x_3080_ = v___x_3037_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v___x_3071_);
lean_ctor_set(v_reuseFailAlloc_3122_, 1, v___x_3077_);
lean_ctor_set(v_reuseFailAlloc_3122_, 2, v___x_3078_);
v___x_3080_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3086_; 
lean_inc_ref_n(v___x_3080_, 7);
lean_inc_n(v___x_3071_, 2);
v___x_3081_ = l_Lean_Syntax_node7(v___x_3071_, v___x_3076_, v___x_3080_, v___x_3080_, v___x_3080_, v___x_3080_, v___x_3080_, v___x_3080_, v___x_3080_);
v___x_3082_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__3));
lean_inc_ref(v___y_3056_);
v___x_3083_ = l_Lean_Name_mkStr4(v___x_3029_, v___y_3056_, v___x_3072_, v___x_3082_);
v___x_3084_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__4));
if (v_isShared_3052_ == 0)
{
lean_ctor_set_tag(v___x_3051_, 2);
lean_ctor_set(v___x_3051_, 1, v___x_3084_);
lean_ctor_set(v___x_3051_, 0, v___x_3071_);
v___x_3086_ = v___x_3051_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v___x_3071_);
lean_ctor_set(v_reuseFailAlloc_3121_, 1, v___x_3084_);
v___x_3086_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3119_; 
v___x_3087_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__5));
lean_inc_ref_n(v___y_3056_, 5);
v___x_3088_ = l_Lean_Name_mkStr4(v___x_3029_, v___y_3056_, v___x_3072_, v___x_3087_);
v___x_3089_ = l_Lean_mkIdent(v_auxFunName_3027_);
lean_inc_ref_n(v___x_3080_, 4);
lean_inc_n(v___x_3071_, 11);
v___x_3090_ = l_Lean_Syntax_node2(v___x_3071_, v___x_3088_, v___x_3089_, v___x_3080_);
v___x_3091_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__6));
v___x_3092_ = l_Lean_Name_mkStr4(v___x_3029_, v___y_3056_, v___x_3072_, v___x_3091_);
v___x_3093_ = l_Array_append___redArg(v___x_3078_, v___x_3066_);
lean_dec_ref(v___x_3066_);
v___x_3094_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3071_);
lean_ctor_set(v___x_3094_, 1, v___x_3077_);
lean_ctor_set(v___x_3094_, 2, v___x_3093_);
v___x_3095_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__9));
lean_inc_ref(v___y_3058_);
v___x_3096_ = l_Lean_Name_mkStr4(v___x_3029_, v___y_3056_, v___y_3058_, v___x_3095_);
v___x_3097_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__11));
v___x_3098_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3071_);
lean_ctor_set(v___x_3098_, 1, v___x_3097_);
v___x_3099_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__7, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__7_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__7);
v___x_3100_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__8));
lean_inc(v_currMacroScope_3070_);
lean_inc(v_quotContext_3069_);
v___x_3101_ = l_Lean_addMacroScope(v_quotContext_3069_, v___x_3100_, v_currMacroScope_3070_);
v___x_3102_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__14));
v___x_3103_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3071_);
lean_ctor_set(v___x_3103_, 1, v___x_3099_);
lean_ctor_set(v___x_3103_, 2, v___x_3101_);
lean_ctor_set(v___x_3103_, 3, v___x_3102_);
v___x_3104_ = l_Lean_Syntax_node2(v___x_3071_, v___x_3096_, v___x_3098_, v___x_3103_);
v___x_3105_ = l_Lean_Syntax_node1(v___x_3071_, v___x_3077_, v___x_3104_);
v___x_3106_ = l_Lean_Syntax_node2(v___x_3071_, v___x_3092_, v___x_3094_, v___x_3105_);
v___x_3107_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__15));
v___x_3108_ = l_Lean_Name_mkStr4(v___x_3029_, v___y_3056_, v___x_3072_, v___x_3107_);
v___x_3109_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__27));
v___x_3110_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3110_, 0, v___x_3071_);
lean_ctor_set(v___x_3110_, 1, v___x_3109_);
v___x_3111_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__16));
v___x_3112_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__17));
v___x_3113_ = l_Lean_Name_mkStr4(v___x_3029_, v___y_3056_, v___x_3111_, v___x_3112_);
v___x_3114_ = l_Lean_Syntax_node2(v___x_3071_, v___x_3113_, v___x_3080_, v___x_3080_);
v___x_3115_ = l_Lean_Syntax_node4(v___x_3071_, v___x_3108_, v___x_3110_, v___y_3055_, v___x_3114_, v___x_3080_);
v___x_3116_ = l_Lean_Syntax_node5(v___x_3071_, v___x_3083_, v___x_3086_, v___x_3090_, v___x_3106_, v___x_3115_, v___x_3080_);
v___x_3117_ = l_Lean_Syntax_node2(v___x_3071_, v___x_3074_, v___x_3081_, v___x_3116_);
if (v_isShared_3046_ == 0)
{
lean_ctor_set(v___x_3045_, 0, v___x_3117_);
v___x_3119_ = v___x_3045_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v___x_3117_);
v___x_3119_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
return v___x_3119_;
}
}
}
}
else
{
lean_object* v_toCold_3123_; lean_object* v_ref_3124_; lean_object* v_quotContext_3125_; lean_object* v_currMacroScope_3126_; uint8_t v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3137_; 
v_toCold_3123_ = lean_ctor_get(v___y_3054_, 0);
v_ref_3124_ = lean_ctor_get(v___y_3054_, 2);
v_quotContext_3125_ = lean_ctor_get(v_toCold_3123_, 8);
v_currMacroScope_3126_ = lean_ctor_get(v_toCold_3123_, 9);
v___x_3127_ = 0;
v___x_3128_ = l_Lean_SourceInfo_fromRef(v_ref_3124_, v___x_3127_);
v___x_3129_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__0));
v___x_3130_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__1));
lean_inc_ref_n(v___y_3056_, 2);
v___x_3131_ = l_Lean_Name_mkStr4(v___x_3029_, v___y_3056_, v___x_3129_, v___x_3130_);
v___x_3132_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__2));
v___x_3133_ = l_Lean_Name_mkStr4(v___x_3029_, v___y_3056_, v___x_3129_, v___x_3132_);
v___x_3134_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_3135_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
lean_inc(v___x_3128_);
if (v_isShared_3038_ == 0)
{
lean_ctor_set_tag(v___x_3037_, 1);
lean_ctor_set(v___x_3037_, 2, v___x_3135_);
lean_ctor_set(v___x_3037_, 1, v___x_3134_);
lean_ctor_set(v___x_3037_, 0, v___x_3128_);
v___x_3137_ = v___x_3037_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v___x_3128_);
lean_ctor_set(v_reuseFailAlloc_3184_, 1, v___x_3134_);
lean_ctor_set(v_reuseFailAlloc_3184_, 2, v___x_3135_);
v___x_3137_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3141_; 
v___x_3138_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__18));
lean_inc_ref(v___y_3056_);
v___x_3139_ = l_Lean_Name_mkStr4(v___x_3029_, v___y_3056_, v___x_3129_, v___x_3138_);
lean_inc(v___x_3128_);
if (v_isShared_3052_ == 0)
{
lean_ctor_set_tag(v___x_3051_, 2);
lean_ctor_set(v___x_3051_, 1, v___x_3138_);
lean_ctor_set(v___x_3051_, 0, v___x_3128_);
v___x_3141_ = v___x_3051_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v___x_3128_);
lean_ctor_set(v_reuseFailAlloc_3183_, 1, v___x_3138_);
v___x_3141_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3181_; 
lean_inc_n(v___x_3128_, 15);
v___x_3142_ = l_Lean_Syntax_node1(v___x_3128_, v___x_3139_, v___x_3141_);
v___x_3143_ = l_Lean_Syntax_node1(v___x_3128_, v___x_3134_, v___x_3142_);
lean_inc_ref_n(v___x_3137_, 10);
v___x_3144_ = l_Lean_Syntax_node7(v___x_3128_, v___x_3133_, v___x_3137_, v___x_3137_, v___x_3137_, v___x_3137_, v___x_3137_, v___x_3137_, v___x_3143_);
v___x_3145_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__3));
lean_inc_ref_n(v___y_3056_, 6);
v___x_3146_ = l_Lean_Name_mkStr4(v___x_3029_, v___y_3056_, v___x_3129_, v___x_3145_);
v___x_3147_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__4));
v___x_3148_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3128_);
lean_ctor_set(v___x_3148_, 1, v___x_3147_);
v___x_3149_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__5));
v___x_3150_ = l_Lean_Name_mkStr4(v___x_3029_, v___y_3056_, v___x_3129_, v___x_3149_);
v___x_3151_ = l_Lean_mkIdent(v_auxFunName_3027_);
v___x_3152_ = l_Lean_Syntax_node2(v___x_3128_, v___x_3150_, v___x_3151_, v___x_3137_);
v___x_3153_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__6));
v___x_3154_ = l_Lean_Name_mkStr4(v___x_3029_, v___y_3056_, v___x_3129_, v___x_3153_);
v___x_3155_ = l_Array_append___redArg(v___x_3135_, v___x_3066_);
lean_dec_ref(v___x_3066_);
v___x_3156_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3128_);
lean_ctor_set(v___x_3156_, 1, v___x_3134_);
lean_ctor_set(v___x_3156_, 2, v___x_3155_);
v___x_3157_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__9));
lean_inc_ref(v___y_3058_);
v___x_3158_ = l_Lean_Name_mkStr4(v___x_3029_, v___y_3056_, v___y_3058_, v___x_3157_);
v___x_3159_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__11));
v___x_3160_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3128_);
lean_ctor_set(v___x_3160_, 1, v___x_3159_);
v___x_3161_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__7, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__7_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__7);
v___x_3162_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__8));
lean_inc(v_currMacroScope_3126_);
lean_inc(v_quotContext_3125_);
v___x_3163_ = l_Lean_addMacroScope(v_quotContext_3125_, v___x_3162_, v_currMacroScope_3126_);
v___x_3164_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__14));
v___x_3165_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3128_);
lean_ctor_set(v___x_3165_, 1, v___x_3161_);
lean_ctor_set(v___x_3165_, 2, v___x_3163_);
lean_ctor_set(v___x_3165_, 3, v___x_3164_);
v___x_3166_ = l_Lean_Syntax_node2(v___x_3128_, v___x_3158_, v___x_3160_, v___x_3165_);
v___x_3167_ = l_Lean_Syntax_node1(v___x_3128_, v___x_3134_, v___x_3166_);
v___x_3168_ = l_Lean_Syntax_node2(v___x_3128_, v___x_3154_, v___x_3156_, v___x_3167_);
v___x_3169_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__15));
v___x_3170_ = l_Lean_Name_mkStr4(v___x_3029_, v___y_3056_, v___x_3129_, v___x_3169_);
v___x_3171_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__27));
v___x_3172_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3128_);
lean_ctor_set(v___x_3172_, 1, v___x_3171_);
v___x_3173_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__16));
v___x_3174_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__17));
v___x_3175_ = l_Lean_Name_mkStr4(v___x_3029_, v___y_3056_, v___x_3173_, v___x_3174_);
v___x_3176_ = l_Lean_Syntax_node2(v___x_3128_, v___x_3175_, v___x_3137_, v___x_3137_);
v___x_3177_ = l_Lean_Syntax_node4(v___x_3128_, v___x_3170_, v___x_3172_, v___y_3055_, v___x_3176_, v___x_3137_);
v___x_3178_ = l_Lean_Syntax_node5(v___x_3128_, v___x_3146_, v___x_3148_, v___x_3152_, v___x_3168_, v___x_3177_, v___x_3137_);
v___x_3179_ = l_Lean_Syntax_node2(v___x_3128_, v___x_3131_, v___x_3144_, v___x_3178_);
if (v_isShared_3046_ == 0)
{
lean_ctor_set(v___x_3045_, 0, v___x_3179_);
v___x_3181_ = v___x_3045_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v___x_3179_);
v___x_3181_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
return v___x_3181_;
}
}
}
}
}
v___jp_3185_:
{
if (lean_obj_tag(v___y_3191_) == 0)
{
lean_object* v_a_3192_; 
v_a_3192_ = lean_ctor_get(v___y_3191_, 0);
lean_inc(v_a_3192_);
lean_dec_ref_known(v___y_3191_, 1);
v___y_3054_ = v___y_3186_;
v___y_3055_ = v___y_3187_;
v___y_3056_ = v___y_3188_;
v___y_3057_ = v___y_3189_;
v___y_3058_ = v___y_3190_;
v_a_3059_ = v_a_3192_;
goto v___jp_3053_;
}
else
{
lean_dec_ref(v___y_3189_);
lean_dec(v___y_3187_);
lean_del_object(v___x_3051_);
lean_dec(v_snd_3049_);
lean_del_object(v___x_3045_);
lean_del_object(v___x_3037_);
lean_dec(v_auxFunName_3027_);
return v___y_3191_;
}
}
v___jp_3193_:
{
lean_object* v_binders_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; uint8_t v___x_3209_; 
v_binders_3201_ = lean_ctor_get(v_a_3034_, 0);
lean_inc_ref(v_binders_3201_);
lean_dec(v_a_3034_);
v___x_3202_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__1));
v___x_3203_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__2));
v___x_3204_ = lean_box(0);
v___x_3205_ = lean_array_get_size(v_binders_3201_);
v___x_3206_ = lean_nat_sub(v___x_3205_, v___x_3031_);
v___x_3207_ = lean_array_get_borrowed(v___x_3204_, v_binders_3201_, v___x_3206_);
lean_dec(v___x_3206_);
v___x_3208_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__3));
lean_inc(v___x_3207_);
v___x_3209_ = l_Lean_Syntax_isOfKind(v___x_3207_, v___x_3208_);
if (v___x_3209_ == 0)
{
lean_object* v___x_3210_; lean_object* v___x_3211_; 
lean_dec(v_indVal_3028_);
v___x_3210_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20);
v___x_3211_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v___x_3210_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_);
v___y_3186_ = v___y_3199_;
v___y_3187_ = v_body_3194_;
v___y_3188_ = v___x_3202_;
v___y_3189_ = v_binders_3201_;
v___y_3190_ = v___x_3203_;
v___y_3191_ = v___x_3211_;
goto v___jp_3185_;
}
else
{
lean_object* v___x_3212_; uint8_t v___x_3213_; 
v___x_3212_ = l_Lean_Syntax_getArg(v___x_3207_, v___x_3031_);
lean_inc(v___x_3212_);
v___x_3213_ = l_Lean_Syntax_matchesNull(v___x_3212_, v___x_3031_);
if (v___x_3213_ == 0)
{
lean_object* v___x_3214_; lean_object* v___x_3215_; 
lean_dec(v___x_3212_);
lean_dec(v_indVal_3028_);
v___x_3214_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20);
v___x_3215_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v___x_3214_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_);
v___y_3186_ = v___y_3199_;
v___y_3187_ = v_body_3194_;
v___y_3188_ = v___x_3202_;
v___y_3189_ = v_binders_3201_;
v___y_3190_ = v___x_3203_;
v___y_3191_ = v___x_3215_;
goto v___jp_3185_;
}
else
{
lean_object* v___x_3216_; lean_object* v___x_3217_; uint8_t v___x_3218_; 
v___x_3216_ = lean_unsigned_to_nat(2u);
v___x_3217_ = l_Lean_Syntax_getArg(v___x_3207_, v___x_3216_);
lean_inc(v___x_3217_);
v___x_3218_ = l_Lean_Syntax_matchesNull(v___x_3217_, v___x_3216_);
if (v___x_3218_ == 0)
{
lean_object* v___x_3219_; lean_object* v___x_3220_; 
lean_dec(v___x_3217_);
lean_dec(v___x_3212_);
lean_dec(v_indVal_3028_);
v___x_3219_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20);
v___x_3220_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v___x_3219_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_);
v___y_3186_ = v___y_3199_;
v___y_3187_ = v_body_3194_;
v___y_3188_ = v___x_3202_;
v___y_3189_ = v_binders_3201_;
v___y_3190_ = v___x_3203_;
v___y_3191_ = v___x_3220_;
goto v___jp_3185_;
}
else
{
lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; uint8_t v___x_3224_; 
v___x_3221_ = lean_unsigned_to_nat(0u);
v___x_3222_ = lean_unsigned_to_nat(3u);
v___x_3223_ = l_Lean_Syntax_getArg(v___x_3207_, v___x_3222_);
v___x_3224_ = l_Lean_Syntax_matchesNull(v___x_3223_, v___x_3221_);
if (v___x_3224_ == 0)
{
lean_object* v___x_3225_; lean_object* v___x_3226_; 
lean_dec(v___x_3217_);
lean_dec(v___x_3212_);
lean_dec(v_indVal_3028_);
v___x_3225_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20);
v___x_3226_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v___x_3225_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_);
v___y_3186_ = v___y_3199_;
v___y_3187_ = v_body_3194_;
v___y_3188_ = v___x_3202_;
v___y_3189_ = v_binders_3201_;
v___y_3190_ = v___x_3203_;
v___y_3191_ = v___x_3226_;
goto v___jp_3185_;
}
else
{
lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
v___x_3227_ = l_Lean_Syntax_getArg(v___x_3212_, v___x_3221_);
lean_dec(v___x_3212_);
v___x_3228_ = l_Lean_Syntax_getArg(v___x_3217_, v___x_3031_);
lean_dec(v___x_3217_);
v___x_3229_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType(v_indVal_3028_, v___x_3228_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_);
if (lean_obj_tag(v___x_3229_) == 0)
{
lean_object* v_a_3230_; lean_object* v_ref_3231_; uint8_t v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; 
v_a_3230_ = lean_ctor_get(v___x_3229_, 0);
lean_inc(v_a_3230_);
lean_dec_ref_known(v___x_3229_, 1);
v_ref_3231_ = lean_ctor_get(v___y_3199_, 2);
v___x_3232_ = 0;
v___x_3233_ = l_Lean_SourceInfo_fromRef(v_ref_3231_, v___x_3232_);
v___x_3234_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__4));
lean_inc_n(v___x_3233_, 6);
v___x_3235_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3235_, 0, v___x_3233_);
lean_ctor_set(v___x_3235_, 1, v___x_3234_);
v___x_3236_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_3237_ = l_Lean_Syntax_node1(v___x_3233_, v___x_3236_, v___x_3227_);
v___x_3238_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__11));
v___x_3239_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3239_, 0, v___x_3233_);
lean_ctor_set(v___x_3239_, 1, v___x_3238_);
v___x_3240_ = l_Lean_Syntax_node2(v___x_3233_, v___x_3236_, v___x_3239_, v_a_3230_);
v___x_3241_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_3242_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3233_);
lean_ctor_set(v___x_3242_, 1, v___x_3236_);
lean_ctor_set(v___x_3242_, 2, v___x_3241_);
v___x_3243_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__13));
v___x_3244_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3244_, 0, v___x_3233_);
lean_ctor_set(v___x_3244_, 1, v___x_3243_);
v___x_3245_ = l_Lean_Syntax_node5(v___x_3233_, v___x_3208_, v___x_3235_, v___x_3237_, v___x_3240_, v___x_3242_, v___x_3244_);
v___y_3054_ = v___y_3199_;
v___y_3055_ = v_body_3194_;
v___y_3056_ = v___x_3202_;
v___y_3057_ = v_binders_3201_;
v___y_3058_ = v___x_3203_;
v_a_3059_ = v___x_3245_;
goto v___jp_3053_;
}
else
{
lean_dec(v___x_3227_);
v___y_3186_ = v___y_3199_;
v___y_3187_ = v_body_3194_;
v___y_3188_ = v___x_3202_;
v___y_3189_ = v_binders_3201_;
v___y_3190_ = v___x_3203_;
v___y_3191_ = v___x_3229_;
goto v___jp_3185_;
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
lean_object* v_a_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3273_; 
lean_del_object(v___x_3037_);
lean_dec(v_a_3034_);
lean_dec(v_indVal_3028_);
lean_dec(v_auxFunName_3027_);
lean_dec_ref(v_ctx_3013_);
v_a_3266_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3273_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3268_ = v___x_3042_;
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_a_3266_);
lean_dec(v___x_3042_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v___x_3271_; 
if (v_isShared_3269_ == 0)
{
v___x_3271_ = v___x_3268_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_a_3266_);
v___x_3271_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
return v___x_3271_;
}
}
}
}
}
else
{
lean_object* v_a_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3284_; 
lean_dec(v_indVal_3028_);
lean_dec(v_auxFunName_3027_);
lean_dec_ref(v_ctx_3013_);
v_a_3277_ = lean_ctor_get(v___x_3032_, 0);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3279_ = v___x_3032_;
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_a_3277_);
lean_dec(v___x_3032_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
lean_object* v___x_3282_; 
if (v_isShared_3280_ == 0)
{
v___x_3282_ = v___x_3279_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v_a_3277_);
v___x_3282_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
return v___x_3282_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_3013_ = stack[0].m_obj;
lean_object* v_i_3014_ = stack[1].m_obj;
lean_object* v_a_3015_ = stack[2].m_obj;
lean_object* v_a_3016_ = stack[3].m_obj;
lean_object* v_a_3017_ = stack[4].m_obj;
lean_object* v_a_3018_ = stack[5].m_obj;
lean_object* v_a_3019_ = stack[6].m_obj;
lean_object* v_a_3020_ = stack[7].m_obj;
lean_object* v_res_3285_;
v_res_3285_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction(v_ctx_3013_, v_i_3014_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_);
stack->m_obj
 = v_res_3285_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___boxed(lean_object* v_ctx_3286_, lean_object* v_i_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_){
_start:
{
lean_object* v_res_3295_; 
v_res_3295_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction(v_ctx_3286_, v_i_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_);
lean_dec(v_a_3293_);
lean_dec_ref(v_a_3292_);
lean_dec(v_a_3291_);
lean_dec_ref(v_a_3290_);
lean_dec(v_a_3289_);
lean_dec_ref(v_a_3288_);
lean_dec(v_i_3287_);
return v_res_3295_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0(size_t v_sz_3296_, size_t v_i_3297_, lean_object* v_bs_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_){
_start:
{
lean_object* v___x_3306_; 
v___x_3306_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg(v_sz_3296_, v_i_3297_, v_bs_3298_, v___y_3303_, v___y_3304_);
return v___x_3306_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3296_ = stack[0].m_num;
size_t v_i_3297_ = stack[1].m_num;
lean_object* v_bs_3298_ = stack[2].m_obj;
lean_object* v___y_3299_ = stack[3].m_obj;
lean_object* v___y_3300_ = stack[4].m_obj;
lean_object* v___y_3301_ = stack[5].m_obj;
lean_object* v___y_3302_ = stack[6].m_obj;
lean_object* v___y_3303_ = stack[7].m_obj;
lean_object* v___y_3304_ = stack[8].m_obj;
lean_object* v_res_3307_;
v_res_3307_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0(v_sz_3296_, v_i_3297_, v_bs_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_);
stack->m_obj
 = v_res_3307_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___boxed(lean_object* v_sz_3308_, lean_object* v_i_3309_, lean_object* v_bs_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_){
_start:
{
size_t v_sz_boxed_3318_; size_t v_i_boxed_3319_; lean_object* v_res_3320_; 
v_sz_boxed_3318_ = lean_unbox_usize(v_sz_3308_);
lean_dec(v_sz_3308_);
v_i_boxed_3319_ = lean_unbox_usize(v_i_3309_);
lean_dec(v_i_3309_);
v_res_3320_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0(v_sz_boxed_3318_, v_i_boxed_3319_, v_bs_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_);
lean_dec(v___y_3316_);
lean_dec_ref(v___y_3315_);
lean_dec(v___y_3314_);
lean_dec_ref(v___y_3313_);
lean_dec(v___y_3312_);
lean_dec_ref(v___y_3311_);
return v_res_3320_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0___redArg(lean_object* v_upperBound_3321_, lean_object* v_ctx_3322_, lean_object* v_a_3323_, lean_object* v_b_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_){
_start:
{
uint8_t v___x_3332_; 
v___x_3332_ = lean_nat_dec_lt(v_a_3323_, v_upperBound_3321_);
if (v___x_3332_ == 0)
{
lean_object* v___x_3333_; 
lean_dec(v_a_3323_);
lean_dec_ref(v_ctx_3322_);
v___x_3333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3333_, 0, v_b_3324_);
return v___x_3333_;
}
else
{
lean_object* v___x_3334_; 
lean_inc_ref(v_ctx_3322_);
v___x_3334_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction(v_ctx_3322_, v_a_3323_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_);
if (lean_obj_tag(v___x_3334_) == 0)
{
lean_object* v_a_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
v_a_3335_ = lean_ctor_get(v___x_3334_, 0);
lean_inc(v_a_3335_);
lean_dec_ref_known(v___x_3334_, 1);
v___x_3336_ = lean_array_push(v_b_3324_, v_a_3335_);
v___x_3337_ = lean_unsigned_to_nat(1u);
v___x_3338_ = lean_nat_add(v_a_3323_, v___x_3337_);
lean_dec(v_a_3323_);
v_a_3323_ = v___x_3338_;
v_b_3324_ = v___x_3336_;
goto _start;
}
else
{
lean_object* v_a_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3347_; 
lean_dec_ref(v_b_3324_);
lean_dec(v_a_3323_);
lean_dec_ref(v_ctx_3322_);
v_a_3340_ = lean_ctor_get(v___x_3334_, 0);
v_isSharedCheck_3347_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3342_ = v___x_3334_;
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_a_3340_);
lean_dec(v___x_3334_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v___x_3345_; 
if (v_isShared_3343_ == 0)
{
v___x_3345_ = v___x_3342_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_a_3340_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
return v___x_3345_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_3321_ = stack[0].m_obj;
lean_object* v_ctx_3322_ = stack[1].m_obj;
lean_object* v_a_3323_ = stack[2].m_obj;
lean_object* v_b_3324_ = stack[3].m_obj;
lean_object* v___y_3325_ = stack[4].m_obj;
lean_object* v___y_3326_ = stack[5].m_obj;
lean_object* v___y_3327_ = stack[6].m_obj;
lean_object* v___y_3328_ = stack[7].m_obj;
lean_object* v___y_3329_ = stack[8].m_obj;
lean_object* v___y_3330_ = stack[9].m_obj;
lean_object* v_res_3348_;
v_res_3348_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0___redArg(v_upperBound_3321_, v_ctx_3322_, v_a_3323_, v_b_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_);
stack->m_obj
 = v_res_3348_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0___redArg___boxed(lean_object* v_upperBound_3349_, lean_object* v_ctx_3350_, lean_object* v_a_3351_, lean_object* v_b_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_){
_start:
{
lean_object* v_res_3360_; 
v_res_3360_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0___redArg(v_upperBound_3349_, v_ctx_3350_, v_a_3351_, v_b_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
lean_dec(v___y_3358_);
lean_dec_ref(v___y_3357_);
lean_dec(v___y_3356_);
lean_dec_ref(v___y_3355_);
lean_dec(v___y_3354_);
lean_dec_ref(v___y_3353_);
lean_dec(v_upperBound_3349_);
return v_res_3360_;
}
}
lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions(lean_object* v_ctx_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_){
_start:
{
lean_object* v_typeInfos_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v_auxDefs_3379_; lean_object* v___x_3380_; 
v_typeInfos_3376_ = lean_ctor_get(v_ctx_3368_, 1);
v___x_3377_ = lean_array_get_size(v_typeInfos_3376_);
v___x_3378_ = lean_unsigned_to_nat(0u);
v_auxDefs_3379_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__0));
v___x_3380_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0___redArg(v___x_3377_, v_ctx_3368_, v___x_3378_, v_auxDefs_3379_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_);
if (lean_obj_tag(v___x_3380_) == 0)
{
lean_object* v_a_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3401_; 
v_a_3381_ = lean_ctor_get(v___x_3380_, 0);
v_isSharedCheck_3401_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3383_ = v___x_3380_;
v_isShared_3384_ = v_isSharedCheck_3401_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_a_3381_);
lean_dec(v___x_3380_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3401_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v_ref_3385_; uint8_t v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3399_; 
v_ref_3385_ = lean_ctor_get(v_a_3373_, 2);
v___x_3386_ = 0;
v___x_3387_ = l_Lean_SourceInfo_fromRef(v_ref_3385_, v___x_3386_);
v___x_3388_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions___closed__0));
v___x_3389_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions___closed__1));
lean_inc_n(v___x_3387_, 3);
v___x_3390_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3387_);
lean_ctor_set(v___x_3390_, 1, v___x_3388_);
v___x_3391_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_3392_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_3393_ = l_Array_append___redArg(v___x_3392_, v_a_3381_);
lean_dec(v_a_3381_);
v___x_3394_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3394_, 0, v___x_3387_);
lean_ctor_set(v___x_3394_, 1, v___x_3391_);
lean_ctor_set(v___x_3394_, 2, v___x_3393_);
v___x_3395_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions___closed__2));
v___x_3396_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3387_);
lean_ctor_set(v___x_3396_, 1, v___x_3395_);
v___x_3397_ = l_Lean_Syntax_node3(v___x_3387_, v___x_3389_, v___x_3390_, v___x_3394_, v___x_3396_);
if (v_isShared_3384_ == 0)
{
lean_ctor_set(v___x_3383_, 0, v___x_3397_);
v___x_3399_ = v___x_3383_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v___x_3397_);
v___x_3399_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
return v___x_3399_;
}
}
}
else
{
lean_object* v_a_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3409_; 
v_a_3402_ = lean_ctor_get(v___x_3380_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3404_ = v___x_3380_;
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_a_3402_);
lean_dec(v___x_3380_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3407_; 
if (v_isShared_3405_ == 0)
{
v___x_3407_ = v___x_3404_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_a_3402_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_3368_ = stack[0].m_obj;
lean_object* v_a_3369_ = stack[1].m_obj;
lean_object* v_a_3370_ = stack[2].m_obj;
lean_object* v_a_3371_ = stack[3].m_obj;
lean_object* v_a_3372_ = stack[4].m_obj;
lean_object* v_a_3373_ = stack[5].m_obj;
lean_object* v_a_3374_ = stack[6].m_obj;
lean_object* v_res_3410_;
v_res_3410_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions(v_ctx_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_);
stack->m_obj
 = v_res_3410_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions___boxed(lean_object* v_ctx_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_){
_start:
{
lean_object* v_res_3419_; 
v_res_3419_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions(v_ctx_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
lean_dec(v_a_3417_);
lean_dec_ref(v_a_3416_);
lean_dec(v_a_3415_);
lean_dec_ref(v_a_3414_);
lean_dec(v_a_3413_);
lean_dec_ref(v_a_3412_);
return v_res_3419_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0(lean_object* v_upperBound_3420_, lean_object* v_ctx_3421_, lean_object* v_inst_3422_, lean_object* v_R_3423_, lean_object* v_a_3424_, lean_object* v_b_3425_, lean_object* v_c_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_){
_start:
{
lean_object* v___x_3434_; 
v___x_3434_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0___redArg(v_upperBound_3420_, v_ctx_3421_, v_a_3424_, v_b_3425_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_);
return v___x_3434_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_3420_ = stack[0].m_obj;
lean_object* v_ctx_3421_ = stack[1].m_obj;
lean_object* v_a_3424_ = stack[4].m_obj;
lean_object* v_b_3425_ = stack[5].m_obj;
lean_object* v___y_3427_ = stack[7].m_obj;
lean_object* v___y_3428_ = stack[8].m_obj;
lean_object* v___y_3429_ = stack[9].m_obj;
lean_object* v___y_3430_ = stack[10].m_obj;
lean_object* v___y_3431_ = stack[11].m_obj;
lean_object* v___y_3432_ = stack[12].m_obj;
lean_object* v_res_3435_;
v_res_3435_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0(v_upperBound_3420_, v_ctx_3421_, lean_box(0), lean_box(0), v_a_3424_, v_b_3425_, lean_box(0), v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_);
stack->m_obj
 = v_res_3435_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0___boxed(lean_object* v_upperBound_3436_, lean_object* v_ctx_3437_, lean_object* v_inst_3438_, lean_object* v_R_3439_, lean_object* v_a_3440_, lean_object* v_b_3441_, lean_object* v_c_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_){
_start:
{
lean_object* v_res_3450_; 
v_res_3450_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0(v_upperBound_3436_, v_ctx_3437_, v_inst_3438_, v_R_3439_, v_a_3440_, v_b_3441_, v_c_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
lean_dec(v___y_3448_);
lean_dec_ref(v___y_3447_);
lean_dec(v___y_3446_);
lean_dec_ref(v___y_3445_);
lean_dec(v___y_3444_);
lean_dec_ref(v___y_3443_);
lean_dec(v_upperBound_3436_);
return v_res_3450_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0_spec__0(lean_object* v_a_3451_, lean_object* v_as_3452_, size_t v_i_3453_, size_t v_stop_3454_){
_start:
{
uint8_t v___x_3455_; 
v___x_3455_ = lean_usize_dec_eq(v_i_3453_, v_stop_3454_);
if (v___x_3455_ == 0)
{
lean_object* v___x_3456_; uint8_t v___x_3457_; 
v___x_3456_ = lean_array_uget_borrowed(v_as_3452_, v_i_3453_);
v___x_3457_ = lean_name_eq(v_a_3451_, v___x_3456_);
if (v___x_3457_ == 0)
{
size_t v___x_3458_; size_t v___x_3459_; 
v___x_3458_ = ((size_t)1ULL);
v___x_3459_ = lean_usize_add(v_i_3453_, v___x_3458_);
v_i_3453_ = v___x_3459_;
goto _start;
}
else
{
return v___x_3457_;
}
}
else
{
uint8_t v___x_3461_; 
v___x_3461_ = 0;
return v___x_3461_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3451_ = stack[0].m_obj;
lean_object* v_as_3452_ = stack[1].m_obj;
size_t v_i_3453_ = stack[2].m_num;
size_t v_stop_3454_ = stack[3].m_num;
uint8_t v_res_3462_;
v_res_3462_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0_spec__0(v_a_3451_, v_as_3452_, v_i_3453_, v_stop_3454_);
stack->m_num = v_res_3462_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0_spec__0___boxed(lean_object* v_a_3463_, lean_object* v_as_3464_, lean_object* v_i_3465_, lean_object* v_stop_3466_){
_start:
{
size_t v_i_boxed_3467_; size_t v_stop_boxed_3468_; uint8_t v_res_3469_; lean_object* v_r_3470_; 
v_i_boxed_3467_ = lean_unbox_usize(v_i_3465_);
lean_dec(v_i_3465_);
v_stop_boxed_3468_ = lean_unbox_usize(v_stop_3466_);
lean_dec(v_stop_3466_);
v_res_3469_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0_spec__0(v_a_3463_, v_as_3464_, v_i_boxed_3467_, v_stop_boxed_3468_);
lean_dec_ref(v_as_3464_);
lean_dec(v_a_3463_);
v_r_3470_ = lean_box(v_res_3469_);
return v_r_3470_;
}
}
uint8_t l_Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0(lean_object* v_as_3471_, lean_object* v_a_3472_){
_start:
{
lean_object* v___x_3473_; lean_object* v___x_3474_; uint8_t v___x_3475_; 
v___x_3473_ = lean_unsigned_to_nat(0u);
v___x_3474_ = lean_array_get_size(v_as_3471_);
v___x_3475_ = lean_nat_dec_lt(v___x_3473_, v___x_3474_);
if (v___x_3475_ == 0)
{
return v___x_3475_;
}
else
{
if (v___x_3475_ == 0)
{
return v___x_3475_;
}
else
{
size_t v___x_3476_; size_t v___x_3477_; uint8_t v___x_3478_; 
v___x_3476_ = ((size_t)0ULL);
v___x_3477_ = lean_usize_of_nat(v___x_3474_);
v___x_3478_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0_spec__0(v_a_3472_, v_as_3471_, v___x_3476_, v___x_3477_);
return v___x_3478_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3471_ = stack[0].m_obj;
lean_object* v_a_3472_ = stack[1].m_obj;
uint8_t v_res_3479_;
v_res_3479_ = l_Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0(v_as_3471_, v_a_3472_);
stack->m_num = v_res_3479_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0___boxed(lean_object* v_as_3480_, lean_object* v_a_3481_){
_start:
{
uint8_t v_res_3482_; lean_object* v_r_3483_; 
v_res_3482_ = l_Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0(v_as_3480_, v_a_3481_);
lean_dec(v_a_3481_);
lean_dec_ref(v_as_3480_);
v_r_3483_ = lean_box(v_res_3482_);
return v_r_3483_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg(size_t v_sz_3490_, size_t v_i_3491_, lean_object* v_bs_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_){
_start:
{
uint8_t v___x_3496_; 
v___x_3496_ = lean_usize_dec_lt(v_i_3491_, v_sz_3490_);
if (v___x_3496_ == 0)
{
lean_object* v___x_3497_; 
v___x_3497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3497_, 0, v_bs_3492_);
return v___x_3497_;
}
else
{
lean_object* v_v_3498_; lean_object* v___x_3499_; lean_object* v_bs_x27_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; 
v_v_3498_ = lean_array_uget(v_bs_3492_, v_i_3491_);
v___x_3499_ = lean_unsigned_to_nat(0u);
v_bs_x27_3500_ = lean_array_uset(v_bs_3492_, v_i_3491_, v___x_3499_);
v___x_3501_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__1));
v___x_3502_ = l_Lean_Core_mkFreshUserName(v___x_3501_, v___y_3493_, v___y_3494_);
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_object* v_toCold_3503_; lean_object* v_a_3504_; lean_object* v_ref_3505_; lean_object* v_quotContext_3506_; lean_object* v_currMacroScope_3507_; lean_object* v___x_3508_; uint8_t v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; size_t v___x_3535_; size_t v___x_3536_; lean_object* v___x_3537_; 
v_toCold_3503_ = lean_ctor_get(v___y_3493_, 0);
v_a_3504_ = lean_ctor_get(v___x_3502_, 0);
lean_inc(v_a_3504_);
lean_dec_ref_known(v___x_3502_, 1);
v_ref_3505_ = lean_ctor_get(v___y_3493_, 2);
v_quotContext_3506_ = lean_ctor_get(v_toCold_3503_, 8);
v_currMacroScope_3507_ = lean_ctor_get(v_toCold_3503_, 9);
v___x_3508_ = l_Lean_mkIdent(v_a_3504_);
v___x_3509_ = 0;
v___x_3510_ = l_Lean_SourceInfo_fromRef(v_ref_3505_, v___x_3509_);
v___x_3511_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg___closed__1));
v___x_3512_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__13));
lean_inc_n(v___x_3510_, 9);
v___x_3513_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3513_, 0, v___x_3510_);
lean_ctor_set(v___x_3513_, 1, v___x_3512_);
v___x_3514_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_3515_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__11));
v___x_3516_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3516_, 0, v___x_3510_);
lean_ctor_set(v___x_3516_, 1, v___x_3515_);
lean_inc(v___x_3508_);
v___x_3517_ = l_Lean_Syntax_node2(v___x_3510_, v___x_3514_, v___x_3508_, v___x_3516_);
v___x_3518_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__6));
v___x_3519_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__5);
v___x_3520_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__6));
lean_inc(v_currMacroScope_3507_);
lean_inc(v_quotContext_3506_);
v___x_3521_ = l_Lean_addMacroScope(v_quotContext_3506_, v___x_3520_, v_currMacroScope_3507_);
v___x_3522_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__12));
v___x_3523_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3523_, 0, v___x_3510_);
lean_ctor_set(v___x_3523_, 1, v___x_3519_);
lean_ctor_set(v___x_3523_, 2, v___x_3521_);
lean_ctor_set(v___x_3523_, 3, v___x_3522_);
v___x_3524_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__7));
v___x_3525_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3525_, 0, v___x_3510_);
lean_ctor_set(v___x_3525_, 1, v___x_3524_);
v___x_3526_ = l_Lean_mkIdent(v_v_3498_);
v___x_3527_ = l_Lean_Syntax_node1(v___x_3510_, v___x_3514_, v___x_3526_);
v___x_3528_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__10));
v___x_3529_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3529_, 0, v___x_3510_);
lean_ctor_set(v___x_3529_, 1, v___x_3528_);
v___x_3530_ = l_Lean_Syntax_node4(v___x_3510_, v___x_3518_, v___x_3523_, v___x_3525_, v___x_3527_, v___x_3529_);
v___x_3531_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__14));
v___x_3532_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3532_, 0, v___x_3510_);
lean_ctor_set(v___x_3532_, 1, v___x_3531_);
v___x_3533_ = l_Lean_Syntax_node4(v___x_3510_, v___x_3511_, v___x_3513_, v___x_3517_, v___x_3530_, v___x_3532_);
v___x_3534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3534_, 0, v___x_3508_);
lean_ctor_set(v___x_3534_, 1, v___x_3533_);
v___x_3535_ = ((size_t)1ULL);
v___x_3536_ = lean_usize_add(v_i_3491_, v___x_3535_);
v___x_3537_ = lean_array_uset(v_bs_x27_3500_, v_i_3491_, v___x_3534_);
v_i_3491_ = v___x_3536_;
v_bs_3492_ = v___x_3537_;
goto _start;
}
else
{
lean_object* v_a_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3546_; 
lean_dec_ref(v_bs_x27_3500_);
lean_dec(v_v_3498_);
v_a_3539_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3541_ = v___x_3502_;
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_a_3539_);
lean_dec(v___x_3502_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3544_; 
if (v_isShared_3542_ == 0)
{
v___x_3544_ = v___x_3541_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_a_3539_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
return v___x_3544_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3490_ = stack[0].m_num;
size_t v_i_3491_ = stack[1].m_num;
lean_object* v_bs_3492_ = stack[2].m_obj;
lean_object* v___y_3493_ = stack[3].m_obj;
lean_object* v___y_3494_ = stack[4].m_obj;
lean_object* v_res_3547_;
v_res_3547_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg(v_sz_3490_, v_i_3491_, v_bs_3492_, v___y_3493_, v___y_3494_);
stack->m_obj
 = v_res_3547_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg___boxed(lean_object* v_sz_3548_, lean_object* v_i_3549_, lean_object* v_bs_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_){
_start:
{
size_t v_sz_boxed_3554_; size_t v_i_boxed_3555_; lean_object* v_res_3556_; 
v_sz_boxed_3554_ = lean_unbox_usize(v_sz_3548_);
lean_dec(v_sz_3548_);
v_i_boxed_3555_ = lean_unbox_usize(v_i_3549_);
lean_dec(v_i_3549_);
v_res_3556_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg(v_sz_boxed_3554_, v_i_boxed_3555_, v_bs_3550_, v___y_3551_, v___y_3552_);
lean_dec(v___y_3552_);
lean_dec_ref(v___y_3551_);
return v_res_3556_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__2(size_t v_sz_3557_, size_t v_i_3558_, lean_object* v_bs_3559_){
_start:
{
uint8_t v___x_3560_; 
v___x_3560_ = lean_usize_dec_lt(v_i_3558_, v_sz_3557_);
if (v___x_3560_ == 0)
{
return v_bs_3559_;
}
else
{
lean_object* v_v_3561_; lean_object* v___x_3562_; lean_object* v_bs_x27_3563_; size_t v___x_3564_; size_t v___x_3565_; lean_object* v___x_3566_; 
v_v_3561_ = lean_array_uget(v_bs_3559_, v_i_3558_);
v___x_3562_ = lean_unsigned_to_nat(0u);
v_bs_x27_3563_ = lean_array_uset(v_bs_3559_, v_i_3558_, v___x_3562_);
v___x_3564_ = ((size_t)1ULL);
v___x_3565_ = lean_usize_add(v_i_3558_, v___x_3564_);
v___x_3566_ = lean_array_uset(v_bs_x27_3563_, v_i_3558_, v_v_3561_);
v_i_3558_ = v___x_3565_;
v_bs_3559_ = v___x_3566_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3557_ = stack[0].m_num;
size_t v_i_3558_ = stack[1].m_num;
lean_object* v_bs_3559_ = stack[2].m_obj;
lean_object* v_res_3568_;
v_res_3568_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__2(v_sz_3557_, v_i_3558_, v_bs_3559_);
stack->m_obj
 = v_res_3568_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__2___boxed(lean_object* v_sz_3569_, lean_object* v_i_3570_, lean_object* v_bs_3571_){
_start:
{
size_t v_sz_boxed_3572_; size_t v_i_boxed_3573_; lean_object* v_res_3574_; 
v_sz_boxed_3572_ = lean_unbox_usize(v_sz_3569_);
lean_dec(v_sz_3569_);
v_i_boxed_3573_ = lean_unbox_usize(v_i_3570_);
lean_dec(v_i_3570_);
v_res_3574_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__2(v_sz_boxed_3572_, v_i_boxed_3573_, v_bs_3571_);
return v_res_3574_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3(lean_object* v_typeNames_3615_, lean_object* v_as_3616_, size_t v_sz_3617_, size_t v_i_3618_, lean_object* v_b_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_){
_start:
{
lean_object* v_a_3628_; uint8_t v___x_3632_; 
v___x_3632_ = lean_usize_dec_lt(v_i_3618_, v_sz_3617_);
if (v___x_3632_ == 0)
{
lean_object* v___x_3633_; 
v___x_3633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3633_, 0, v_b_3619_);
return v___x_3633_;
}
else
{
lean_object* v_snd_3634_; lean_object* v_fst_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3847_; 
v_snd_3634_ = lean_ctor_get(v_b_3619_, 1);
v_fst_3635_ = lean_ctor_get(v_b_3619_, 0);
v_isSharedCheck_3847_ = !lean_is_exclusive(v_b_3619_);
if (v_isSharedCheck_3847_ == 0)
{
v___x_3637_ = v_b_3619_;
v_isShared_3638_ = v_isSharedCheck_3847_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_snd_3634_);
lean_inc(v_fst_3635_);
lean_dec(v_b_3619_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3847_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v_array_3639_; lean_object* v_start_3640_; lean_object* v_stop_3641_; uint8_t v___x_3642_; 
v_array_3639_ = lean_ctor_get(v_snd_3634_, 0);
v_start_3640_ = lean_ctor_get(v_snd_3634_, 1);
v_stop_3641_ = lean_ctor_get(v_snd_3634_, 2);
v___x_3642_ = lean_nat_dec_lt(v_start_3640_, v_stop_3641_);
if (v___x_3642_ == 0)
{
lean_object* v___x_3644_; 
if (v_isShared_3638_ == 0)
{
v___x_3644_ = v___x_3637_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_fst_3635_);
lean_ctor_set(v_reuseFailAlloc_3646_, 1, v_snd_3634_);
v___x_3644_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
lean_object* v___x_3645_; 
v___x_3645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3645_, 0, v___x_3644_);
return v___x_3645_;
}
}
else
{
lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3843_; 
lean_inc(v_stop_3641_);
lean_inc(v_start_3640_);
lean_inc_ref(v_array_3639_);
v_isSharedCheck_3843_ = !lean_is_exclusive(v_snd_3634_);
if (v_isSharedCheck_3843_ == 0)
{
lean_object* v_unused_3844_; lean_object* v_unused_3845_; lean_object* v_unused_3846_; 
v_unused_3844_ = lean_ctor_get(v_snd_3634_, 2);
lean_dec(v_unused_3844_);
v_unused_3845_ = lean_ctor_get(v_snd_3634_, 1);
lean_dec(v_unused_3845_);
v_unused_3846_ = lean_ctor_get(v_snd_3634_, 0);
lean_dec(v_unused_3846_);
v___x_3648_ = v_snd_3634_;
v_isShared_3649_ = v_isSharedCheck_3843_;
goto v_resetjp_3647_;
}
else
{
lean_dec(v_snd_3634_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3843_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v_a_3650_; lean_object* v_toConstantVal_3651_; lean_object* v_name_3652_; lean_object* v_levelParams_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3841_; 
v_a_3650_ = lean_array_uget_borrowed(v_as_3616_, v_i_3618_);
v_toConstantVal_3651_ = lean_ctor_get(v_a_3650_, 0);
lean_inc_ref(v_toConstantVal_3651_);
v_name_3652_ = lean_ctor_get(v_toConstantVal_3651_, 0);
v_levelParams_3653_ = lean_ctor_get(v_toConstantVal_3651_, 1);
v_isSharedCheck_3841_ = !lean_is_exclusive(v_toConstantVal_3651_);
if (v_isSharedCheck_3841_ == 0)
{
lean_object* v_unused_3842_; 
v_unused_3842_ = lean_ctor_get(v_toConstantVal_3651_, 2);
lean_dec(v_unused_3842_);
v___x_3655_ = v_toConstantVal_3651_;
v_isShared_3656_ = v_isSharedCheck_3841_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_levelParams_3653_);
lean_inc(v_name_3652_);
lean_dec(v_toConstantVal_3651_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3841_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3661_; 
v___x_3657_ = lean_array_fget(v_array_3639_, v_start_3640_);
v___x_3658_ = lean_unsigned_to_nat(1u);
v___x_3659_ = lean_nat_add(v_start_3640_, v___x_3658_);
lean_dec(v_start_3640_);
if (v_isShared_3649_ == 0)
{
lean_ctor_set(v___x_3648_, 1, v___x_3659_);
v___x_3661_ = v___x_3648_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_array_3639_);
lean_ctor_set(v_reuseFailAlloc_3840_, 1, v___x_3659_);
lean_ctor_set(v_reuseFailAlloc_3840_, 2, v_stop_3641_);
v___x_3661_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
uint8_t v___x_3662_; 
v___x_3662_ = l_Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0(v_typeNames_3615_, v_name_3652_);
if (v___x_3662_ == 0)
{
lean_object* v___x_3664_; 
lean_dec(v___x_3657_);
lean_del_object(v___x_3655_);
lean_dec(v_levelParams_3653_);
lean_dec(v_name_3652_);
if (v_isShared_3638_ == 0)
{
lean_ctor_set(v___x_3637_, 1, v___x_3661_);
v___x_3664_ = v___x_3637_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v_fst_3635_);
lean_ctor_set(v_reuseFailAlloc_3665_, 1, v___x_3661_);
v___x_3664_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
v_a_3628_ = v___x_3664_;
goto v___jp_3627_;
}
}
else
{
lean_object* v___x_3666_; 
lean_del_object(v___x_3637_);
lean_inc(v_a_3650_);
v___x_3666_ = l_Lean_Elab_Deriving_mkInductArgNames(v_a_3650_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_);
if (lean_obj_tag(v___x_3666_) == 0)
{
lean_object* v_a_3667_; lean_object* v___x_3668_; 
v_a_3667_ = lean_ctor_get(v___x_3666_, 0);
lean_inc_n(v_a_3667_, 2);
lean_dec_ref_known(v___x_3666_, 1);
v___x_3668_ = l_Lean_Elab_Deriving_mkImplicitBinders(v_a_3667_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_);
if (lean_obj_tag(v___x_3668_) == 0)
{
lean_object* v_a_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; 
v_a_3669_ = lean_ctor_get(v___x_3668_, 0);
lean_inc(v_a_3669_);
lean_dec_ref_known(v___x_3668_, 1);
v___x_3670_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__14));
lean_inc(v_a_3667_);
lean_inc(v_a_3650_);
v___x_3671_ = l_Lean_Elab_Deriving_mkInstImplicitBinders(v___x_3670_, v_a_3650_, v_a_3667_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_);
if (lean_obj_tag(v___x_3671_) == 0)
{
lean_object* v_a_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; size_t v_sz_3675_; size_t v___x_3676_; lean_object* v___x_3677_; 
v_a_3672_ = lean_ctor_get(v___x_3671_, 0);
lean_inc(v_a_3672_);
lean_dec_ref_known(v___x_3671_, 1);
v___x_3673_ = l_Array_append___redArg(v_a_3669_, v_a_3672_);
lean_dec(v_a_3672_);
v___x_3674_ = lean_array_mk(v_levelParams_3653_);
v_sz_3675_ = lean_array_size(v___x_3674_);
v___x_3676_ = ((size_t)0ULL);
v___x_3677_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg(v_sz_3675_, v___x_3676_, v___x_3674_, v___y_3624_, v___y_3625_);
if (lean_obj_tag(v___x_3677_) == 0)
{
lean_object* v_a_3678_; lean_object* v___x_3679_; lean_object* v_fst_3680_; lean_object* v_snd_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3807_; 
v_a_3678_ = lean_ctor_get(v___x_3677_, 0);
lean_inc(v_a_3678_);
lean_dec_ref_known(v___x_3677_, 1);
v___x_3679_ = l_Array_unzip___redArg(v_a_3678_);
lean_dec(v_a_3678_);
v_fst_3680_ = lean_ctor_get(v___x_3679_, 0);
v_snd_3681_ = lean_ctor_get(v___x_3679_, 1);
v_isSharedCheck_3807_ = !lean_is_exclusive(v___x_3679_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3683_ = v___x_3679_;
v_isShared_3684_ = v_isSharedCheck_3807_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_snd_3681_);
lean_inc(v_fst_3680_);
lean_dec(v___x_3679_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3807_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3685_; lean_object* v___x_3686_; 
v___x_3685_ = l_Array_append___redArg(v___x_3673_, v_snd_3681_);
lean_dec(v_snd_3681_);
lean_inc(v_a_3667_);
lean_inc(v_a_3650_);
v___x_3686_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v_a_3650_, v_a_3667_, v___y_3624_);
if (lean_obj_tag(v___x_3686_) == 0)
{
lean_object* v_a_3687_; lean_object* v___x_3688_; 
v_a_3687_ = lean_ctor_get(v___x_3686_, 0);
lean_inc(v_a_3687_);
lean_dec_ref_known(v___x_3686_, 1);
lean_inc(v_a_3650_);
v___x_3688_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType(v_a_3650_, v_a_3687_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_);
if (lean_obj_tag(v___x_3688_) == 0)
{
lean_object* v_a_3689_; lean_object* v___x_3690_; 
v_a_3689_ = lean_ctor_get(v___x_3688_, 0);
lean_inc(v_a_3689_);
lean_dec_ref_known(v___x_3688_, 1);
lean_inc(v_a_3650_);
v___x_3690_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr(v_a_3650_, v_a_3667_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_);
if (lean_obj_tag(v___x_3690_) == 0)
{
lean_object* v_a_3691_; lean_object* v___x_3692_; 
v_a_3691_ = lean_ctor_get(v___x_3690_, 0);
lean_inc(v_a_3691_);
lean_dec_ref_known(v___x_3690_, 1);
v___x_3692_ = l_Lean_Elab_Deriving_mkInstName(v___x_3670_, v_name_3652_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_);
if (lean_obj_tag(v___x_3692_) == 0)
{
lean_object* v_toCold_3693_; lean_object* v_a_3694_; lean_object* v_ref_3695_; lean_object* v_quotContext_3696_; lean_object* v_currMacroScope_3697_; uint8_t v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3705_; 
v_toCold_3693_ = lean_ctor_get(v___y_3624_, 0);
v_a_3694_ = lean_ctor_get(v___x_3692_, 0);
lean_inc(v_a_3694_);
lean_dec_ref_known(v___x_3692_, 1);
v_ref_3695_ = lean_ctor_get(v___y_3624_, 2);
v_quotContext_3696_ = lean_ctor_get(v_toCold_3693_, 8);
v_currMacroScope_3697_ = lean_ctor_get(v_toCold_3693_, 9);
v___x_3698_ = 0;
v___x_3699_ = l_Lean_SourceInfo_fromRef(v_ref_3695_, v___x_3698_);
v___x_3700_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__0));
v___x_3701_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__1));
v___x_3702_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_3703_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
lean_inc(v___x_3699_);
if (v_isShared_3656_ == 0)
{
lean_ctor_set_tag(v___x_3655_, 1);
lean_ctor_set(v___x_3655_, 2, v___x_3703_);
lean_ctor_set(v___x_3655_, 1, v___x_3702_);
lean_ctor_set(v___x_3655_, 0, v___x_3699_);
v___x_3705_ = v___x_3655_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v___x_3699_);
lean_ctor_set(v_reuseFailAlloc_3774_, 1, v___x_3702_);
lean_ctor_set(v_reuseFailAlloc_3774_, 2, v___x_3703_);
v___x_3705_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; size_t v_sz_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3772_; 
lean_inc_ref_n(v___x_3705_, 19);
lean_inc_n(v___x_3699_, 30);
v___x_3706_ = l_Lean_Syntax_node7(v___x_3699_, v___x_3701_, v___x_3705_, v___x_3705_, v___x_3705_, v___x_3705_, v___x_3705_, v___x_3705_, v___x_3705_);
v___x_3707_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__2));
v___x_3708_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__3));
v___x_3709_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__5));
v___x_3710_ = l_Lean_Syntax_node1(v___x_3699_, v___x_3709_, v___x_3705_);
v___x_3711_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3711_, 0, v___x_3699_);
lean_ctor_set(v___x_3711_, 1, v___x_3707_);
v___x_3712_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__6));
v___x_3713_ = l_Lean_mkIdent(v_a_3694_);
v___x_3714_ = l_Lean_Syntax_node2(v___x_3699_, v___x_3712_, v___x_3713_, v___x_3705_);
v___x_3715_ = l_Lean_Syntax_node1(v___x_3699_, v___x_3702_, v___x_3714_);
v___x_3716_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__8));
v___x_3717_ = l_Array_append___redArg(v___x_3703_, v___x_3685_);
lean_dec_ref(v___x_3685_);
v___x_3718_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3718_, 0, v___x_3699_);
lean_ctor_set(v___x_3718_, 1, v___x_3702_);
lean_ctor_set(v___x_3718_, 2, v___x_3717_);
v___x_3719_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__10));
v___x_3720_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__11));
v___x_3721_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3721_, 0, v___x_3699_);
lean_ctor_set(v___x_3721_, 1, v___x_3720_);
v___x_3722_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_3723_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__12);
v___x_3724_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__13));
lean_inc_n(v_currMacroScope_3697_, 3);
lean_inc_n(v_quotContext_3696_, 3);
v___x_3725_ = l_Lean_addMacroScope(v_quotContext_3696_, v___x_3724_, v_currMacroScope_3697_);
v___x_3726_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__26));
v___x_3727_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3727_, 0, v___x_3699_);
lean_ctor_set(v___x_3727_, 1, v___x_3723_);
lean_ctor_set(v___x_3727_, 2, v___x_3725_);
lean_ctor_set(v___x_3727_, 3, v___x_3726_);
v___x_3728_ = l_Lean_Syntax_node1(v___x_3699_, v___x_3702_, v_a_3689_);
v___x_3729_ = l_Lean_Syntax_node2(v___x_3699_, v___x_3722_, v___x_3727_, v___x_3728_);
v___x_3730_ = l_Lean_Syntax_node2(v___x_3699_, v___x_3719_, v___x_3721_, v___x_3729_);
v___x_3731_ = l_Lean_Syntax_node2(v___x_3699_, v___x_3716_, v___x_3718_, v___x_3730_);
v___x_3732_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__10));
v___x_3733_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__11));
v___x_3734_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3699_);
lean_ctor_set(v___x_3734_, 1, v___x_3733_);
v___x_3735_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__32));
v___x_3736_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__34));
v___x_3737_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__36));
v___x_3738_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1);
v___x_3739_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__2));
v___x_3740_ = l_Lean_addMacroScope(v_quotContext_3696_, v___x_3739_, v_currMacroScope_3697_);
v___x_3741_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__6));
v___x_3742_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3742_, 0, v___x_3699_);
lean_ctor_set(v___x_3742_, 1, v___x_3738_);
lean_ctor_set(v___x_3742_, 2, v___x_3740_);
lean_ctor_set(v___x_3742_, 3, v___x_3741_);
v___x_3743_ = l_Lean_Syntax_node2(v___x_3699_, v___x_3737_, v___x_3742_, v___x_3705_);
v___x_3744_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__38));
v___x_3745_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__27));
v___x_3746_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3746_, 0, v___x_3699_);
lean_ctor_set(v___x_3746_, 1, v___x_3745_);
v___x_3747_ = l_Lean_mkIdent(v___x_3657_);
v_sz_3748_ = lean_array_size(v_fst_3680_);
v___x_3749_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__2(v_sz_3748_, v___x_3676_, v_fst_3680_);
v___x_3750_ = l_Array_append___redArg(v___x_3703_, v___x_3749_);
lean_dec_ref(v___x_3749_);
v___x_3751_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3751_, 0, v___x_3699_);
lean_ctor_set(v___x_3751_, 1, v___x_3702_);
lean_ctor_set(v___x_3751_, 2, v___x_3750_);
v___x_3752_ = l_Lean_Syntax_node2(v___x_3699_, v___x_3722_, v___x_3747_, v___x_3751_);
lean_inc_ref(v___x_3746_);
v___x_3753_ = l_Lean_Syntax_node3(v___x_3699_, v___x_3744_, v___x_3746_, v___x_3705_, v___x_3752_);
v___x_3754_ = l_Lean_Syntax_node3(v___x_3699_, v___x_3702_, v___x_3705_, v___x_3705_, v___x_3753_);
v___x_3755_ = l_Lean_Syntax_node2(v___x_3699_, v___x_3736_, v___x_3743_, v___x_3754_);
v___x_3756_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8);
v___x_3757_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__9));
v___x_3758_ = l_Lean_addMacroScope(v_quotContext_3696_, v___x_3757_, v_currMacroScope_3697_);
v___x_3759_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__12));
v___x_3760_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3760_, 0, v___x_3699_);
lean_ctor_set(v___x_3760_, 1, v___x_3756_);
lean_ctor_set(v___x_3760_, 2, v___x_3758_);
lean_ctor_set(v___x_3760_, 3, v___x_3759_);
v___x_3761_ = l_Lean_Syntax_node2(v___x_3699_, v___x_3737_, v___x_3760_, v___x_3705_);
v___x_3762_ = l_Lean_Syntax_node3(v___x_3699_, v___x_3744_, v___x_3746_, v___x_3705_, v_a_3691_);
v___x_3763_ = l_Lean_Syntax_node3(v___x_3699_, v___x_3702_, v___x_3705_, v___x_3705_, v___x_3762_);
v___x_3764_ = l_Lean_Syntax_node2(v___x_3699_, v___x_3736_, v___x_3761_, v___x_3763_);
v___x_3765_ = l_Lean_Syntax_node3(v___x_3699_, v___x_3702_, v___x_3755_, v___x_3705_, v___x_3764_);
v___x_3766_ = l_Lean_Syntax_node1(v___x_3699_, v___x_3735_, v___x_3765_);
v___x_3767_ = l_Lean_Syntax_node3(v___x_3699_, v___x_3732_, v___x_3734_, v___x_3766_, v___x_3705_);
v___x_3768_ = l_Lean_Syntax_node6(v___x_3699_, v___x_3708_, v___x_3710_, v___x_3711_, v___x_3705_, v___x_3715_, v___x_3731_, v___x_3767_);
v___x_3769_ = l_Lean_Syntax_node2(v___x_3699_, v___x_3700_, v___x_3706_, v___x_3768_);
v___x_3770_ = lean_array_push(v_fst_3635_, v___x_3769_);
if (v_isShared_3684_ == 0)
{
lean_ctor_set(v___x_3683_, 1, v___x_3661_);
lean_ctor_set(v___x_3683_, 0, v___x_3770_);
v___x_3772_ = v___x_3683_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v___x_3770_);
lean_ctor_set(v_reuseFailAlloc_3773_, 1, v___x_3661_);
v___x_3772_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
v_a_3628_ = v___x_3772_;
goto v___jp_3627_;
}
}
}
else
{
lean_object* v_a_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3782_; 
lean_dec(v_a_3691_);
lean_dec(v_a_3689_);
lean_dec_ref(v___x_3685_);
lean_del_object(v___x_3683_);
lean_dec(v_fst_3680_);
lean_dec_ref(v___x_3661_);
lean_dec(v___x_3657_);
lean_del_object(v___x_3655_);
lean_dec(v_fst_3635_);
v_a_3775_ = lean_ctor_get(v___x_3692_, 0);
v_isSharedCheck_3782_ = !lean_is_exclusive(v___x_3692_);
if (v_isSharedCheck_3782_ == 0)
{
v___x_3777_ = v___x_3692_;
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
else
{
lean_inc(v_a_3775_);
lean_dec(v___x_3692_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
lean_object* v___x_3780_; 
if (v_isShared_3778_ == 0)
{
v___x_3780_ = v___x_3777_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_a_3775_);
v___x_3780_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
return v___x_3780_;
}
}
}
}
else
{
lean_object* v_a_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3790_; 
lean_dec(v_a_3689_);
lean_dec_ref(v___x_3685_);
lean_del_object(v___x_3683_);
lean_dec(v_fst_3680_);
lean_dec_ref(v___x_3661_);
lean_dec(v___x_3657_);
lean_del_object(v___x_3655_);
lean_dec(v_name_3652_);
lean_dec(v_fst_3635_);
v_a_3783_ = lean_ctor_get(v___x_3690_, 0);
v_isSharedCheck_3790_ = !lean_is_exclusive(v___x_3690_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3785_ = v___x_3690_;
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_a_3783_);
lean_dec(v___x_3690_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3788_; 
if (v_isShared_3786_ == 0)
{
v___x_3788_ = v___x_3785_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_a_3783_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
return v___x_3788_;
}
}
}
}
else
{
lean_object* v_a_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3798_; 
lean_dec_ref(v___x_3685_);
lean_del_object(v___x_3683_);
lean_dec(v_fst_3680_);
lean_dec(v_a_3667_);
lean_dec_ref(v___x_3661_);
lean_dec(v___x_3657_);
lean_del_object(v___x_3655_);
lean_dec(v_name_3652_);
lean_dec(v_fst_3635_);
v_a_3791_ = lean_ctor_get(v___x_3688_, 0);
v_isSharedCheck_3798_ = !lean_is_exclusive(v___x_3688_);
if (v_isSharedCheck_3798_ == 0)
{
v___x_3793_ = v___x_3688_;
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_a_3791_);
lean_dec(v___x_3688_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v___x_3796_; 
if (v_isShared_3794_ == 0)
{
v___x_3796_ = v___x_3793_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v_a_3791_);
v___x_3796_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
return v___x_3796_;
}
}
}
}
else
{
lean_object* v_a_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3806_; 
lean_dec_ref(v___x_3685_);
lean_del_object(v___x_3683_);
lean_dec(v_fst_3680_);
lean_dec(v_a_3667_);
lean_dec_ref(v___x_3661_);
lean_dec(v___x_3657_);
lean_del_object(v___x_3655_);
lean_dec(v_name_3652_);
lean_dec(v_fst_3635_);
v_a_3799_ = lean_ctor_get(v___x_3686_, 0);
v_isSharedCheck_3806_ = !lean_is_exclusive(v___x_3686_);
if (v_isSharedCheck_3806_ == 0)
{
v___x_3801_ = v___x_3686_;
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_a_3799_);
lean_dec(v___x_3686_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3804_; 
if (v_isShared_3802_ == 0)
{
v___x_3804_ = v___x_3801_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v_a_3799_);
v___x_3804_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
return v___x_3804_;
}
}
}
}
}
else
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3815_; 
lean_dec_ref(v___x_3673_);
lean_dec(v_a_3667_);
lean_dec_ref(v___x_3661_);
lean_dec(v___x_3657_);
lean_del_object(v___x_3655_);
lean_dec(v_name_3652_);
lean_dec(v_fst_3635_);
v_a_3808_ = lean_ctor_get(v___x_3677_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3677_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3810_ = v___x_3677_;
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3677_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3813_; 
if (v_isShared_3811_ == 0)
{
v___x_3813_ = v___x_3810_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_a_3808_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
}
}
else
{
lean_object* v_a_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3823_; 
lean_dec(v_a_3669_);
lean_dec(v_a_3667_);
lean_dec_ref(v___x_3661_);
lean_dec(v___x_3657_);
lean_del_object(v___x_3655_);
lean_dec(v_levelParams_3653_);
lean_dec(v_name_3652_);
lean_dec(v_fst_3635_);
v_a_3816_ = lean_ctor_get(v___x_3671_, 0);
v_isSharedCheck_3823_ = !lean_is_exclusive(v___x_3671_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3818_ = v___x_3671_;
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_a_3816_);
lean_dec(v___x_3671_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v___x_3821_; 
if (v_isShared_3819_ == 0)
{
v___x_3821_ = v___x_3818_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_a_3816_);
v___x_3821_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
return v___x_3821_;
}
}
}
}
else
{
lean_object* v_a_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3831_; 
lean_dec(v_a_3667_);
lean_dec_ref(v___x_3661_);
lean_dec(v___x_3657_);
lean_del_object(v___x_3655_);
lean_dec(v_levelParams_3653_);
lean_dec(v_name_3652_);
lean_dec(v_fst_3635_);
v_a_3824_ = lean_ctor_get(v___x_3668_, 0);
v_isSharedCheck_3831_ = !lean_is_exclusive(v___x_3668_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3826_ = v___x_3668_;
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
else
{
lean_inc(v_a_3824_);
lean_dec(v___x_3668_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
lean_object* v___x_3829_; 
if (v_isShared_3827_ == 0)
{
v___x_3829_ = v___x_3826_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_a_3824_);
v___x_3829_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
return v___x_3829_;
}
}
}
}
else
{
lean_object* v_a_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3839_; 
lean_dec_ref(v___x_3661_);
lean_dec(v___x_3657_);
lean_del_object(v___x_3655_);
lean_dec(v_levelParams_3653_);
lean_dec(v_name_3652_);
lean_dec(v_fst_3635_);
v_a_3832_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3834_ = v___x_3666_;
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_a_3832_);
lean_dec(v___x_3666_);
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
}
}
}
}
}
v___jp_3627_:
{
size_t v___x_3629_; size_t v___x_3630_; 
v___x_3629_ = ((size_t)1ULL);
v___x_3630_ = lean_usize_add(v_i_3618_, v___x_3629_);
v_i_3618_ = v___x_3630_;
v_b_3619_ = v_a_3628_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_typeNames_3615_ = stack[0].m_obj;
lean_object* v_as_3616_ = stack[1].m_obj;
size_t v_sz_3617_ = stack[2].m_num;
size_t v_i_3618_ = stack[3].m_num;
lean_object* v_b_3619_ = stack[4].m_obj;
lean_object* v___y_3620_ = stack[5].m_obj;
lean_object* v___y_3621_ = stack[6].m_obj;
lean_object* v___y_3622_ = stack[7].m_obj;
lean_object* v___y_3623_ = stack[8].m_obj;
lean_object* v___y_3624_ = stack[9].m_obj;
lean_object* v___y_3625_ = stack[10].m_obj;
lean_object* v_res_3848_;
v_res_3848_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3(v_typeNames_3615_, v_as_3616_, v_sz_3617_, v_i_3618_, v_b_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_);
stack->m_obj
 = v_res_3848_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___boxed(lean_object* v_typeNames_3849_, lean_object* v_as_3850_, lean_object* v_sz_3851_, lean_object* v_i_3852_, lean_object* v_b_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_){
_start:
{
size_t v_sz_boxed_3861_; size_t v_i_boxed_3862_; lean_object* v_res_3863_; 
v_sz_boxed_3861_ = lean_unbox_usize(v_sz_3851_);
lean_dec(v_sz_3851_);
v_i_boxed_3862_ = lean_unbox_usize(v_i_3852_);
lean_dec(v_i_3852_);
v_res_3863_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3(v_typeNames_3849_, v_as_3850_, v_sz_boxed_3861_, v_i_boxed_3862_, v_b_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
lean_dec(v___y_3859_);
lean_dec_ref(v___y_3858_);
lean_dec(v___y_3857_);
lean_dec_ref(v___y_3856_);
lean_dec(v___y_3855_);
lean_dec_ref(v___y_3854_);
lean_dec_ref(v_as_3850_);
lean_dec_ref(v_typeNames_3849_);
return v_res_3863_;
}
}
lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds(lean_object* v_ctx_3864_, lean_object* v_typeNames_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_){
_start:
{
lean_object* v_typeInfos_3873_; lean_object* v_auxFunNames_3874_; lean_object* v___x_3875_; lean_object* v_instances_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; size_t v_sz_3880_; size_t v___x_3881_; lean_object* v___x_3882_; 
v_typeInfos_3873_ = lean_ctor_get(v_ctx_3864_, 1);
lean_inc_ref(v_typeInfos_3873_);
v_auxFunNames_3874_ = lean_ctor_get(v_ctx_3864_, 2);
lean_inc_ref(v_auxFunNames_3874_);
lean_dec_ref(v_ctx_3864_);
v___x_3875_ = lean_unsigned_to_nat(0u);
v_instances_3876_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__0));
v___x_3877_ = lean_array_get_size(v_auxFunNames_3874_);
v___x_3878_ = l_Array_toSubarray___redArg(v_auxFunNames_3874_, v___x_3875_, v___x_3877_);
v___x_3879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3879_, 0, v_instances_3876_);
lean_ctor_set(v___x_3879_, 1, v___x_3878_);
v_sz_3880_ = lean_array_size(v_typeInfos_3873_);
v___x_3881_ = ((size_t)0ULL);
v___x_3882_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3(v_typeNames_3865_, v_typeInfos_3873_, v_sz_3880_, v___x_3881_, v___x_3879_, v_a_3866_, v_a_3867_, v_a_3868_, v_a_3869_, v_a_3870_, v_a_3871_);
lean_dec_ref(v_typeInfos_3873_);
if (lean_obj_tag(v___x_3882_) == 0)
{
lean_object* v_a_3883_; lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3891_; 
v_a_3883_ = lean_ctor_get(v___x_3882_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___x_3882_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3885_ = v___x_3882_;
v_isShared_3886_ = v_isSharedCheck_3891_;
goto v_resetjp_3884_;
}
else
{
lean_inc(v_a_3883_);
lean_dec(v___x_3882_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3891_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v_fst_3887_; lean_object* v___x_3889_; 
v_fst_3887_ = lean_ctor_get(v_a_3883_, 0);
lean_inc(v_fst_3887_);
lean_dec(v_a_3883_);
if (v_isShared_3886_ == 0)
{
lean_ctor_set(v___x_3885_, 0, v_fst_3887_);
v___x_3889_ = v___x_3885_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_fst_3887_);
v___x_3889_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
return v___x_3889_;
}
}
}
else
{
lean_object* v_a_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3899_; 
v_a_3892_ = lean_ctor_get(v___x_3882_, 0);
v_isSharedCheck_3899_ = !lean_is_exclusive(v___x_3882_);
if (v_isSharedCheck_3899_ == 0)
{
v___x_3894_ = v___x_3882_;
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_a_3892_);
lean_dec(v___x_3882_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v___x_3897_; 
if (v_isShared_3895_ == 0)
{
v___x_3897_ = v___x_3894_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v_a_3892_);
v___x_3897_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
return v___x_3897_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_3864_ = stack[0].m_obj;
lean_object* v_typeNames_3865_ = stack[1].m_obj;
lean_object* v_a_3866_ = stack[2].m_obj;
lean_object* v_a_3867_ = stack[3].m_obj;
lean_object* v_a_3868_ = stack[4].m_obj;
lean_object* v_a_3869_ = stack[5].m_obj;
lean_object* v_a_3870_ = stack[6].m_obj;
lean_object* v_a_3871_ = stack[7].m_obj;
lean_object* v_res_3900_;
v_res_3900_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds(v_ctx_3864_, v_typeNames_3865_, v_a_3866_, v_a_3867_, v_a_3868_, v_a_3869_, v_a_3870_, v_a_3871_);
stack->m_obj
 = v_res_3900_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds___boxed(lean_object* v_ctx_3901_, lean_object* v_typeNames_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_){
_start:
{
lean_object* v_res_3910_; 
v_res_3910_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds(v_ctx_3901_, v_typeNames_3902_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_);
lean_dec(v_a_3908_);
lean_dec_ref(v_a_3907_);
lean_dec(v_a_3906_);
lean_dec_ref(v_a_3905_);
lean_dec(v_a_3904_);
lean_dec_ref(v_a_3903_);
lean_dec_ref(v_typeNames_3902_);
return v_res_3910_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1(size_t v_sz_3911_, size_t v_i_3912_, lean_object* v_bs_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_){
_start:
{
lean_object* v___x_3921_; 
v___x_3921_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg(v_sz_3911_, v_i_3912_, v_bs_3913_, v___y_3918_, v___y_3919_);
return v___x_3921_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3911_ = stack[0].m_num;
size_t v_i_3912_ = stack[1].m_num;
lean_object* v_bs_3913_ = stack[2].m_obj;
lean_object* v___y_3914_ = stack[3].m_obj;
lean_object* v___y_3915_ = stack[4].m_obj;
lean_object* v___y_3916_ = stack[5].m_obj;
lean_object* v___y_3917_ = stack[6].m_obj;
lean_object* v___y_3918_ = stack[7].m_obj;
lean_object* v___y_3919_ = stack[8].m_obj;
lean_object* v_res_3922_;
v_res_3922_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1(v_sz_3911_, v_i_3912_, v_bs_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_);
stack->m_obj
 = v_res_3922_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___boxed(lean_object* v_sz_3923_, lean_object* v_i_3924_, lean_object* v_bs_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_){
_start:
{
size_t v_sz_boxed_3933_; size_t v_i_boxed_3934_; lean_object* v_res_3935_; 
v_sz_boxed_3933_ = lean_unbox_usize(v_sz_3923_);
lean_dec(v_sz_3923_);
v_i_boxed_3934_ = lean_unbox_usize(v_i_3924_);
lean_dec(v_i_3924_);
v_res_3935_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1(v_sz_boxed_3933_, v_i_boxed_3934_, v_bs_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_);
lean_dec(v___y_3931_);
lean_dec_ref(v___y_3930_);
lean_dec(v___y_3929_);
lean_dec_ref(v___y_3928_);
lean_dec(v___y_3927_);
lean_dec_ref(v___y_3926_);
return v_res_3935_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__0(lean_object* v_a_3936_, lean_object* v_a_3937_){
_start:
{
if (lean_obj_tag(v_a_3936_) == 0)
{
lean_object* v___x_3938_; 
v___x_3938_ = l_List_reverse___redArg(v_a_3937_);
return v___x_3938_;
}
else
{
lean_object* v_head_3939_; lean_object* v_tail_3940_; lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_3949_; 
v_head_3939_ = lean_ctor_get(v_a_3936_, 0);
v_tail_3940_ = lean_ctor_get(v_a_3936_, 1);
v_isSharedCheck_3949_ = !lean_is_exclusive(v_a_3936_);
if (v_isSharedCheck_3949_ == 0)
{
v___x_3942_ = v_a_3936_;
v_isShared_3943_ = v_isSharedCheck_3949_;
goto v_resetjp_3941_;
}
else
{
lean_inc(v_tail_3940_);
lean_inc(v_head_3939_);
lean_dec(v_a_3936_);
v___x_3942_ = lean_box(0);
v_isShared_3943_ = v_isSharedCheck_3949_;
goto v_resetjp_3941_;
}
v_resetjp_3941_:
{
lean_object* v___x_3944_; lean_object* v___x_3946_; 
v___x_3944_ = l_Lean_MessageData_ofSyntax(v_head_3939_);
if (v_isShared_3943_ == 0)
{
lean_ctor_set(v___x_3942_, 1, v_a_3937_);
lean_ctor_set(v___x_3942_, 0, v___x_3944_);
v___x_3946_ = v___x_3942_;
goto v_reusejp_3945_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v___x_3944_);
lean_ctor_set(v_reuseFailAlloc_3948_, 1, v_a_3937_);
v___x_3946_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3945_;
}
v_reusejp_3945_:
{
v_a_3936_ = v_tail_3940_;
v_a_3937_ = v___x_3946_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3950_; double v___x_3951_; 
v___x_3950_ = lean_unsigned_to_nat(0u);
v___x_3951_ = lean_float_of_nat(v___x_3950_);
return v___x_3951_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg(lean_object* v_cls_3955_, lean_object* v_msg_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_){
_start:
{
lean_object* v_ref_3962_; lean_object* v___x_3963_; lean_object* v_a_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_4009_; 
v_ref_3962_ = lean_ctor_get(v___y_3959_, 2);
v___x_3963_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__0(v_msg_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_);
v_a_3964_ = lean_ctor_get(v___x_3963_, 0);
v_isSharedCheck_4009_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_3966_ = v___x_3963_;
v_isShared_3967_ = v_isSharedCheck_4009_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_a_3964_);
lean_dec(v___x_3963_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_4009_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3968_; lean_object* v_traceState_3969_; lean_object* v_env_3970_; lean_object* v_nextMacroScope_3971_; lean_object* v_ngen_3972_; lean_object* v_auxDeclNGen_3973_; lean_object* v_cache_3974_; lean_object* v_recordedDeps_3975_; lean_object* v_messages_3976_; lean_object* v_infoState_3977_; lean_object* v_snapshotTasks_3978_; lean_object* v___x_3980_; uint8_t v_isShared_3981_; uint8_t v_isSharedCheck_4008_; 
v___x_3968_ = lean_st_ref_take(v___y_3960_);
v_traceState_3969_ = lean_ctor_get(v___x_3968_, 4);
v_env_3970_ = lean_ctor_get(v___x_3968_, 0);
v_nextMacroScope_3971_ = lean_ctor_get(v___x_3968_, 1);
v_ngen_3972_ = lean_ctor_get(v___x_3968_, 2);
v_auxDeclNGen_3973_ = lean_ctor_get(v___x_3968_, 3);
v_cache_3974_ = lean_ctor_get(v___x_3968_, 5);
v_recordedDeps_3975_ = lean_ctor_get(v___x_3968_, 6);
v_messages_3976_ = lean_ctor_get(v___x_3968_, 7);
v_infoState_3977_ = lean_ctor_get(v___x_3968_, 8);
v_snapshotTasks_3978_ = lean_ctor_get(v___x_3968_, 9);
v_isSharedCheck_4008_ = !lean_is_exclusive(v___x_3968_);
if (v_isSharedCheck_4008_ == 0)
{
v___x_3980_ = v___x_3968_;
v_isShared_3981_ = v_isSharedCheck_4008_;
goto v_resetjp_3979_;
}
else
{
lean_inc(v_snapshotTasks_3978_);
lean_inc(v_infoState_3977_);
lean_inc(v_messages_3976_);
lean_inc(v_recordedDeps_3975_);
lean_inc(v_cache_3974_);
lean_inc(v_traceState_3969_);
lean_inc(v_auxDeclNGen_3973_);
lean_inc(v_ngen_3972_);
lean_inc(v_nextMacroScope_3971_);
lean_inc(v_env_3970_);
lean_dec(v___x_3968_);
v___x_3980_ = lean_box(0);
v_isShared_3981_ = v_isSharedCheck_4008_;
goto v_resetjp_3979_;
}
v_resetjp_3979_:
{
uint64_t v_tid_3982_; lean_object* v_traces_3983_; lean_object* v___x_3985_; uint8_t v_isShared_3986_; uint8_t v_isSharedCheck_4007_; 
v_tid_3982_ = lean_ctor_get_uint64(v_traceState_3969_, sizeof(void*)*1);
v_traces_3983_ = lean_ctor_get(v_traceState_3969_, 0);
v_isSharedCheck_4007_ = !lean_is_exclusive(v_traceState_3969_);
if (v_isSharedCheck_4007_ == 0)
{
v___x_3985_ = v_traceState_3969_;
v_isShared_3986_ = v_isSharedCheck_4007_;
goto v_resetjp_3984_;
}
else
{
lean_inc(v_traces_3983_);
lean_dec(v_traceState_3969_);
v___x_3985_ = lean_box(0);
v_isShared_3986_ = v_isSharedCheck_4007_;
goto v_resetjp_3984_;
}
v_resetjp_3984_:
{
lean_object* v___x_3987_; lean_object* v___x_3988_; double v___x_3989_; uint8_t v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3998_; 
v___x_3987_ = lean_box(0);
v___x_3988_ = lean_box(0);
v___x_3989_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg___closed__0);
v___x_3990_ = 0;
v___x_3991_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg___closed__1));
v___x_3992_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3992_, 0, v_cls_3955_);
lean_ctor_set(v___x_3992_, 1, v___x_3988_);
lean_ctor_set(v___x_3992_, 2, v___x_3991_);
lean_ctor_set_float(v___x_3992_, sizeof(void*)*3, v___x_3989_);
lean_ctor_set_float(v___x_3992_, sizeof(void*)*3 + 8, v___x_3989_);
lean_ctor_set_uint8(v___x_3992_, sizeof(void*)*3 + 16, v___x_3990_);
v___x_3993_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg___closed__2));
v___x_3994_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3994_, 0, v___x_3992_);
lean_ctor_set(v___x_3994_, 1, v_a_3964_);
lean_ctor_set(v___x_3994_, 2, v___x_3993_);
lean_inc(v_ref_3962_);
v___x_3995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3995_, 0, v_ref_3962_);
lean_ctor_set(v___x_3995_, 1, v___x_3994_);
v___x_3996_ = l_Lean_PersistentArray_push___redArg(v_traces_3983_, v___x_3995_);
if (v_isShared_3986_ == 0)
{
lean_ctor_set(v___x_3985_, 0, v___x_3996_);
v___x_3998_ = v___x_3985_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_4006_; 
v_reuseFailAlloc_4006_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4006_, 0, v___x_3996_);
lean_ctor_set_uint64(v_reuseFailAlloc_4006_, sizeof(void*)*1, v_tid_3982_);
v___x_3998_ = v_reuseFailAlloc_4006_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
lean_object* v___x_4000_; 
if (v_isShared_3981_ == 0)
{
lean_ctor_set(v___x_3980_, 4, v___x_3998_);
v___x_4000_ = v___x_3980_;
goto v_reusejp_3999_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v_env_3970_);
lean_ctor_set(v_reuseFailAlloc_4005_, 1, v_nextMacroScope_3971_);
lean_ctor_set(v_reuseFailAlloc_4005_, 2, v_ngen_3972_);
lean_ctor_set(v_reuseFailAlloc_4005_, 3, v_auxDeclNGen_3973_);
lean_ctor_set(v_reuseFailAlloc_4005_, 4, v___x_3998_);
lean_ctor_set(v_reuseFailAlloc_4005_, 5, v_cache_3974_);
lean_ctor_set(v_reuseFailAlloc_4005_, 6, v_recordedDeps_3975_);
lean_ctor_set(v_reuseFailAlloc_4005_, 7, v_messages_3976_);
lean_ctor_set(v_reuseFailAlloc_4005_, 8, v_infoState_3977_);
lean_ctor_set(v_reuseFailAlloc_4005_, 9, v_snapshotTasks_3978_);
v___x_4000_ = v_reuseFailAlloc_4005_;
goto v_reusejp_3999_;
}
v_reusejp_3999_:
{
lean_object* v___x_4001_; lean_object* v___x_4003_; 
v___x_4001_ = lean_st_ref_put(v___y_3960_, v___x_4000_);
if (v_isShared_3967_ == 0)
{
lean_ctor_set(v___x_3966_, 0, v___x_3987_);
v___x_4003_ = v___x_3966_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v___x_3987_);
v___x_4003_ = v_reuseFailAlloc_4004_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
return v___x_4003_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_3955_ = stack[0].m_obj;
lean_object* v_msg_3956_ = stack[1].m_obj;
lean_object* v___y_3957_ = stack[2].m_obj;
lean_object* v___y_3958_ = stack[3].m_obj;
lean_object* v___y_3959_ = stack[4].m_obj;
lean_object* v___y_3960_ = stack[5].m_obj;
lean_object* v_res_4010_;
v_res_4010_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg(v_cls_3955_, v_msg_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_);
stack->m_obj
 = v_res_4010_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg___boxed(lean_object* v_cls_4011_, lean_object* v_msg_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_){
_start:
{
lean_object* v_res_4018_; 
v_res_4018_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg(v_cls_4011_, v_msg_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_);
lean_dec(v___y_4016_);
lean_dec_ref(v___y_4015_);
lean_dec(v___y_4014_);
lean_dec_ref(v___y_4013_);
return v_res_4018_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__3(void){
_start:
{
lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; 
v___x_4026_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__0));
v___x_4027_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__2));
v___x_4028_ = l_Lean_Name_append(v___x_4027_, v___x_4026_);
return v___x_4028_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__5(void){
_start:
{
lean_object* v___x_4030_; lean_object* v___x_4031_; 
v___x_4030_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__4));
v___x_4031_ = l_Lean_stringToMessageData(v___x_4030_);
return v___x_4031_;
}
}
lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds(lean_object* v_declNames_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_){
_start:
{
lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; uint8_t v___x_4045_; lean_object* v___x_4046_; 
v___x_4040_ = lean_box(0);
v___x_4041_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__14));
v___x_4042_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__0));
v___x_4043_ = lean_unsigned_to_nat(0u);
v___x_4044_ = lean_array_get_borrowed(v___x_4040_, v_declNames_4032_, v___x_4043_);
v___x_4045_ = 1;
lean_inc(v___x_4044_);
v___x_4046_ = l_Lean_Elab_Deriving_mkContext(v___x_4041_, v___x_4042_, v___x_4044_, v___x_4045_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_, v_a_4038_);
if (lean_obj_tag(v___x_4046_) == 0)
{
lean_object* v_a_4047_; lean_object* v___x_4048_; 
v_a_4047_ = lean_ctor_get(v___x_4046_, 0);
lean_inc_n(v_a_4047_, 2);
lean_dec_ref_known(v___x_4046_, 1);
v___x_4048_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions(v_a_4047_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_, v_a_4038_);
if (lean_obj_tag(v___x_4048_) == 0)
{
lean_object* v_a_4049_; lean_object* v___x_4050_; 
v_a_4049_ = lean_ctor_get(v___x_4048_, 0);
lean_inc(v_a_4049_);
lean_dec_ref_known(v___x_4048_, 1);
v___x_4050_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds(v_a_4047_, v_declNames_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_, v_a_4038_);
if (lean_obj_tag(v___x_4050_) == 0)
{
lean_object* v_toCold_4051_; lean_object* v_options_4052_; lean_object* v_a_4053_; lean_object* v___x_4055_; uint8_t v_isShared_4056_; uint8_t v_isSharedCheck_4095_; 
v_toCold_4051_ = lean_ctor_get(v_a_4037_, 0);
v_options_4052_ = lean_ctor_get(v_toCold_4051_, 2);
v_a_4053_ = lean_ctor_get(v___x_4050_, 0);
v_isSharedCheck_4095_ = !lean_is_exclusive(v___x_4050_);
if (v_isSharedCheck_4095_ == 0)
{
v___x_4055_ = v___x_4050_;
v_isShared_4056_ = v_isSharedCheck_4095_;
goto v_resetjp_4054_;
}
else
{
lean_inc(v_a_4053_);
lean_dec(v___x_4050_);
v___x_4055_ = lean_box(0);
v_isShared_4056_ = v_isSharedCheck_4095_;
goto v_resetjp_4054_;
}
v_resetjp_4054_:
{
lean_object* v_inheritedTraceOptions_4057_; uint8_t v_hasTrace_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; 
v_inheritedTraceOptions_4057_ = lean_ctor_get(v_toCold_4051_, 11);
v_hasTrace_4058_ = lean_ctor_get_uint8(v_options_4052_, sizeof(void*)*1);
v___x_4059_ = lean_unsigned_to_nat(1u);
v___x_4060_ = lean_mk_empty_array_with_capacity(v___x_4059_);
v___x_4061_ = lean_array_push(v___x_4060_, v_a_4049_);
v___x_4062_ = l_Array_append___redArg(v___x_4061_, v_a_4053_);
lean_dec(v_a_4053_);
if (v_hasTrace_4058_ == 0)
{
lean_object* v___x_4064_; 
if (v_isShared_4056_ == 0)
{
lean_ctor_set(v___x_4055_, 0, v___x_4062_);
v___x_4064_ = v___x_4055_;
goto v_reusejp_4063_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v___x_4062_);
v___x_4064_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4063_;
}
v_reusejp_4063_:
{
return v___x_4064_;
}
}
else
{
lean_object* v___x_4066_; lean_object* v___x_4067_; uint8_t v___x_4068_; 
v___x_4066_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__0));
v___x_4067_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__3, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__3_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__3);
v___x_4068_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4057_, v_options_4052_, v___x_4067_);
if (v___x_4068_ == 0)
{
lean_object* v___x_4070_; 
if (v_isShared_4056_ == 0)
{
lean_ctor_set(v___x_4055_, 0, v___x_4062_);
v___x_4070_ = v___x_4055_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v___x_4062_);
v___x_4070_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
return v___x_4070_;
}
}
else
{
lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; 
lean_del_object(v___x_4055_);
v___x_4072_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__5, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__5_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__5);
lean_inc_ref(v___x_4062_);
v___x_4073_ = lean_array_to_list(v___x_4062_);
v___x_4074_ = lean_box(0);
v___x_4075_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__0(v___x_4073_, v___x_4074_);
v___x_4076_ = l_Lean_MessageData_ofList(v___x_4075_);
v___x_4077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4077_, 0, v___x_4072_);
lean_ctor_set(v___x_4077_, 1, v___x_4076_);
v___x_4078_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg(v___x_4066_, v___x_4077_, v_a_4035_, v_a_4036_, v_a_4037_, v_a_4038_);
if (lean_obj_tag(v___x_4078_) == 0)
{
lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4085_; 
v_isSharedCheck_4085_ = !lean_is_exclusive(v___x_4078_);
if (v_isSharedCheck_4085_ == 0)
{
lean_object* v_unused_4086_; 
v_unused_4086_ = lean_ctor_get(v___x_4078_, 0);
lean_dec(v_unused_4086_);
v___x_4080_ = v___x_4078_;
v_isShared_4081_ = v_isSharedCheck_4085_;
goto v_resetjp_4079_;
}
else
{
lean_dec(v___x_4078_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4085_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v___x_4083_; 
if (v_isShared_4081_ == 0)
{
lean_ctor_set(v___x_4080_, 0, v___x_4062_);
v___x_4083_ = v___x_4080_;
goto v_reusejp_4082_;
}
else
{
lean_object* v_reuseFailAlloc_4084_; 
v_reuseFailAlloc_4084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4084_, 0, v___x_4062_);
v___x_4083_ = v_reuseFailAlloc_4084_;
goto v_reusejp_4082_;
}
v_reusejp_4082_:
{
return v___x_4083_;
}
}
}
else
{
lean_object* v_a_4087_; lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4094_; 
lean_dec_ref(v___x_4062_);
v_a_4087_ = lean_ctor_get(v___x_4078_, 0);
v_isSharedCheck_4094_ = !lean_is_exclusive(v___x_4078_);
if (v_isSharedCheck_4094_ == 0)
{
v___x_4089_ = v___x_4078_;
v_isShared_4090_ = v_isSharedCheck_4094_;
goto v_resetjp_4088_;
}
else
{
lean_inc(v_a_4087_);
lean_dec(v___x_4078_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4094_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
lean_object* v___x_4092_; 
if (v_isShared_4090_ == 0)
{
v___x_4092_ = v___x_4089_;
goto v_reusejp_4091_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v_a_4087_);
v___x_4092_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4091_;
}
v_reusejp_4091_:
{
return v___x_4092_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4096_; lean_object* v___x_4098_; uint8_t v_isShared_4099_; uint8_t v_isSharedCheck_4103_; 
lean_dec(v_a_4049_);
v_a_4096_ = lean_ctor_get(v___x_4050_, 0);
v_isSharedCheck_4103_ = !lean_is_exclusive(v___x_4050_);
if (v_isSharedCheck_4103_ == 0)
{
v___x_4098_ = v___x_4050_;
v_isShared_4099_ = v_isSharedCheck_4103_;
goto v_resetjp_4097_;
}
else
{
lean_inc(v_a_4096_);
lean_dec(v___x_4050_);
v___x_4098_ = lean_box(0);
v_isShared_4099_ = v_isSharedCheck_4103_;
goto v_resetjp_4097_;
}
v_resetjp_4097_:
{
lean_object* v___x_4101_; 
if (v_isShared_4099_ == 0)
{
v___x_4101_ = v___x_4098_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4102_; 
v_reuseFailAlloc_4102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4102_, 0, v_a_4096_);
v___x_4101_ = v_reuseFailAlloc_4102_;
goto v_reusejp_4100_;
}
v_reusejp_4100_:
{
return v___x_4101_;
}
}
}
}
else
{
lean_object* v_a_4104_; lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4111_; 
lean_dec(v_a_4047_);
v_a_4104_ = lean_ctor_get(v___x_4048_, 0);
v_isSharedCheck_4111_ = !lean_is_exclusive(v___x_4048_);
if (v_isSharedCheck_4111_ == 0)
{
v___x_4106_ = v___x_4048_;
v_isShared_4107_ = v_isSharedCheck_4111_;
goto v_resetjp_4105_;
}
else
{
lean_inc(v_a_4104_);
lean_dec(v___x_4048_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4111_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
lean_object* v___x_4109_; 
if (v_isShared_4107_ == 0)
{
v___x_4109_ = v___x_4106_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4110_; 
v_reuseFailAlloc_4110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4110_, 0, v_a_4104_);
v___x_4109_ = v_reuseFailAlloc_4110_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
return v___x_4109_;
}
}
}
}
else
{
lean_object* v_a_4112_; lean_object* v___x_4114_; uint8_t v_isShared_4115_; uint8_t v_isSharedCheck_4119_; 
v_a_4112_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4119_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4119_ == 0)
{
v___x_4114_ = v___x_4046_;
v_isShared_4115_ = v_isSharedCheck_4119_;
goto v_resetjp_4113_;
}
else
{
lean_inc(v_a_4112_);
lean_dec(v___x_4046_);
v___x_4114_ = lean_box(0);
v_isShared_4115_ = v_isSharedCheck_4119_;
goto v_resetjp_4113_;
}
v_resetjp_4113_:
{
lean_object* v___x_4117_; 
if (v_isShared_4115_ == 0)
{
v___x_4117_ = v___x_4114_;
goto v_reusejp_4116_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v_a_4112_);
v___x_4117_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4116_;
}
v_reusejp_4116_:
{
return v___x_4117_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_0interp(lean_interpreter_value* stack)
{
lean_object* v_declNames_4032_ = stack[0].m_obj;
lean_object* v_a_4033_ = stack[1].m_obj;
lean_object* v_a_4034_ = stack[2].m_obj;
lean_object* v_a_4035_ = stack[3].m_obj;
lean_object* v_a_4036_ = stack[4].m_obj;
lean_object* v_a_4037_ = stack[5].m_obj;
lean_object* v_a_4038_ = stack[6].m_obj;
lean_object* v_res_4120_;
v_res_4120_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds(v_declNames_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_, v_a_4038_);
stack->m_obj
 = v_res_4120_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___boxed(lean_object* v_declNames_4121_, lean_object* v_a_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_){
_start:
{
lean_object* v_res_4129_; 
v_res_4129_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds(v_declNames_4121_, v_a_4122_, v_a_4123_, v_a_4124_, v_a_4125_, v_a_4126_, v_a_4127_);
lean_dec(v_a_4127_);
lean_dec_ref(v_a_4126_);
lean_dec(v_a_4125_);
lean_dec_ref(v_a_4124_);
lean_dec(v_a_4123_);
lean_dec_ref(v_a_4122_);
lean_dec_ref(v_declNames_4121_);
return v_res_4129_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1(lean_object* v_cls_4130_, lean_object* v_msg_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_){
_start:
{
lean_object* v___x_4139_; 
v___x_4139_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___redArg(v_cls_4130_, v_msg_4131_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_);
return v___x_4139_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_4130_ = stack[0].m_obj;
lean_object* v_msg_4131_ = stack[1].m_obj;
lean_object* v___y_4132_ = stack[2].m_obj;
lean_object* v___y_4133_ = stack[3].m_obj;
lean_object* v___y_4134_ = stack[4].m_obj;
lean_object* v___y_4135_ = stack[5].m_obj;
lean_object* v___y_4136_ = stack[6].m_obj;
lean_object* v___y_4137_ = stack[7].m_obj;
lean_object* v_res_4140_;
v_res_4140_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1(v_cls_4130_, v_msg_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_);
stack->m_obj
 = v_res_4140_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1___boxed(lean_object* v_cls_4141_, lean_object* v_msg_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_){
_start:
{
lean_object* v_res_4150_; 
v_res_4150_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1(v_cls_4141_, v_msg_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_);
lean_dec(v___y_4148_);
lean_dec_ref(v___y_4147_);
lean_dec(v___y_4146_);
lean_dec_ref(v___y_4145_);
lean_dec(v___y_4144_);
lean_dec_ref(v___y_4143_);
return v_res_4150_;
}
}
lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0___redArg(lean_object* v_declName_4151_, lean_object* v___y_4152_){
_start:
{
lean_object* v___x_4154_; lean_object* v_env_4155_; uint8_t v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; 
v___x_4154_ = lean_st_ref_get(v___y_4152_);
v_env_4155_ = lean_ctor_get(v___x_4154_, 0);
lean_inc_ref(v_env_4155_);
lean_dec(v___x_4154_);
v___x_4156_ = l_Lean_isInductiveCore(v_env_4155_, v_declName_4151_);
v___x_4157_ = lean_box(v___x_4156_);
v___x_4158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4158_, 0, v___x_4157_);
return v___x_4158_;
}
}
LEAN_EXPORT void l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_4151_ = stack[0].m_obj;
lean_object* v___y_4152_ = stack[1].m_obj;
lean_object* v_res_4159_;
v_res_4159_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0___redArg(v_declName_4151_, v___y_4152_);
stack->m_obj
 = v_res_4159_;
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0___redArg___boxed(lean_object* v_declName_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_){
_start:
{
lean_object* v_res_4163_; 
v_res_4163_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0___redArg(v_declName_4160_, v___y_4161_);
lean_dec(v___y_4161_);
return v_res_4163_;
}
}
lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0(lean_object* v_declName_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_){
_start:
{
lean_object* v___x_4168_; 
v___x_4168_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0___redArg(v_declName_4164_, v___y_4166_);
return v___x_4168_;
}
}
LEAN_EXPORT void l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_4164_ = stack[0].m_obj;
lean_object* v___y_4165_ = stack[1].m_obj;
lean_object* v___y_4166_ = stack[2].m_obj;
lean_object* v_res_4169_;
v_res_4169_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0(v_declName_4164_, v___y_4165_, v___y_4166_);
stack->m_obj
 = v_res_4169_;
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0___boxed(lean_object* v_declName_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_){
_start:
{
lean_object* v_res_4174_; 
v_res_4174_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0(v_declName_4170_, v___y_4171_, v___y_4172_);
lean_dec(v___y_4172_);
lean_dec_ref(v___y_4171_);
return v_res_4174_;
}
}
lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__0(uint8_t v_____do__lift_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_){
_start:
{
if (v_____do__lift_4175_ == 0)
{
uint8_t v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; 
v___x_4179_ = 1;
v___x_4180_ = lean_box(v___x_4179_);
v___x_4181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4181_, 0, v___x_4180_);
return v___x_4181_;
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
LEAN_EXPORT void l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_____do__lift_4175_ = stack[0].m_num;
lean_object* v___y_4176_ = stack[1].m_obj;
lean_object* v___y_4177_ = stack[2].m_obj;
lean_object* v_res_4185_;
v_res_4185_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__0(v_____do__lift_4175_, v___y_4176_, v___y_4177_);
stack->m_obj
 = v_res_4185_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__0___boxed(lean_object* v_____do__lift_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_){
_start:
{
uint8_t v_____do__lift_1540__boxed_4190_; lean_object* v_res_4191_; 
v_____do__lift_1540__boxed_4190_ = lean_unbox(v_____do__lift_4186_);
v_res_4191_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__0(v_____do__lift_1540__boxed_4190_, v___y_4187_, v___y_4188_);
lean_dec(v___y_4188_);
lean_dec_ref(v___y_4187_);
return v_res_4191_;
}
}
lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1_spec__1(lean_object* v_o_4192_, lean_object* v_k_4193_, uint8_t v_v_4194_){
_start:
{
lean_object* v_map_4195_; uint8_t v_hasTrace_4196_; lean_object* v___x_4198_; uint8_t v_isShared_4199_; uint8_t v_isSharedCheck_4210_; 
v_map_4195_ = lean_ctor_get(v_o_4192_, 0);
v_hasTrace_4196_ = lean_ctor_get_uint8(v_o_4192_, sizeof(void*)*1);
v_isSharedCheck_4210_ = !lean_is_exclusive(v_o_4192_);
if (v_isSharedCheck_4210_ == 0)
{
v___x_4198_ = v_o_4192_;
v_isShared_4199_ = v_isSharedCheck_4210_;
goto v_resetjp_4197_;
}
else
{
lean_inc(v_map_4195_);
lean_dec(v_o_4192_);
v___x_4198_ = lean_box(0);
v_isShared_4199_ = v_isSharedCheck_4210_;
goto v_resetjp_4197_;
}
v_resetjp_4197_:
{
lean_object* v___x_4200_; lean_object* v___x_4201_; 
v___x_4200_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4200_, 0, v_v_4194_);
lean_inc(v_k_4193_);
v___x_4201_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4193_, v___x_4200_, v_map_4195_);
if (v_hasTrace_4196_ == 0)
{
lean_object* v___x_4202_; uint8_t v___x_4203_; lean_object* v___x_4205_; 
v___x_4202_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__2));
v___x_4203_ = l_Lean_Name_isPrefixOf(v___x_4202_, v_k_4193_);
lean_dec(v_k_4193_);
if (v_isShared_4199_ == 0)
{
lean_ctor_set(v___x_4198_, 0, v___x_4201_);
v___x_4205_ = v___x_4198_;
goto v_reusejp_4204_;
}
else
{
lean_object* v_reuseFailAlloc_4206_; 
v_reuseFailAlloc_4206_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4206_, 0, v___x_4201_);
v___x_4205_ = v_reuseFailAlloc_4206_;
goto v_reusejp_4204_;
}
v_reusejp_4204_:
{
lean_ctor_set_uint8(v___x_4205_, sizeof(void*)*1, v___x_4203_);
return v___x_4205_;
}
}
else
{
lean_object* v___x_4208_; 
lean_dec(v_k_4193_);
if (v_isShared_4199_ == 0)
{
lean_ctor_set(v___x_4198_, 0, v___x_4201_);
v___x_4208_ = v___x_4198_;
goto v_reusejp_4207_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v___x_4201_);
lean_ctor_set_uint8(v_reuseFailAlloc_4209_, sizeof(void*)*1, v_hasTrace_4196_);
v___x_4208_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4207_;
}
v_reusejp_4207_:
{
return v___x_4208_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_4192_ = stack[0].m_obj;
lean_object* v_k_4193_ = stack[1].m_obj;
uint8_t v_v_4194_ = stack[2].m_num;
lean_object* v_res_4211_;
v_res_4211_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1_spec__1(v_o_4192_, v_k_4193_, v_v_4194_);
stack->m_obj
 = v_res_4211_;
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1_spec__1___boxed(lean_object* v_o_4212_, lean_object* v_k_4213_, lean_object* v_v_4214_){
_start:
{
uint8_t v_v_boxed_4215_; lean_object* v_res_4216_; 
v_v_boxed_4215_ = lean_unbox(v_v_4214_);
v_res_4216_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1_spec__1(v_o_4212_, v_k_4213_, v_v_boxed_4215_);
return v_res_4216_;
}
}
lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1(lean_object* v_opts_4217_, lean_object* v_opt_4218_, uint8_t v_val_4219_){
_start:
{
lean_object* v_name_4220_; lean_object* v___x_4221_; 
v_name_4220_ = lean_ctor_get(v_opt_4218_, 0);
lean_inc(v_name_4220_);
lean_dec_ref(v_opt_4218_);
v___x_4221_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1_spec__1(v_opts_4217_, v_name_4220_, v_val_4219_);
return v___x_4221_;
}
}
LEAN_EXPORT void l_Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_4217_ = stack[0].m_obj;
lean_object* v_opt_4218_ = stack[1].m_obj;
uint8_t v_val_4219_ = stack[2].m_num;
lean_object* v_res_4222_;
v_res_4222_ = l_Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1(v_opts_4217_, v_opt_4218_, v_val_4219_);
stack->m_obj
 = v_res_4222_;
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1___boxed(lean_object* v_opts_4223_, lean_object* v_opt_4224_, lean_object* v_val_4225_){
_start:
{
uint8_t v_val_boxed_4226_; lean_object* v_res_4227_; 
v_val_boxed_4226_ = lean_unbox(v_val_4225_);
v_res_4227_ = l_Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1(v_opts_4223_, v_opt_4224_, v_val_boxed_4226_);
return v_res_4227_;
}
}
lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__1(uint8_t v_a_4228_, lean_object* v_scope_4229_){
_start:
{
lean_object* v_header_4230_; lean_object* v_opts_4231_; lean_object* v_currNamespace_4232_; lean_object* v_openDecls_4233_; lean_object* v_levelNames_4234_; lean_object* v_varDecls_4235_; lean_object* v_varUIds_4236_; lean_object* v_includedVars_4237_; lean_object* v_omittedVars_4238_; uint8_t v_isNoncomputable_4239_; uint8_t v_isPublic_4240_; uint8_t v_isMeta_4241_; lean_object* v_attrs_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4251_; 
v_header_4230_ = lean_ctor_get(v_scope_4229_, 0);
v_opts_4231_ = lean_ctor_get(v_scope_4229_, 1);
v_currNamespace_4232_ = lean_ctor_get(v_scope_4229_, 2);
v_openDecls_4233_ = lean_ctor_get(v_scope_4229_, 3);
v_levelNames_4234_ = lean_ctor_get(v_scope_4229_, 4);
v_varDecls_4235_ = lean_ctor_get(v_scope_4229_, 5);
v_varUIds_4236_ = lean_ctor_get(v_scope_4229_, 6);
v_includedVars_4237_ = lean_ctor_get(v_scope_4229_, 7);
v_omittedVars_4238_ = lean_ctor_get(v_scope_4229_, 8);
v_isNoncomputable_4239_ = lean_ctor_get_uint8(v_scope_4229_, sizeof(void*)*10);
v_isPublic_4240_ = lean_ctor_get_uint8(v_scope_4229_, sizeof(void*)*10 + 1);
v_isMeta_4241_ = lean_ctor_get_uint8(v_scope_4229_, sizeof(void*)*10 + 2);
v_attrs_4242_ = lean_ctor_get(v_scope_4229_, 9);
v_isSharedCheck_4251_ = !lean_is_exclusive(v_scope_4229_);
if (v_isSharedCheck_4251_ == 0)
{
v___x_4244_ = v_scope_4229_;
v_isShared_4245_ = v_isSharedCheck_4251_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_attrs_4242_);
lean_inc(v_omittedVars_4238_);
lean_inc(v_includedVars_4237_);
lean_inc(v_varUIds_4236_);
lean_inc(v_varDecls_4235_);
lean_inc(v_levelNames_4234_);
lean_inc(v_openDecls_4233_);
lean_inc(v_currNamespace_4232_);
lean_inc(v_opts_4231_);
lean_inc(v_header_4230_);
lean_dec(v_scope_4229_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4251_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4249_; 
v___x_4246_ = l_Lean_Elab_autoImplicit;
v___x_4247_ = l_Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1(v_opts_4231_, v___x_4246_, v_a_4228_);
if (v_isShared_4245_ == 0)
{
lean_ctor_set(v___x_4244_, 1, v___x_4247_);
v___x_4249_ = v___x_4244_;
goto v_reusejp_4248_;
}
else
{
lean_object* v_reuseFailAlloc_4250_; 
v_reuseFailAlloc_4250_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v_reuseFailAlloc_4250_, 0, v_header_4230_);
lean_ctor_set(v_reuseFailAlloc_4250_, 1, v___x_4247_);
lean_ctor_set(v_reuseFailAlloc_4250_, 2, v_currNamespace_4232_);
lean_ctor_set(v_reuseFailAlloc_4250_, 3, v_openDecls_4233_);
lean_ctor_set(v_reuseFailAlloc_4250_, 4, v_levelNames_4234_);
lean_ctor_set(v_reuseFailAlloc_4250_, 5, v_varDecls_4235_);
lean_ctor_set(v_reuseFailAlloc_4250_, 6, v_varUIds_4236_);
lean_ctor_set(v_reuseFailAlloc_4250_, 7, v_includedVars_4237_);
lean_ctor_set(v_reuseFailAlloc_4250_, 8, v_omittedVars_4238_);
lean_ctor_set(v_reuseFailAlloc_4250_, 9, v_attrs_4242_);
lean_ctor_set_uint8(v_reuseFailAlloc_4250_, sizeof(void*)*10, v_isNoncomputable_4239_);
lean_ctor_set_uint8(v_reuseFailAlloc_4250_, sizeof(void*)*10 + 1, v_isPublic_4240_);
lean_ctor_set_uint8(v_reuseFailAlloc_4250_, sizeof(void*)*10 + 2, v_isMeta_4241_);
v___x_4249_ = v_reuseFailAlloc_4250_;
goto v_reusejp_4248_;
}
v_reusejp_4248_:
{
return v___x_4249_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_4228_ = stack[0].m_num;
lean_object* v_scope_4229_ = stack[1].m_obj;
lean_object* v_res_4252_;
v_res_4252_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__1(v_a_4228_, v_scope_4229_);
stack->m_obj
 = v_res_4252_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__1___boxed(lean_object* v_a_4253_, lean_object* v_scope_4254_){
_start:
{
uint8_t v_a_1627__boxed_4255_; lean_object* v_res_4256_; 
v_a_1627__boxed_4255_ = lean_unbox(v_a_4253_);
v_res_4256_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__1(v_a_1627__boxed_4255_, v_scope_4254_);
return v_res_4256_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__2(lean_object* v_as_4257_, size_t v_i_4258_, size_t v_stop_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_){
_start:
{
uint8_t v___x_4267_; 
v___x_4267_ = lean_usize_dec_eq(v_i_4258_, v_stop_4259_);
if (v___x_4267_ == 0)
{
uint8_t v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; 
v___x_4268_ = 1;
v___x_4269_ = lean_array_uget_borrowed(v_as_4257_, v_i_4258_);
lean_inc(v___x_4269_);
v___x_4270_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0___redArg(v___x_4269_, v___y_4261_);
if (lean_obj_tag(v___x_4270_) == 0)
{
lean_object* v_a_4271_; lean_object* v___x_4273_; uint8_t v_isShared_4274_; uint8_t v_isSharedCheck_4280_; 
v_a_4271_ = lean_ctor_get(v___x_4270_, 0);
v_isSharedCheck_4280_ = !lean_is_exclusive(v___x_4270_);
if (v_isSharedCheck_4280_ == 0)
{
v___x_4273_ = v___x_4270_;
v_isShared_4274_ = v_isSharedCheck_4280_;
goto v_resetjp_4272_;
}
else
{
lean_inc(v_a_4271_);
lean_dec(v___x_4270_);
v___x_4273_ = lean_box(0);
v_isShared_4274_ = v_isSharedCheck_4280_;
goto v_resetjp_4272_;
}
v_resetjp_4272_:
{
uint8_t v___x_4275_; 
v___x_4275_ = lean_unbox(v_a_4271_);
lean_dec(v_a_4271_);
if (v___x_4275_ == 0)
{
lean_object* v___x_4276_; lean_object* v___x_4278_; 
v___x_4276_ = lean_box(v___x_4268_);
if (v_isShared_4274_ == 0)
{
lean_ctor_set(v___x_4273_, 0, v___x_4276_);
v___x_4278_ = v___x_4273_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v___x_4276_);
v___x_4278_ = v_reuseFailAlloc_4279_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
return v___x_4278_;
}
}
else
{
lean_del_object(v___x_4273_);
goto v___jp_4263_;
}
}
}
else
{
if (lean_obj_tag(v___x_4270_) == 0)
{
lean_object* v_a_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4290_; 
v_a_4281_ = lean_ctor_get(v___x_4270_, 0);
v_isSharedCheck_4290_ = !lean_is_exclusive(v___x_4270_);
if (v_isSharedCheck_4290_ == 0)
{
v___x_4283_ = v___x_4270_;
v_isShared_4284_ = v_isSharedCheck_4290_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_a_4281_);
lean_dec(v___x_4270_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4290_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
uint8_t v___x_4285_; 
v___x_4285_ = lean_unbox(v_a_4281_);
lean_dec(v_a_4281_);
if (v___x_4285_ == 0)
{
lean_del_object(v___x_4283_);
goto v___jp_4263_;
}
else
{
lean_object* v___x_4286_; lean_object* v___x_4288_; 
v___x_4286_ = lean_box(v___x_4268_);
if (v_isShared_4284_ == 0)
{
lean_ctor_set_tag(v___x_4283_, 0);
lean_ctor_set(v___x_4283_, 0, v___x_4286_);
v___x_4288_ = v___x_4283_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4289_; 
v_reuseFailAlloc_4289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4289_, 0, v___x_4286_);
v___x_4288_ = v_reuseFailAlloc_4289_;
goto v_reusejp_4287_;
}
v_reusejp_4287_:
{
return v___x_4288_;
}
}
}
}
else
{
return v___x_4270_;
}
}
}
else
{
uint8_t v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; 
v___x_4291_ = 0;
v___x_4292_ = lean_box(v___x_4291_);
v___x_4293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4293_, 0, v___x_4292_);
return v___x_4293_;
}
v___jp_4263_:
{
size_t v___x_4264_; size_t v___x_4265_; 
v___x_4264_ = ((size_t)1ULL);
v___x_4265_ = lean_usize_add(v_i_4258_, v___x_4264_);
v_i_4258_ = v___x_4265_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4257_ = stack[0].m_obj;
size_t v_i_4258_ = stack[1].m_num;
size_t v_stop_4259_ = stack[2].m_num;
lean_object* v___y_4260_ = stack[3].m_obj;
lean_object* v___y_4261_ = stack[4].m_obj;
lean_object* v_res_4294_;
v_res_4294_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__2(v_as_4257_, v_i_4258_, v_stop_4259_, v___y_4260_, v___y_4261_);
stack->m_obj
 = v_res_4294_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__2___boxed(lean_object* v_as_4295_, lean_object* v_i_4296_, lean_object* v_stop_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_){
_start:
{
size_t v_i_boxed_4301_; size_t v_stop_boxed_4302_; lean_object* v_res_4303_; 
v_i_boxed_4301_ = lean_unbox_usize(v_i_4296_);
lean_dec(v_i_4296_);
v_stop_boxed_4302_ = lean_unbox_usize(v_stop_4297_);
lean_dec(v_stop_4297_);
v_res_4303_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__2(v_as_4295_, v_i_boxed_4301_, v_stop_boxed_4302_, v___y_4298_, v___y_4299_);
lean_dec(v___y_4299_);
lean_dec_ref(v___y_4298_);
lean_dec_ref(v_as_4295_);
return v_res_4303_;
}
}
lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler(lean_object* v_declNames_4304_, lean_object* v_a_4305_, lean_object* v_a_4306_){
_start:
{
lean_object* v___x_4308_; lean_object* v___x_4309_; uint8_t v_a_4311_; lean_object* v___y_4352_; uint8_t v___x_4356_; 
v___x_4308_ = lean_unsigned_to_nat(0u);
v___x_4309_ = lean_array_get_size(v_declNames_4304_);
v___x_4356_ = lean_nat_dec_lt(v___x_4308_, v___x_4309_);
if (v___x_4356_ == 0)
{
lean_object* v___x_4357_; 
v___x_4357_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__0(v___x_4356_, v_a_4305_, v_a_4306_);
v___y_4352_ = v___x_4357_;
goto v___jp_4351_;
}
else
{
if (v___x_4356_ == 0)
{
v_a_4311_ = v___x_4356_;
goto v___jp_4310_;
}
else
{
size_t v___x_4358_; size_t v___x_4359_; lean_object* v___x_4360_; 
v___x_4358_ = ((size_t)0ULL);
v___x_4359_ = lean_usize_of_nat(v___x_4309_);
v___x_4360_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__2(v_declNames_4304_, v___x_4358_, v___x_4359_, v_a_4305_, v_a_4306_);
if (lean_obj_tag(v___x_4360_) == 0)
{
lean_object* v_a_4361_; uint8_t v___x_4362_; lean_object* v___x_4363_; 
v_a_4361_ = lean_ctor_get(v___x_4360_, 0);
lean_inc(v_a_4361_);
lean_dec_ref_known(v___x_4360_, 1);
v___x_4362_ = lean_unbox(v_a_4361_);
lean_dec(v_a_4361_);
v___x_4363_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__0(v___x_4362_, v_a_4305_, v_a_4306_);
v___y_4352_ = v___x_4363_;
goto v___jp_4351_;
}
else
{
v___y_4352_ = v___x_4360_;
goto v___jp_4351_;
}
}
}
v___jp_4310_:
{
uint8_t v___x_4312_; 
v___x_4312_ = lean_nat_dec_lt(v___x_4308_, v___x_4309_);
if (v___x_4312_ == 0)
{
lean_object* v___x_4313_; lean_object* v___x_4314_; 
lean_dec_ref(v_declNames_4304_);
v___x_4313_ = lean_box(v___x_4312_);
v___x_4314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4314_, 0, v___x_4313_);
return v___x_4314_;
}
else
{
lean_object* v___x_4315_; lean_object* v___f_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; 
v___x_4315_ = lean_box(v_a_4311_);
v___f_4316_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__1___boxed), 2, 1);
lean_closure_set(v___f_4316_, 0, v___x_4315_);
v___x_4317_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___boxed), 8, 1);
lean_closure_set(v___x_4317_, 0, v_declNames_4304_);
v___x_4318_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftTermElabM___boxed), 5, 2);
lean_closure_set(v___x_4318_, 0, lean_box(0));
lean_closure_set(v___x_4318_, 1, v___x_4317_);
v___x_4319_ = l_Lean_Elab_Command_withFreshMacroScope___redArg(v___x_4318_, v_a_4305_, v_a_4306_);
if (lean_obj_tag(v___x_4319_) == 0)
{
lean_object* v_a_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; 
v_a_4320_ = lean_ctor_get(v___x_4319_, 0);
lean_inc(v_a_4320_);
lean_dec_ref_known(v___x_4319_, 1);
v___x_4321_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_4322_ = lean_box(2);
v___x_4323_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4323_, 0, v___x_4322_);
lean_ctor_set(v___x_4323_, 1, v___x_4321_);
lean_ctor_set(v___x_4323_, 2, v_a_4320_);
v___x_4324_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(v___x_4324_, 0, v___x_4323_);
v___x_4325_ = l_Lean_Elab_Command_withScope___redArg(v___f_4316_, v___x_4324_, v_a_4305_, v_a_4306_);
if (lean_obj_tag(v___x_4325_) == 0)
{
lean_object* v___x_4327_; uint8_t v_isShared_4328_; uint8_t v_isSharedCheck_4333_; 
v_isSharedCheck_4333_ = !lean_is_exclusive(v___x_4325_);
if (v_isSharedCheck_4333_ == 0)
{
lean_object* v_unused_4334_; 
v_unused_4334_ = lean_ctor_get(v___x_4325_, 0);
lean_dec(v_unused_4334_);
v___x_4327_ = v___x_4325_;
v_isShared_4328_ = v_isSharedCheck_4333_;
goto v_resetjp_4326_;
}
else
{
lean_dec(v___x_4325_);
v___x_4327_ = lean_box(0);
v_isShared_4328_ = v_isSharedCheck_4333_;
goto v_resetjp_4326_;
}
v_resetjp_4326_:
{
lean_object* v___x_4329_; lean_object* v___x_4331_; 
v___x_4329_ = lean_box(v_a_4311_);
if (v_isShared_4328_ == 0)
{
lean_ctor_set(v___x_4327_, 0, v___x_4329_);
v___x_4331_ = v___x_4327_;
goto v_reusejp_4330_;
}
else
{
lean_object* v_reuseFailAlloc_4332_; 
v_reuseFailAlloc_4332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4332_, 0, v___x_4329_);
v___x_4331_ = v_reuseFailAlloc_4332_;
goto v_reusejp_4330_;
}
v_reusejp_4330_:
{
return v___x_4331_;
}
}
}
else
{
lean_object* v_a_4335_; lean_object* v___x_4337_; uint8_t v_isShared_4338_; uint8_t v_isSharedCheck_4342_; 
v_a_4335_ = lean_ctor_get(v___x_4325_, 0);
v_isSharedCheck_4342_ = !lean_is_exclusive(v___x_4325_);
if (v_isSharedCheck_4342_ == 0)
{
v___x_4337_ = v___x_4325_;
v_isShared_4338_ = v_isSharedCheck_4342_;
goto v_resetjp_4336_;
}
else
{
lean_inc(v_a_4335_);
lean_dec(v___x_4325_);
v___x_4337_ = lean_box(0);
v_isShared_4338_ = v_isSharedCheck_4342_;
goto v_resetjp_4336_;
}
v_resetjp_4336_:
{
lean_object* v___x_4340_; 
if (v_isShared_4338_ == 0)
{
v___x_4340_ = v___x_4337_;
goto v_reusejp_4339_;
}
else
{
lean_object* v_reuseFailAlloc_4341_; 
v_reuseFailAlloc_4341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4341_, 0, v_a_4335_);
v___x_4340_ = v_reuseFailAlloc_4341_;
goto v_reusejp_4339_;
}
v_reusejp_4339_:
{
return v___x_4340_;
}
}
}
}
else
{
lean_object* v_a_4343_; lean_object* v___x_4345_; uint8_t v_isShared_4346_; uint8_t v_isSharedCheck_4350_; 
lean_dec_ref(v___f_4316_);
v_a_4343_ = lean_ctor_get(v___x_4319_, 0);
v_isSharedCheck_4350_ = !lean_is_exclusive(v___x_4319_);
if (v_isSharedCheck_4350_ == 0)
{
v___x_4345_ = v___x_4319_;
v_isShared_4346_ = v_isSharedCheck_4350_;
goto v_resetjp_4344_;
}
else
{
lean_inc(v_a_4343_);
lean_dec(v___x_4319_);
v___x_4345_ = lean_box(0);
v_isShared_4346_ = v_isSharedCheck_4350_;
goto v_resetjp_4344_;
}
v_resetjp_4344_:
{
lean_object* v___x_4348_; 
if (v_isShared_4346_ == 0)
{
v___x_4348_ = v___x_4345_;
goto v_reusejp_4347_;
}
else
{
lean_object* v_reuseFailAlloc_4349_; 
v_reuseFailAlloc_4349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4349_, 0, v_a_4343_);
v___x_4348_ = v_reuseFailAlloc_4349_;
goto v_reusejp_4347_;
}
v_reusejp_4347_:
{
return v___x_4348_;
}
}
}
}
}
v___jp_4351_:
{
if (lean_obj_tag(v___y_4352_) == 0)
{
lean_object* v_a_4353_; uint8_t v___x_4354_; 
v_a_4353_ = lean_ctor_get(v___y_4352_, 0);
v___x_4354_ = lean_unbox(v_a_4353_);
if (v___x_4354_ == 0)
{
lean_dec_ref(v_declNames_4304_);
return v___y_4352_;
}
else
{
uint8_t v___x_4355_; 
lean_inc(v_a_4353_);
lean_dec_ref_known(v___y_4352_, 1);
v___x_4355_ = lean_unbox(v_a_4353_);
lean_dec(v_a_4353_);
v_a_4311_ = v___x_4355_;
goto v___jp_4310_;
}
}
else
{
lean_dec_ref(v_declNames_4304_);
return v___y_4352_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_0interp(lean_interpreter_value* stack)
{
lean_object* v_declNames_4304_ = stack[0].m_obj;
lean_object* v_a_4305_ = stack[1].m_obj;
lean_object* v_a_4306_ = stack[2].m_obj;
lean_object* v_res_4364_;
v_res_4364_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler(v_declNames_4304_, v_a_4305_, v_a_4306_);
stack->m_obj
 = v_res_4364_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___boxed(lean_object* v_declNames_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_){
_start:
{
lean_object* v_res_4369_; 
v_res_4369_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler(v_declNames_4365_, v_a_4366_, v_a_4367_);
lean_dec(v_a_4367_);
lean_dec_ref(v_a_4366_);
return v_res_4369_;
}
}
lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; 
v___x_4437_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__14));
v___x_4438_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__0_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_));
v___x_4439_ = l_Lean_Elab_registerDerivingHandler(v___x_4437_, v___x_4438_);
if (lean_obj_tag(v___x_4439_) == 0)
{
lean_object* v___x_4440_; uint8_t v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; 
lean_dec_ref_known(v___x_4439_, 1);
v___x_4440_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__0));
v___x_4441_ = 0;
v___x_4442_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__25_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_));
v___x_4443_ = l_Lean_registerTraceClass(v___x_4440_, v___x_4441_, v___x_4442_);
return v___x_4443_;
}
else
{
return v___x_4439_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4444_;
v_res_4444_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_();
stack->m_obj
 = v_res_4444_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2____boxed(lean_object* v_a_4445_){
_start:
{
lean_object* v_res_4446_; 
v_res_4446_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_();
return v_res_4446_;
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
