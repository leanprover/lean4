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
lean_inc_ref(v_a_76_);
v___x_87_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg(v_args_73_, v___x_85_, v___x_86_, v_f_72_, v_a_76_);
return v___x_87_;
}
}
else
{
size_t v___x_88_; size_t v___x_89_; lean_object* v___x_90_; 
v___x_88_ = ((size_t)0ULL);
v___x_89_ = lean_usize_of_nat(v___x_80_);
lean_inc_ref(v_a_76_);
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
lean_inc_ref(v___y_105_);
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
lean_inc_ref(v_a_316_);
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
lean_inc_ref(v_a_316_);
v___x_337_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v___x_336_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_);
return v___x_337_;
}
else
{
lean_object* v_ref_338_; lean_object* v___x_339_; size_t v_sz_340_; size_t v___x_341_; lean_object* v_levels_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v_args_346_; uint8_t v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; size_t v_sz_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_362_; 
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
lean_dec_ref(v_a_377_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0(lean_object* v_00_u03b1_385_, lean_object* v_msg_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v___x_394_; 
lean_inc_ref(v___y_387_);
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
lean_dec_ref(v___y_397_);
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
lean_inc(v___y_433_);
lean_inc_ref(v___y_432_);
lean_inc(v___y_431_);
lean_inc_ref(v___y_430_);
lean_inc(v___y_427_);
lean_inc_ref(v___y_426_);
v___x_435_ = lean_apply_9(v_k_425_, v_b_428_, v_c_429_, v___y_426_, v___y_427_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, lean_box(0));
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg___lam__0___boxed(lean_object* v_k_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v_b_439_, lean_object* v_c_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg___lam__0(v_k_436_, v___y_437_, v___y_438_, v_b_439_, v_c_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_);
lean_dec(v___y_444_);
lean_dec_ref(v___y_443_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg(lean_object* v_type_447_, lean_object* v_k_448_, uint8_t v_cleanupAnnotations_449_, uint8_t v_whnfType_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v___f_458_; lean_object* v___x_459_; 
lean_inc(v___y_452_);
lean_inc_ref(v___y_451_);
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
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
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
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
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
lean_dec_ref(v___y_547_);
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
lean_dec_ref(v___y_547_);
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
lean_dec_ref(v___y_547_);
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
lean_dec(v___y_640_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0(lean_object* v_argNames_685_, size_t v___x_686_, lean_object* v_a_687_, lean_object* v_name_688_, lean_object* v_xs_689_, lean_object* v_x_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; size_t v_sz_703_; lean_object* v___x_704_; 
v___x_698_ = lean_unsigned_to_nat(0u);
v___x_699_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__0));
v___x_700_ = lean_array_get_size(v_xs_689_);
v___x_701_ = l_Array_toSubarray___redArg(v_xs_689_, v___x_698_, v___x_700_);
v___x_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_699_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
v_sz_703_ = lean_array_size(v_argNames_685_);
lean_inc_ref(v___y_695_);
v___x_704_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg(v_argNames_685_, v_sz_703_, v___x_686_, v___x_702_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; lean_object* v_fst_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_755_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_a_705_);
lean_dec_ref(v___x_704_);
v_fst_706_ = lean_ctor_get(v_a_705_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v_a_705_);
if (v_isSharedCheck_755_ == 0)
{
lean_object* v_unused_756_; 
v_unused_756_ = lean_ctor_get(v_a_705_, 1);
lean_dec(v_unused_756_);
v___x_708_ = v_a_705_;
v_isShared_709_ = v_isSharedCheck_755_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_fst_706_);
lean_dec(v_a_705_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_755_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v_ref_710_; lean_object* v_quotContext_711_; lean_object* v_currMacroScope_712_; uint8_t v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___y_724_; lean_object* v___x_741_; 
v_ref_710_ = lean_ctor_get(v___y_695_, 5);
v_quotContext_711_ = lean_ctor_get(v___y_695_, 10);
v_currMacroScope_712_ = lean_ctor_get(v___y_695_, 11);
v___x_713_ = 0;
v___x_714_ = l_Lean_SourceInfo_fromRef(v_ref_710_, v___x_713_);
v___x_715_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_716_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__2, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__2_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__2);
v___x_717_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__4));
lean_inc(v_currMacroScope_712_);
lean_inc(v_quotContext_711_);
v___x_718_ = l_Lean_addMacroScope(v_quotContext_711_, v___x_717_, v_currMacroScope_712_);
v___x_719_ = lean_box(0);
v___x_720_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__10));
lean_inc(v___x_714_);
v___x_721_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_721_, 0, v___x_714_);
lean_ctor_set(v___x_721_, 1, v___x_716_);
lean_ctor_set(v___x_721_, 2, v___x_718_);
lean_ctor_set(v___x_721_, 3, v___x_720_);
v___x_722_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
lean_inc(v_name_688_);
v___x_741_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_719_, v_name_688_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v___x_742_; 
v___x_742_ = l_Lean_quoteNameMk(v_name_688_);
v___y_724_ = v___x_742_;
goto v___jp_723_;
}
else
{
lean_object* v_val_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
lean_dec(v_name_688_);
v_val_743_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_val_743_);
lean_dec_ref(v___x_741_);
v___x_744_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__16));
v___x_745_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__17));
v___x_746_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__18));
v___x_747_ = lean_string_intercalate(v___x_746_, v_val_743_);
v___x_748_ = lean_string_append(v___x_745_, v___x_747_);
lean_dec_ref(v___x_747_);
v___x_749_ = lean_box(2);
v___x_750_ = l_Lean_Syntax_mkNameLit(v___x_748_, v___x_749_);
v___x_751_ = lean_unsigned_to_nat(1u);
v___x_752_ = lean_mk_empty_array_with_capacity(v___x_751_);
v___x_753_ = lean_array_push(v___x_752_, v___x_750_);
v___x_754_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_754_, 0, v___x_749_);
lean_ctor_set(v___x_754_, 1, v___x_744_);
lean_ctor_set(v___x_754_, 2, v___x_753_);
v___y_724_ = v___x_754_;
goto v___jp_723_;
}
v___jp_723_:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_728_; 
v___x_725_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__12));
v___x_726_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__13));
lean_inc(v___x_714_);
if (v_isShared_709_ == 0)
{
lean_ctor_set_tag(v___x_708_, 2);
lean_ctor_set(v___x_708_, 1, v___x_726_);
lean_ctor_set(v___x_708_, 0, v___x_714_);
v___x_728_ = v___x_708_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_714_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v___x_726_);
v___x_728_ = v_reuseFailAlloc_740_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_729_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_730_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__9));
v___x_731_ = l_Lean_Syntax_SepArray_ofElems(v___x_730_, v_a_687_);
v___x_732_ = l_Array_append___redArg(v___x_729_, v___x_731_);
lean_dec_ref(v___x_731_);
lean_inc(v___x_714_);
v___x_733_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_733_, 0, v___x_714_);
lean_ctor_set(v___x_733_, 1, v___x_722_);
lean_ctor_set(v___x_733_, 2, v___x_732_);
v___x_734_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__14));
lean_inc(v___x_714_);
v___x_735_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_714_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
lean_inc(v___x_714_);
v___x_736_ = l_Lean_Syntax_node3(v___x_714_, v___x_725_, v___x_728_, v___x_733_, v___x_735_);
lean_inc(v___x_714_);
v___x_737_ = l_Lean_Syntax_node2(v___x_714_, v___x_722_, v___y_724_, v___x_736_);
v___x_738_ = l_Lean_Syntax_node2(v___x_714_, v___x_715_, v___x_721_, v___x_737_);
v___x_739_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm(v___x_738_, v_fst_706_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec(v_fst_706_);
return v___x_739_;
}
}
}
}
else
{
lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_764_; 
lean_dec_ref(v___y_695_);
lean_dec(v_name_688_);
v_a_757_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_764_ == 0)
{
v___x_759_ = v___x_704_;
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___x_704_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_762_; 
if (v_isShared_760_ == 0)
{
v___x_762_ = v___x_759_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_a_757_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___boxed(lean_object* v_argNames_765_, lean_object* v___x_766_, lean_object* v_a_767_, lean_object* v_name_768_, lean_object* v_xs_769_, lean_object* v_x_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
size_t v___x_11659__boxed_778_; lean_object* v_res_779_; 
v___x_11659__boxed_778_ = lean_unbox_usize(v___x_766_);
lean_dec(v___x_766_);
v_res_779_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0(v_argNames_765_, v___x_11659__boxed_778_, v_a_767_, v_name_768_, v_xs_769_, v_x_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
lean_dec(v___y_776_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec_ref(v_x_770_);
lean_dec_ref(v_a_767_);
lean_dec_ref(v_argNames_765_);
return v_res_779_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__0));
v___x_782_ = l_String_toRawSubstring_x27(v___x_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg(size_t v_sz_798_, size_t v_i_799_, lean_object* v_bs_800_, lean_object* v___y_801_){
_start:
{
uint8_t v___x_803_; 
v___x_803_ = lean_usize_dec_lt(v_i_799_, v_sz_798_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; 
lean_dec_ref(v___y_801_);
v___x_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_804_, 0, v_bs_800_);
return v___x_804_;
}
else
{
lean_object* v_ref_805_; lean_object* v_quotContext_806_; lean_object* v_currMacroScope_807_; lean_object* v_v_808_; lean_object* v___x_809_; lean_object* v_bs_x27_810_; uint8_t v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; size_t v___x_827_; size_t v___x_828_; lean_object* v___x_829_; 
v_ref_805_ = lean_ctor_get(v___y_801_, 5);
v_quotContext_806_ = lean_ctor_get(v___y_801_, 10);
v_currMacroScope_807_ = lean_ctor_get(v___y_801_, 11);
v_v_808_ = lean_array_uget(v_bs_800_, v_i_799_);
v___x_809_ = lean_unsigned_to_nat(0u);
v_bs_x27_810_ = lean_array_uset(v_bs_800_, v_i_799_, v___x_809_);
v___x_811_ = 0;
v___x_812_ = l_Lean_SourceInfo_fromRef(v_ref_805_, v___x_811_);
v___x_813_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__6));
v___x_814_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__1);
v___x_815_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__3));
lean_inc(v_currMacroScope_807_);
lean_inc(v_quotContext_806_);
v___x_816_ = l_Lean_addMacroScope(v_quotContext_806_, v___x_815_, v_currMacroScope_807_);
v___x_817_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__7));
lean_inc(v___x_812_);
v___x_818_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_818_, 0, v___x_812_);
lean_ctor_set(v___x_818_, 1, v___x_814_);
lean_ctor_set(v___x_818_, 2, v___x_816_);
lean_ctor_set(v___x_818_, 3, v___x_817_);
v___x_819_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__7));
lean_inc(v___x_812_);
v___x_820_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_812_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
v___x_821_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_822_ = lean_mk_syntax_ident(v_v_808_);
lean_inc(v___x_812_);
v___x_823_ = l_Lean_Syntax_node1(v___x_812_, v___x_821_, v___x_822_);
v___x_824_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__10));
lean_inc(v___x_812_);
v___x_825_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_812_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
v___x_826_ = l_Lean_Syntax_node4(v___x_812_, v___x_813_, v___x_818_, v___x_820_, v___x_823_, v___x_825_);
v___x_827_ = ((size_t)1ULL);
v___x_828_ = lean_usize_add(v_i_799_, v___x_827_);
v___x_829_ = lean_array_uset(v_bs_x27_810_, v_i_799_, v___x_826_);
v_i_799_ = v___x_828_;
v_bs_800_ = v___x_829_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___boxed(lean_object* v_sz_831_, lean_object* v_i_832_, lean_object* v_bs_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
size_t v_sz_boxed_836_; size_t v_i_boxed_837_; lean_object* v_res_838_; 
v_sz_boxed_836_ = lean_unbox_usize(v_sz_831_);
lean_dec(v_sz_831_);
v_i_boxed_837_ = lean_unbox_usize(v_i_832_);
lean_dec(v_i_832_);
v_res_838_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg(v_sz_boxed_836_, v_i_boxed_837_, v_bs_833_, v___y_834_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr(lean_object* v_indVal_841_, lean_object* v_argNames_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_){
_start:
{
lean_object* v_toConstantVal_850_; lean_object* v_name_851_; lean_object* v_levelParams_852_; lean_object* v_type_853_; lean_object* v___x_854_; size_t v_sz_855_; size_t v___x_856_; lean_object* v___x_857_; 
v_toConstantVal_850_ = lean_ctor_get(v_indVal_841_, 0);
lean_inc_ref(v_toConstantVal_850_);
lean_dec_ref(v_indVal_841_);
v_name_851_ = lean_ctor_get(v_toConstantVal_850_, 0);
lean_inc(v_name_851_);
v_levelParams_852_ = lean_ctor_get(v_toConstantVal_850_, 1);
lean_inc(v_levelParams_852_);
v_type_853_ = lean_ctor_get(v_toConstantVal_850_, 2);
lean_inc_ref(v_type_853_);
lean_dec_ref(v_toConstantVal_850_);
v___x_854_ = lean_array_mk(v_levelParams_852_);
v_sz_855_ = lean_array_size(v___x_854_);
v___x_856_ = ((size_t)0ULL);
lean_inc_ref(v_a_847_);
v___x_857_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg(v_sz_855_, v___x_856_, v___x_854_, v_a_847_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; lean_object* v___x_859_; lean_object* v___f_860_; uint8_t v___x_861_; lean_object* v___x_862_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_a_858_);
lean_dec_ref(v___x_857_);
v___x_859_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___boxed__const__1));
v___f_860_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___boxed), 13, 4);
lean_closure_set(v___f_860_, 0, v_argNames_842_);
lean_closure_set(v___f_860_, 1, v___x_859_);
lean_closure_set(v___f_860_, 2, v_a_858_);
lean_closure_set(v___f_860_, 3, v_name_851_);
v___x_861_ = 0;
v___x_862_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg(v_type_853_, v___f_860_, v___x_861_, v___x_861_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_);
return v___x_862_;
}
else
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
lean_dec_ref(v_type_853_);
lean_dec(v_name_851_);
lean_dec_ref(v_argNames_842_);
v_a_863_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_870_ == 0)
{
v___x_865_ = v___x_857_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_857_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_a_863_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___boxed(lean_object* v_indVal_871_, lean_object* v_argNames_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr(v_indVal_871_, v_argNames_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
lean_dec(v_a_878_);
lean_dec_ref(v_a_877_);
lean_dec(v_a_876_);
lean_dec_ref(v_a_875_);
lean_dec(v_a_874_);
lean_dec_ref(v_a_873_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0(size_t v_sz_881_, size_t v_i_882_, lean_object* v_bs_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v___x_891_; 
lean_inc_ref(v___y_888_);
v___x_891_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg(v_sz_881_, v_i_882_, v_bs_883_, v___y_888_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___boxed(lean_object* v_sz_892_, lean_object* v_i_893_, lean_object* v_bs_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
size_t v_sz_boxed_902_; size_t v_i_boxed_903_; lean_object* v_res_904_; 
v_sz_boxed_902_ = lean_unbox_usize(v_sz_892_);
lean_dec(v_sz_892_);
v_i_boxed_903_ = lean_unbox_usize(v_i_893_);
lean_dec(v_i_893_);
v_res_904_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0(v_sz_boxed_902_, v_i_boxed_903_, v_bs_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1(lean_object* v_as_905_, size_t v_sz_906_, size_t v_i_907_, lean_object* v_b_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v___x_916_; 
lean_inc_ref(v___y_913_);
v___x_916_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg(v_as_905_, v_sz_906_, v_i_907_, v_b_908_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___boxed(lean_object* v_as_917_, lean_object* v_sz_918_, lean_object* v_i_919_, lean_object* v_b_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
size_t v_sz_boxed_928_; size_t v_i_boxed_929_; lean_object* v_res_930_; 
v_sz_boxed_928_ = lean_unbox_usize(v_sz_918_);
lean_dec(v_sz_918_);
v_i_boxed_929_ = lean_unbox_usize(v_i_919_);
lean_dec(v_i_919_);
v_res_930_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1(v_as_917_, v_sz_boxed_928_, v_i_boxed_929_, v_b_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec_ref(v_as_917_);
return v_res_930_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_937_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__2));
v___x_938_ = l_String_toRawSubstring_x27(v___x_937_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg(size_t v_sz_941_, size_t v_i_942_, lean_object* v_bs_943_, lean_object* v___y_944_){
_start:
{
uint8_t v___x_946_; 
v___x_946_ = lean_usize_dec_lt(v_i_942_, v_sz_941_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; 
lean_dec_ref(v___y_944_);
v___x_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_947_, 0, v_bs_943_);
return v___x_947_;
}
else
{
lean_object* v_ref_948_; lean_object* v_quotContext_949_; lean_object* v_currMacroScope_950_; lean_object* v_v_951_; lean_object* v___x_952_; lean_object* v_bs_x27_953_; uint8_t v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; size_t v___x_965_; size_t v___x_966_; lean_object* v___x_967_; 
v_ref_948_ = lean_ctor_get(v___y_944_, 5);
v_quotContext_949_ = lean_ctor_get(v___y_944_, 10);
v_currMacroScope_950_ = lean_ctor_get(v___y_944_, 11);
v_v_951_ = lean_array_uget(v_bs_943_, v_i_942_);
v___x_952_ = lean_unsigned_to_nat(0u);
v_bs_x27_953_ = lean_array_uset(v_bs_943_, v_i_942_, v___x_952_);
v___x_954_ = 0;
v___x_955_ = l_Lean_SourceInfo_fromRef(v_ref_948_, v___x_954_);
v___x_956_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__1));
v___x_957_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__18));
lean_inc(v___x_955_);
v___x_958_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_955_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
v___x_959_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__2);
v___x_960_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___closed__3));
lean_inc(v_currMacroScope_950_);
lean_inc(v_quotContext_949_);
v___x_961_ = l_Lean_addMacroScope(v_quotContext_949_, v___x_960_, v_currMacroScope_950_);
v___x_962_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__7));
lean_inc(v___x_955_);
v___x_963_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_963_, 0, v___x_955_);
lean_ctor_set(v___x_963_, 1, v___x_959_);
lean_ctor_set(v___x_963_, 2, v___x_961_);
lean_ctor_set(v___x_963_, 3, v___x_962_);
v___x_964_ = l_Lean_Syntax_node3(v___x_955_, v___x_956_, v_v_951_, v___x_958_, v___x_963_);
v___x_965_ = ((size_t)1ULL);
v___x_966_ = lean_usize_add(v_i_942_, v___x_965_);
v___x_967_ = lean_array_uset(v_bs_x27_953_, v_i_942_, v___x_964_);
v_i_942_ = v___x_966_;
v_bs_943_ = v___x_967_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg___boxed(lean_object* v_sz_969_, lean_object* v_i_970_, lean_object* v_bs_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
size_t v_sz_boxed_974_; size_t v_i_boxed_975_; lean_object* v_res_976_; 
v_sz_boxed_974_ = lean_unbox_usize(v_sz_969_);
lean_dec(v_sz_969_);
v_i_boxed_975_ = lean_unbox_usize(v_i_970_);
lean_dec(v_i_970_);
v_res_976_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg(v_sz_boxed_974_, v_i_boxed_975_, v_bs_971_, v___y_972_);
return v_res_976_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l_instMonadEIO(lean_box(0));
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1(lean_object* v_msg_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v_toApplicative_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1085_; 
v___x_992_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__0);
v___x_993_ = l_StateRefT_x27_instMonad___redArg(v___x_992_);
v_toApplicative_994_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1085_ == 0)
{
lean_object* v_unused_1086_; 
v_unused_1086_ = lean_ctor_get(v___x_993_, 1);
lean_dec(v_unused_1086_);
v___x_996_ = v___x_993_;
v_isShared_997_ = v_isSharedCheck_1085_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_toApplicative_994_);
lean_dec(v___x_993_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1085_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v_toFunctor_998_; lean_object* v_toSeq_999_; lean_object* v_toSeqLeft_1000_; lean_object* v_toSeqRight_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1083_; 
v_toFunctor_998_ = lean_ctor_get(v_toApplicative_994_, 0);
v_toSeq_999_ = lean_ctor_get(v_toApplicative_994_, 2);
v_toSeqLeft_1000_ = lean_ctor_get(v_toApplicative_994_, 3);
v_toSeqRight_1001_ = lean_ctor_get(v_toApplicative_994_, 4);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_toApplicative_994_);
if (v_isSharedCheck_1083_ == 0)
{
lean_object* v_unused_1084_; 
v_unused_1084_ = lean_ctor_get(v_toApplicative_994_, 1);
lean_dec(v_unused_1084_);
v___x_1003_ = v_toApplicative_994_;
v_isShared_1004_ = v_isSharedCheck_1083_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_toSeqRight_1001_);
lean_inc(v_toSeqLeft_1000_);
lean_inc(v_toSeq_999_);
lean_inc(v_toFunctor_998_);
lean_dec(v_toApplicative_994_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1083_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___f_1005_; lean_object* v___f_1006_; lean_object* v___f_1007_; lean_object* v___f_1008_; lean_object* v___x_1009_; lean_object* v___f_1010_; lean_object* v___f_1011_; lean_object* v___f_1012_; lean_object* v___x_1014_; 
v___f_1005_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__1));
v___f_1006_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__2));
lean_inc_ref(v_toFunctor_998_);
v___f_1007_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1007_, 0, v_toFunctor_998_);
v___f_1008_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1008_, 0, v_toFunctor_998_);
v___x_1009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___f_1007_);
lean_ctor_set(v___x_1009_, 1, v___f_1008_);
v___f_1010_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1010_, 0, v_toSeqRight_1001_);
v___f_1011_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1011_, 0, v_toSeqLeft_1000_);
v___f_1012_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1012_, 0, v_toSeq_999_);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 4, v___f_1010_);
lean_ctor_set(v___x_1003_, 3, v___f_1011_);
lean_ctor_set(v___x_1003_, 2, v___f_1012_);
lean_ctor_set(v___x_1003_, 1, v___f_1005_);
lean_ctor_set(v___x_1003_, 0, v___x_1009_);
v___x_1014_ = v___x_1003_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1009_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v___f_1005_);
lean_ctor_set(v_reuseFailAlloc_1082_, 2, v___f_1012_);
lean_ctor_set(v_reuseFailAlloc_1082_, 3, v___f_1011_);
lean_ctor_set(v_reuseFailAlloc_1082_, 4, v___f_1010_);
v___x_1014_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
lean_object* v___x_1016_; 
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 1, v___f_1006_);
lean_ctor_set(v___x_996_, 0, v___x_1014_);
v___x_1016_ = v___x_996_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1014_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v___f_1006_);
v___x_1016_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
lean_object* v___x_1017_; lean_object* v_toApplicative_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1079_; 
v___x_1017_ = l_StateRefT_x27_instMonad___redArg(v___x_1016_);
v_toApplicative_1018_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1079_ == 0)
{
lean_object* v_unused_1080_; 
v_unused_1080_ = lean_ctor_get(v___x_1017_, 1);
lean_dec(v_unused_1080_);
v___x_1020_ = v___x_1017_;
v_isShared_1021_ = v_isSharedCheck_1079_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_toApplicative_1018_);
lean_dec(v___x_1017_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1079_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v_toFunctor_1022_; lean_object* v_toSeq_1023_; lean_object* v_toSeqLeft_1024_; lean_object* v_toSeqRight_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1077_; 
v_toFunctor_1022_ = lean_ctor_get(v_toApplicative_1018_, 0);
v_toSeq_1023_ = lean_ctor_get(v_toApplicative_1018_, 2);
v_toSeqLeft_1024_ = lean_ctor_get(v_toApplicative_1018_, 3);
v_toSeqRight_1025_ = lean_ctor_get(v_toApplicative_1018_, 4);
v_isSharedCheck_1077_ = !lean_is_exclusive(v_toApplicative_1018_);
if (v_isSharedCheck_1077_ == 0)
{
lean_object* v_unused_1078_; 
v_unused_1078_ = lean_ctor_get(v_toApplicative_1018_, 1);
lean_dec(v_unused_1078_);
v___x_1027_ = v_toApplicative_1018_;
v_isShared_1028_ = v_isSharedCheck_1077_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_toSeqRight_1025_);
lean_inc(v_toSeqLeft_1024_);
lean_inc(v_toSeq_1023_);
lean_inc(v_toFunctor_1022_);
lean_dec(v_toApplicative_1018_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1077_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___f_1029_; lean_object* v___f_1030_; lean_object* v___f_1031_; lean_object* v___f_1032_; lean_object* v___x_1033_; lean_object* v___f_1034_; lean_object* v___f_1035_; lean_object* v___f_1036_; lean_object* v___x_1038_; 
v___f_1029_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__3));
v___f_1030_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1022_);
v___f_1031_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1031_, 0, v_toFunctor_1022_);
v___f_1032_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1032_, 0, v_toFunctor_1022_);
v___x_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___f_1031_);
lean_ctor_set(v___x_1033_, 1, v___f_1032_);
v___f_1034_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1034_, 0, v_toSeqRight_1025_);
v___f_1035_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1035_, 0, v_toSeqLeft_1024_);
v___f_1036_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1036_, 0, v_toSeq_1023_);
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 4, v___f_1034_);
lean_ctor_set(v___x_1027_, 3, v___f_1035_);
lean_ctor_set(v___x_1027_, 2, v___f_1036_);
lean_ctor_set(v___x_1027_, 1, v___f_1029_);
lean_ctor_set(v___x_1027_, 0, v___x_1033_);
v___x_1038_ = v___x_1027_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1033_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v___f_1029_);
lean_ctor_set(v_reuseFailAlloc_1076_, 2, v___f_1036_);
lean_ctor_set(v_reuseFailAlloc_1076_, 3, v___f_1035_);
lean_ctor_set(v_reuseFailAlloc_1076_, 4, v___f_1034_);
v___x_1038_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
lean_object* v___x_1040_; 
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 1, v___f_1030_);
lean_ctor_set(v___x_1020_, 0, v___x_1038_);
v___x_1040_ = v___x_1020_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1038_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v___f_1030_);
v___x_1040_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
lean_object* v___x_1041_; lean_object* v_toApplicative_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1073_; 
v___x_1041_ = l_StateRefT_x27_instMonad___redArg(v___x_1040_);
v_toApplicative_1042_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1073_ == 0)
{
lean_object* v_unused_1074_; 
v_unused_1074_ = lean_ctor_get(v___x_1041_, 1);
lean_dec(v_unused_1074_);
v___x_1044_ = v___x_1041_;
v_isShared_1045_ = v_isSharedCheck_1073_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_toApplicative_1042_);
lean_dec(v___x_1041_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1073_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v_toFunctor_1046_; lean_object* v_toSeq_1047_; lean_object* v_toSeqLeft_1048_; lean_object* v_toSeqRight_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1071_; 
v_toFunctor_1046_ = lean_ctor_get(v_toApplicative_1042_, 0);
v_toSeq_1047_ = lean_ctor_get(v_toApplicative_1042_, 2);
v_toSeqLeft_1048_ = lean_ctor_get(v_toApplicative_1042_, 3);
v_toSeqRight_1049_ = lean_ctor_get(v_toApplicative_1042_, 4);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_toApplicative_1042_);
if (v_isSharedCheck_1071_ == 0)
{
lean_object* v_unused_1072_; 
v_unused_1072_ = lean_ctor_get(v_toApplicative_1042_, 1);
lean_dec(v_unused_1072_);
v___x_1051_ = v_toApplicative_1042_;
v_isShared_1052_ = v_isSharedCheck_1071_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_toSeqRight_1049_);
lean_inc(v_toSeqLeft_1048_);
lean_inc(v_toSeq_1047_);
lean_inc(v_toFunctor_1046_);
lean_dec(v_toApplicative_1042_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1071_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___f_1053_; lean_object* v___f_1054_; lean_object* v___f_1055_; lean_object* v___f_1056_; lean_object* v___x_1057_; lean_object* v___f_1058_; lean_object* v___f_1059_; lean_object* v___f_1060_; lean_object* v___x_1062_; 
v___f_1053_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__5));
v___f_1054_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___closed__6));
lean_inc_ref(v_toFunctor_1046_);
v___f_1055_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1055_, 0, v_toFunctor_1046_);
v___f_1056_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1056_, 0, v_toFunctor_1046_);
v___x_1057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___f_1055_);
lean_ctor_set(v___x_1057_, 1, v___f_1056_);
v___f_1058_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1058_, 0, v_toSeqRight_1049_);
v___f_1059_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1059_, 0, v_toSeqLeft_1048_);
v___f_1060_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1060_, 0, v_toSeq_1047_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 4, v___f_1058_);
lean_ctor_set(v___x_1051_, 3, v___f_1059_);
lean_ctor_set(v___x_1051_, 2, v___f_1060_);
lean_ctor_set(v___x_1051_, 1, v___f_1053_);
lean_ctor_set(v___x_1051_, 0, v___x_1057_);
v___x_1062_ = v___x_1051_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1057_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v___f_1053_);
lean_ctor_set(v_reuseFailAlloc_1070_, 2, v___f_1060_);
lean_ctor_set(v_reuseFailAlloc_1070_, 3, v___f_1059_);
lean_ctor_set(v_reuseFailAlloc_1070_, 4, v___f_1058_);
v___x_1062_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
lean_object* v___x_1064_; 
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 1, v___f_1054_);
lean_ctor_set(v___x_1044_, 0, v___x_1062_);
v___x_1064_ = v___x_1044_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1062_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v___f_1054_);
v___x_1064_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_28016__overap_1067_; lean_object* v___x_1068_; 
v___x_1065_ = lean_box(0);
v___x_1066_ = l_instInhabitedOfMonad___redArg(v___x_1064_, v___x_1065_);
v___x_28016__overap_1067_ = lean_panic_fn(v___x_1066_, v_msg_984_);
lean_inc(v___y_990_);
lean_inc_ref(v___y_989_);
lean_inc(v___y_988_);
lean_inc_ref(v___y_987_);
lean_inc(v___y_986_);
lean_inc_ref(v___y_985_);
v___x_1068_ = lean_apply_7(v___x_28016__overap_1067_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, lean_box(0));
return v___x_1068_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1___boxed(lean_object* v_msg_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1(v_msg_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
return v_res_1095_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1096_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__17));
v___x_1097_ = l_Lean_stringToMessageData(v___x_1096_);
return v___x_1097_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__2(void){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1099_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__1));
v___x_1100_ = l_Lean_stringToMessageData(v___x_1099_);
return v___x_1100_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__6(void){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1104_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__5));
v___x_1105_ = lean_unsigned_to_nat(11u);
v___x_1106_ = lean_unsigned_to_nat(122u);
v___x_1107_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__4));
v___x_1108_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__3));
v___x_1109_ = l_mkPanicMessageWithDecl(v___x_1108_, v___x_1107_, v___x_1106_, v___x_1105_, v___x_1104_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1(lean_object* v_constName_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v___x_1126_; lean_object* v_env_1127_; uint8_t v___x_1128_; lean_object* v___x_1129_; 
v___x_1126_ = lean_st_ref_get(v___y_1116_);
v_env_1127_ = lean_ctor_get(v___x_1126_, 0);
lean_inc_ref(v_env_1127_);
lean_dec(v___x_1126_);
v___x_1128_ = 0;
lean_inc(v_constName_1110_);
v___x_1129_ = l_Lean_Environment_findAsync_x3f(v_env_1127_, v_constName_1110_, v___x_1128_);
if (lean_obj_tag(v___x_1129_) == 1)
{
lean_object* v_val_1130_; uint8_t v_kind_1131_; 
v_val_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_val_1130_);
lean_dec_ref(v___x_1129_);
v_kind_1131_ = lean_ctor_get_uint8(v_val_1130_, sizeof(void*)*3);
if (v_kind_1131_ == 6)
{
lean_object* v___x_1132_; 
v___x_1132_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1130_);
if (lean_obj_tag(v___x_1132_) == 6)
{
lean_object* v_val_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
lean_dec(v_constName_1110_);
v_val_1133_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1132_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_val_1133_);
lean_dec(v___x_1132_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
lean_ctor_set_tag(v___x_1135_, 0);
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_val_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
else
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
lean_dec_ref(v___x_1132_);
v___x_1141_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__6, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__6_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__6);
v___x_1142_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1_spec__1(v___x_1141_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1151_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1145_ = v___x_1142_;
v_isShared_1146_ = v_isSharedCheck_1151_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1142_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1151_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
if (lean_obj_tag(v_a_1143_) == 0)
{
lean_del_object(v___x_1145_);
goto v___jp_1118_;
}
else
{
lean_object* v_val_1147_; lean_object* v___x_1149_; 
lean_dec(v_constName_1110_);
v_val_1147_ = lean_ctor_get(v_a_1143_, 0);
lean_inc(v_val_1147_);
lean_dec_ref(v_a_1143_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v_val_1147_);
v___x_1149_ = v___x_1145_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_val_1147_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
else
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
lean_dec(v_constName_1110_);
v_a_1152_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1142_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1142_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
}
else
{
lean_dec(v_val_1130_);
goto v___jp_1118_;
}
}
else
{
lean_dec(v___x_1129_);
goto v___jp_1118_;
}
v___jp_1118_:
{
lean_object* v___x_1119_; uint8_t v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1119_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__0, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__0_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__0);
v___x_1120_ = 0;
v___x_1121_ = l_Lean_MessageData_ofConstName(v_constName_1110_, v___x_1120_);
v___x_1122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1119_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
v___x_1123_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__2, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__2_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___closed__2);
v___x_1124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1122_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
lean_inc_ref(v___y_1111_);
v___x_1125_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v___x_1124_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
return v___x_1125_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1___boxed(lean_object* v_constName_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1(v_constName_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__0(lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v_ref_1176_; uint8_t v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v_ref_1176_ = lean_ctor_get(v___y_1173_, 5);
v___x_1177_ = 0;
v___x_1178_ = l_Lean_SourceInfo_fromRef(v_ref_1176_, v___x_1177_);
v___x_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__0___boxed(lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__0(v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg(lean_object* v_upperBound_1195_, lean_object* v_a_1196_, lean_object* v_b_1197_, lean_object* v___y_1198_){
_start:
{
uint8_t v___x_1200_; 
v___x_1200_ = lean_nat_dec_lt(v_a_1196_, v_upperBound_1195_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; 
lean_dec(v_a_1196_);
v___x_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1201_, 0, v_b_1197_);
return v___x_1201_;
}
else
{
lean_object* v_ref_1202_; uint8_t v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v_ref_1202_ = lean_ctor_get(v___y_1198_, 5);
v___x_1203_ = 0;
v___x_1204_ = l_Lean_SourceInfo_fromRef(v_ref_1202_, v___x_1203_);
v___x_1205_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__1));
v___x_1206_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__2));
lean_inc(v___x_1204_);
v___x_1207_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1204_);
lean_ctor_set(v___x_1207_, 1, v___x_1206_);
v___x_1208_ = l_Lean_Syntax_node1(v___x_1204_, v___x_1205_, v___x_1207_);
v___x_1209_ = lean_array_push(v_b_1197_, v___x_1208_);
v___x_1210_ = lean_unsigned_to_nat(1u);
v___x_1211_ = lean_nat_add(v_a_1196_, v___x_1210_);
lean_dec(v_a_1196_);
v_a_1196_ = v___x_1211_;
v_b_1197_ = v___x_1209_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___boxed(lean_object* v_upperBound_1213_, lean_object* v_a_1214_, lean_object* v_b_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg(v_upperBound_1213_, v_a_1214_, v_b_1215_, v___y_1216_);
lean_dec_ref(v___y_1216_);
lean_dec(v_upperBound_1213_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6___redArg(lean_object* v_upperBound_1219_, lean_object* v_header_1220_, lean_object* v_xs_1221_, lean_object* v_indVal_1222_, lean_object* v_auxFunName_1223_, lean_object* v_levelInsts_1224_, lean_object* v_a_1225_, lean_object* v_b_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
uint8_t v___x_1232_; 
v___x_1232_ = lean_nat_dec_lt(v_a_1225_, v_upperBound_1219_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1233_; 
lean_dec_ref(v___y_1229_);
lean_dec(v_a_1225_);
lean_dec(v_auxFunName_1223_);
lean_dec_ref(v_indVal_1222_);
v___x_1233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1233_, 0, v_b_1226_);
return v___x_1233_;
}
else
{
lean_object* v_argNames_1234_; lean_object* v_ref_1235_; lean_object* v_quotContext_1236_; lean_object* v_currMacroScope_1237_; lean_object* v_a_1239_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v_argNames_1234_ = lean_ctor_get(v_header_1220_, 1);
v_ref_1235_ = lean_ctor_get(v___y_1229_, 5);
v_quotContext_1236_ = lean_ctor_get(v___y_1229_, 10);
v_currMacroScope_1237_ = lean_ctor_get(v___y_1229_, 11);
v___x_1260_ = l_Lean_instInhabitedExpr;
v___x_1261_ = lean_array_get_borrowed(v___x_1260_, v_xs_1221_, v_a_1225_);
lean_inc(v___y_1230_);
lean_inc_ref(v___y_1229_);
lean_inc(v___y_1228_);
lean_inc_ref(v___y_1227_);
lean_inc(v___x_1261_);
v___x_1262_ = lean_infer_type(v___x_1261_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v_toConstantVal_1263_; lean_object* v_a_1264_; lean_object* v_name_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1317_; 
v_toConstantVal_1263_ = lean_ctor_get(v_indVal_1222_, 0);
lean_inc_ref(v_toConstantVal_1263_);
v_a_1264_ = lean_ctor_get(v___x_1262_, 0);
lean_inc(v_a_1264_);
lean_dec_ref(v___x_1262_);
v_name_1265_ = lean_ctor_get(v_toConstantVal_1263_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v_toConstantVal_1263_);
if (v_isSharedCheck_1317_ == 0)
{
lean_object* v_unused_1318_; lean_object* v_unused_1319_; 
v_unused_1318_ = lean_ctor_get(v_toConstantVal_1263_, 2);
lean_dec(v_unused_1318_);
v_unused_1319_ = lean_ctor_get(v_toConstantVal_1263_, 1);
lean_dec(v_unused_1319_);
v___x_1267_ = v_toConstantVal_1263_;
v_isShared_1268_ = v_isSharedCheck_1317_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_name_1265_);
lean_dec(v_toConstantVal_1263_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1317_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; 
v___x_1269_ = lean_box(0);
v___x_1270_ = lean_array_get_borrowed(v___x_1269_, v_argNames_1234_, v_a_1225_);
lean_inc(v___x_1270_);
v___x_1271_ = lean_mk_syntax_ident(v___x_1270_);
v___x_1272_ = l_Lean_Expr_isAppOf(v_a_1264_, v_name_1265_);
lean_dec(v_name_1265_);
lean_dec(v_a_1264_);
if (v___x_1272_ == 0)
{
lean_object* v___x_1273_; 
lean_del_object(v___x_1267_);
lean_inc(v___x_1261_);
v___x_1273_ = l_Lean_Meta_isType(v___x_1261_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_a_1274_; uint8_t v___x_1275_; 
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
lean_inc(v_a_1274_);
lean_dec_ref(v___x_1273_);
v___x_1275_ = lean_unbox(v_a_1274_);
if (v___x_1275_ == 0)
{
uint8_t v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1276_ = lean_unbox(v_a_1274_);
lean_dec(v_a_1274_);
v___x_1277_ = l_Lean_SourceInfo_fromRef(v_ref_1235_, v___x_1276_);
v___x_1278_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1279_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1);
v___x_1280_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__2));
lean_inc(v_currMacroScope_1237_);
lean_inc(v_quotContext_1236_);
v___x_1281_ = l_Lean_addMacroScope(v_quotContext_1236_, v___x_1280_, v_currMacroScope_1237_);
v___x_1282_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__6));
lean_inc(v___x_1277_);
v___x_1283_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1277_);
lean_ctor_set(v___x_1283_, 1, v___x_1279_);
lean_ctor_set(v___x_1283_, 2, v___x_1281_);
lean_ctor_set(v___x_1283_, 3, v___x_1282_);
v___x_1284_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
lean_inc(v___x_1277_);
v___x_1285_ = l_Lean_Syntax_node1(v___x_1277_, v___x_1284_, v___x_1271_);
v___x_1286_ = l_Lean_Syntax_node2(v___x_1277_, v___x_1278_, v___x_1283_, v___x_1285_);
v_a_1239_ = v___x_1286_;
goto v___jp_1238_;
}
else
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
lean_dec(v_a_1274_);
v___x_1287_ = l_Lean_SourceInfo_fromRef(v_ref_1235_, v___x_1272_);
v___x_1288_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1289_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8);
v___x_1290_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__9));
lean_inc(v_currMacroScope_1237_);
lean_inc(v_quotContext_1236_);
v___x_1291_ = l_Lean_addMacroScope(v_quotContext_1236_, v___x_1290_, v_currMacroScope_1237_);
v___x_1292_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__12));
lean_inc(v___x_1287_);
v___x_1293_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1287_);
lean_ctor_set(v___x_1293_, 1, v___x_1289_);
lean_ctor_set(v___x_1293_, 2, v___x_1291_);
lean_ctor_set(v___x_1293_, 3, v___x_1292_);
v___x_1294_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
lean_inc(v___x_1287_);
v___x_1295_ = l_Lean_Syntax_node1(v___x_1287_, v___x_1294_, v___x_1271_);
v___x_1296_ = l_Lean_Syntax_node2(v___x_1287_, v___x_1288_, v___x_1293_, v___x_1295_);
v_a_1239_ = v___x_1296_;
goto v___jp_1238_;
}
}
else
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
lean_dec(v___x_1271_);
lean_dec_ref(v___y_1229_);
lean_dec_ref(v_b_1226_);
lean_dec(v_a_1225_);
lean_dec(v_auxFunName_1223_);
lean_dec_ref(v_indVal_1222_);
v_a_1297_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1299_ = v___x_1273_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1273_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_a_1297_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
else
{
uint8_t v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1314_; 
v___x_1305_ = 0;
v___x_1306_ = l_Lean_SourceInfo_fromRef(v_ref_1235_, v___x_1305_);
v___x_1307_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
lean_inc(v_auxFunName_1223_);
v___x_1308_ = lean_mk_syntax_ident(v_auxFunName_1223_);
v___x_1309_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1310_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_1311_ = l_Array_append___redArg(v___x_1310_, v_levelInsts_1224_);
v___x_1312_ = lean_array_push(v___x_1311_, v___x_1271_);
lean_inc(v___x_1306_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set_tag(v___x_1267_, 1);
lean_ctor_set(v___x_1267_, 2, v___x_1312_);
lean_ctor_set(v___x_1267_, 1, v___x_1309_);
lean_ctor_set(v___x_1267_, 0, v___x_1306_);
v___x_1314_ = v___x_1267_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1306_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v___x_1309_);
lean_ctor_set(v_reuseFailAlloc_1316_, 2, v___x_1312_);
v___x_1314_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
lean_object* v___x_1315_; 
v___x_1315_ = l_Lean_Syntax_node2(v___x_1306_, v___x_1307_, v___x_1308_, v___x_1314_);
v_a_1239_ = v___x_1315_;
goto v___jp_1238_;
}
}
}
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1327_; 
lean_dec_ref(v___y_1229_);
lean_dec_ref(v_b_1226_);
lean_dec(v_a_1225_);
lean_dec(v_auxFunName_1223_);
lean_dec_ref(v_indVal_1222_);
v_a_1320_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1322_ = v___x_1262_;
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1262_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1325_; 
if (v_isShared_1323_ == 0)
{
v___x_1325_ = v___x_1322_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1320_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
v___jp_1238_:
{
lean_object* v_fst_1240_; lean_object* v_snd_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1259_; 
v_fst_1240_ = lean_ctor_get(v_b_1226_, 0);
v_snd_1241_ = lean_ctor_get(v_b_1226_, 1);
v_isSharedCheck_1259_ = !lean_is_exclusive(v_b_1226_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1243_ = v_b_1226_;
v_isShared_1244_ = v_isSharedCheck_1259_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_snd_1241_);
lean_inc(v_fst_1240_);
lean_dec(v_b_1226_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1259_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
uint8_t v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1254_; 
v___x_1245_ = 0;
v___x_1246_ = l_Lean_SourceInfo_fromRef(v_ref_1235_, v___x_1245_);
v___x_1247_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__2));
lean_inc(v___x_1246_);
v___x_1248_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1246_);
lean_ctor_set(v___x_1248_, 1, v___x_1247_);
v___x_1249_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__1));
v___x_1250_ = l_Lean_Syntax_node1(v___x_1246_, v___x_1249_, v___x_1248_);
v___x_1251_ = lean_array_push(v_fst_1240_, v___x_1250_);
v___x_1252_ = lean_array_push(v_snd_1241_, v_a_1239_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 1, v___x_1252_);
lean_ctor_set(v___x_1243_, 0, v___x_1251_);
v___x_1254_ = v___x_1243_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1251_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = lean_unsigned_to_nat(1u);
v___x_1256_ = lean_nat_add(v_a_1225_, v___x_1255_);
lean_dec(v_a_1225_);
v_a_1225_ = v___x_1256_;
v_b_1226_ = v___x_1254_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6___redArg___boxed(lean_object* v_upperBound_1328_, lean_object* v_header_1329_, lean_object* v_xs_1330_, lean_object* v_indVal_1331_, lean_object* v_auxFunName_1332_, lean_object* v_levelInsts_1333_, lean_object* v_a_1334_, lean_object* v_b_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6___redArg(v_upperBound_1328_, v_header_1329_, v_xs_1330_, v_indVal_1331_, v_auxFunName_1332_, v_levelInsts_1333_, v_a_1334_, v_b_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
lean_dec(v___y_1339_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec_ref(v_levelInsts_1333_);
lean_dec_ref(v_xs_1330_);
lean_dec_ref(v_header_1329_);
lean_dec(v_upperBound_1328_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4___redArg(lean_object* v_upperBound_1342_, lean_object* v_header_1343_, lean_object* v_xs_1344_, lean_object* v_indVal_1345_, lean_object* v_auxFunName_1346_, lean_object* v_levelInsts_1347_, lean_object* v_a_1348_, lean_object* v_b_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
uint8_t v___x_1357_; 
v___x_1357_ = lean_nat_dec_lt(v_a_1348_, v_upperBound_1342_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; 
lean_dec_ref(v___y_1354_);
lean_dec(v_auxFunName_1346_);
lean_dec_ref(v_indVal_1345_);
v___x_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1358_, 0, v_b_1349_);
return v___x_1358_;
}
else
{
lean_object* v_argNames_1359_; lean_object* v_ref_1360_; lean_object* v_quotContext_1361_; lean_object* v_currMacroScope_1362_; lean_object* v_a_1364_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v_argNames_1359_ = lean_ctor_get(v_header_1343_, 1);
v_ref_1360_ = lean_ctor_get(v___y_1354_, 5);
v_quotContext_1361_ = lean_ctor_get(v___y_1354_, 10);
v_currMacroScope_1362_ = lean_ctor_get(v___y_1354_, 11);
v___x_1385_ = l_Lean_instInhabitedExpr;
v___x_1386_ = lean_array_get_borrowed(v___x_1385_, v_xs_1344_, v_a_1348_);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc(v___x_1386_);
v___x_1387_ = lean_infer_type(v___x_1386_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v_toConstantVal_1388_; lean_object* v_a_1389_; lean_object* v_name_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1442_; 
v_toConstantVal_1388_ = lean_ctor_get(v_indVal_1345_, 0);
lean_inc_ref(v_toConstantVal_1388_);
v_a_1389_ = lean_ctor_get(v___x_1387_, 0);
lean_inc(v_a_1389_);
lean_dec_ref(v___x_1387_);
v_name_1390_ = lean_ctor_get(v_toConstantVal_1388_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v_toConstantVal_1388_);
if (v_isSharedCheck_1442_ == 0)
{
lean_object* v_unused_1443_; lean_object* v_unused_1444_; 
v_unused_1443_ = lean_ctor_get(v_toConstantVal_1388_, 2);
lean_dec(v_unused_1443_);
v_unused_1444_ = lean_ctor_get(v_toConstantVal_1388_, 1);
lean_dec(v_unused_1444_);
v___x_1392_ = v_toConstantVal_1388_;
v_isShared_1393_ = v_isSharedCheck_1442_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_name_1390_);
lean_dec(v_toConstantVal_1388_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1442_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; uint8_t v___x_1397_; 
v___x_1394_ = lean_box(0);
v___x_1395_ = lean_array_get_borrowed(v___x_1394_, v_argNames_1359_, v_a_1348_);
lean_inc(v___x_1395_);
v___x_1396_ = lean_mk_syntax_ident(v___x_1395_);
v___x_1397_ = l_Lean_Expr_isAppOf(v_a_1389_, v_name_1390_);
lean_dec(v_name_1390_);
lean_dec(v_a_1389_);
if (v___x_1397_ == 0)
{
lean_object* v___x_1398_; 
lean_del_object(v___x_1392_);
lean_inc(v___x_1386_);
v___x_1398_ = l_Lean_Meta_isType(v___x_1386_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v_a_1399_; uint8_t v___x_1400_; 
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_a_1399_);
lean_dec_ref(v___x_1398_);
v___x_1400_ = lean_unbox(v_a_1399_);
if (v___x_1400_ == 0)
{
uint8_t v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1401_ = lean_unbox(v_a_1399_);
lean_dec(v_a_1399_);
v___x_1402_ = l_Lean_SourceInfo_fromRef(v_ref_1360_, v___x_1401_);
v___x_1403_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1404_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1);
v___x_1405_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__2));
lean_inc(v_currMacroScope_1362_);
lean_inc(v_quotContext_1361_);
v___x_1406_ = l_Lean_addMacroScope(v_quotContext_1361_, v___x_1405_, v_currMacroScope_1362_);
v___x_1407_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__6));
lean_inc(v___x_1402_);
v___x_1408_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1402_);
lean_ctor_set(v___x_1408_, 1, v___x_1404_);
lean_ctor_set(v___x_1408_, 2, v___x_1406_);
lean_ctor_set(v___x_1408_, 3, v___x_1407_);
v___x_1409_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
lean_inc(v___x_1402_);
v___x_1410_ = l_Lean_Syntax_node1(v___x_1402_, v___x_1409_, v___x_1396_);
v___x_1411_ = l_Lean_Syntax_node2(v___x_1402_, v___x_1403_, v___x_1408_, v___x_1410_);
v_a_1364_ = v___x_1411_;
goto v___jp_1363_;
}
else
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
lean_dec(v_a_1399_);
v___x_1412_ = l_Lean_SourceInfo_fromRef(v_ref_1360_, v___x_1397_);
v___x_1413_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1414_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8);
v___x_1415_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__9));
lean_inc(v_currMacroScope_1362_);
lean_inc(v_quotContext_1361_);
v___x_1416_ = l_Lean_addMacroScope(v_quotContext_1361_, v___x_1415_, v_currMacroScope_1362_);
v___x_1417_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__12));
lean_inc(v___x_1412_);
v___x_1418_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1412_);
lean_ctor_set(v___x_1418_, 1, v___x_1414_);
lean_ctor_set(v___x_1418_, 2, v___x_1416_);
lean_ctor_set(v___x_1418_, 3, v___x_1417_);
v___x_1419_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
lean_inc(v___x_1412_);
v___x_1420_ = l_Lean_Syntax_node1(v___x_1412_, v___x_1419_, v___x_1396_);
v___x_1421_ = l_Lean_Syntax_node2(v___x_1412_, v___x_1413_, v___x_1418_, v___x_1420_);
v_a_1364_ = v___x_1421_;
goto v___jp_1363_;
}
}
else
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
lean_dec(v___x_1396_);
lean_dec_ref(v___y_1354_);
lean_dec_ref(v_b_1349_);
lean_dec(v_auxFunName_1346_);
lean_dec_ref(v_indVal_1345_);
v_a_1422_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1424_ = v___x_1398_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1398_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1422_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
else
{
uint8_t v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1439_; 
v___x_1430_ = 0;
v___x_1431_ = l_Lean_SourceInfo_fromRef(v_ref_1360_, v___x_1430_);
v___x_1432_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
lean_inc(v_auxFunName_1346_);
v___x_1433_ = lean_mk_syntax_ident(v_auxFunName_1346_);
v___x_1434_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1435_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_1436_ = l_Array_append___redArg(v___x_1435_, v_levelInsts_1347_);
v___x_1437_ = lean_array_push(v___x_1436_, v___x_1396_);
lean_inc(v___x_1431_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set_tag(v___x_1392_, 1);
lean_ctor_set(v___x_1392_, 2, v___x_1437_);
lean_ctor_set(v___x_1392_, 1, v___x_1434_);
lean_ctor_set(v___x_1392_, 0, v___x_1431_);
v___x_1439_ = v___x_1392_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1431_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v___x_1434_);
lean_ctor_set(v_reuseFailAlloc_1441_, 2, v___x_1437_);
v___x_1439_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
lean_object* v___x_1440_; 
v___x_1440_ = l_Lean_Syntax_node2(v___x_1431_, v___x_1432_, v___x_1433_, v___x_1439_);
v_a_1364_ = v___x_1440_;
goto v___jp_1363_;
}
}
}
}
else
{
lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1452_; 
lean_dec_ref(v___y_1354_);
lean_dec_ref(v_b_1349_);
lean_dec(v_auxFunName_1346_);
lean_dec_ref(v_indVal_1345_);
v_a_1445_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1447_ = v___x_1387_;
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v___x_1387_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1450_; 
if (v_isShared_1448_ == 0)
{
v___x_1450_ = v___x_1447_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_a_1445_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
v___jp_1363_:
{
lean_object* v_fst_1365_; lean_object* v_snd_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1384_; 
v_fst_1365_ = lean_ctor_get(v_b_1349_, 0);
v_snd_1366_ = lean_ctor_get(v_b_1349_, 1);
v_isSharedCheck_1384_ = !lean_is_exclusive(v_b_1349_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1368_ = v_b_1349_;
v_isShared_1369_ = v_isSharedCheck_1384_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_snd_1366_);
lean_inc(v_fst_1365_);
lean_dec(v_b_1349_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1384_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
uint8_t v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1370_ = 0;
v___x_1371_ = l_Lean_SourceInfo_fromRef(v_ref_1360_, v___x_1370_);
v___x_1372_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__2));
lean_inc(v___x_1371_);
v___x_1373_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1371_);
lean_ctor_set(v___x_1373_, 1, v___x_1372_);
v___x_1374_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg___closed__1));
v___x_1375_ = l_Lean_Syntax_node1(v___x_1371_, v___x_1374_, v___x_1373_);
v___x_1376_ = lean_array_push(v_fst_1365_, v___x_1375_);
v___x_1377_ = lean_array_push(v_snd_1366_, v_a_1364_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 1, v___x_1377_);
lean_ctor_set(v___x_1368_, 0, v___x_1376_);
v___x_1379_ = v___x_1368_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1376_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v___x_1377_);
v___x_1379_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1380_ = lean_unsigned_to_nat(1u);
v___x_1381_ = lean_nat_add(v_a_1348_, v___x_1380_);
v___x_1382_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6___redArg(v_upperBound_1342_, v_header_1343_, v_xs_1344_, v_indVal_1345_, v_auxFunName_1346_, v_levelInsts_1347_, v___x_1381_, v___x_1379_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
return v___x_1382_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4___redArg___boxed(lean_object* v_upperBound_1453_, lean_object* v_header_1454_, lean_object* v_xs_1455_, lean_object* v_indVal_1456_, lean_object* v_auxFunName_1457_, lean_object* v_levelInsts_1458_, lean_object* v_a_1459_, lean_object* v_b_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4___redArg(v_upperBound_1453_, v_header_1454_, v_xs_1455_, v_indVal_1456_, v_auxFunName_1457_, v_levelInsts_1458_, v_a_1459_, v_b_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
lean_dec(v___y_1466_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v_a_1459_);
lean_dec_ref(v_levelInsts_1458_);
lean_dec_ref(v_xs_1455_);
lean_dec_ref(v_header_1454_);
lean_dec(v_upperBound_1453_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg(lean_object* v_upperBound_1472_, lean_object* v___x_1473_, lean_object* v_xs_1474_, lean_object* v_indVal_1475_, lean_object* v_auxFunName_1476_, lean_object* v_levelInsts_1477_, lean_object* v_a_1478_, lean_object* v_b_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
uint8_t v___x_1485_; 
v___x_1485_ = lean_nat_dec_lt(v_a_1478_, v_upperBound_1472_);
if (v___x_1485_ == 0)
{
lean_object* v___x_1486_; 
lean_dec_ref(v___y_1482_);
lean_dec(v_a_1478_);
lean_dec(v_auxFunName_1476_);
lean_dec_ref(v_indVal_1475_);
v___x_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1486_, 0, v_b_1479_);
return v___x_1486_;
}
else
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1487_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg___closed__1));
v___x_1488_ = l_Lean_Core_mkFreshUserName(v___x_1487_, v___y_1482_, v___y_1483_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v_a_1489_; lean_object* v_fst_1490_; lean_object* v_snd_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1579_; 
v_a_1489_ = lean_ctor_get(v___x_1488_, 0);
lean_inc(v_a_1489_);
lean_dec_ref(v___x_1488_);
v_fst_1490_ = lean_ctor_get(v_b_1479_, 0);
v_snd_1491_ = lean_ctor_get(v_b_1479_, 1);
v_isSharedCheck_1579_ = !lean_is_exclusive(v_b_1479_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1493_ = v_b_1479_;
v_isShared_1494_ = v_isSharedCheck_1579_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_snd_1491_);
lean_inc(v_fst_1490_);
lean_dec(v_b_1479_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1579_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1495_ = l_Lean_instInhabitedExpr;
v___x_1496_ = lean_nat_add(v___x_1473_, v_a_1478_);
v___x_1497_ = lean_array_get_borrowed(v___x_1495_, v_xs_1474_, v___x_1496_);
lean_dec(v___x_1496_);
lean_inc(v___y_1483_);
lean_inc_ref(v___y_1482_);
lean_inc(v___y_1481_);
lean_inc_ref(v___y_1480_);
lean_inc(v___x_1497_);
v___x_1498_ = lean_infer_type(v___x_1497_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v_toConstantVal_1499_; lean_object* v_a_1500_; lean_object* v_name_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1568_; 
v_toConstantVal_1499_ = lean_ctor_get(v_indVal_1475_, 0);
lean_inc_ref(v_toConstantVal_1499_);
v_a_1500_ = lean_ctor_get(v___x_1498_, 0);
lean_inc(v_a_1500_);
lean_dec_ref(v___x_1498_);
v_name_1501_ = lean_ctor_get(v_toConstantVal_1499_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v_toConstantVal_1499_);
if (v_isSharedCheck_1568_ == 0)
{
lean_object* v_unused_1569_; lean_object* v_unused_1570_; 
v_unused_1569_ = lean_ctor_get(v_toConstantVal_1499_, 2);
lean_dec(v_unused_1569_);
v_unused_1570_ = lean_ctor_get(v_toConstantVal_1499_, 1);
lean_dec(v_unused_1570_);
v___x_1503_ = v_toConstantVal_1499_;
v_isShared_1504_ = v_isSharedCheck_1568_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_name_1501_);
lean_dec(v_toConstantVal_1499_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1568_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v_a_1508_; uint8_t v___x_1516_; 
v___x_1505_ = lean_mk_syntax_ident(v_a_1489_);
lean_inc(v___x_1505_);
v___x_1506_ = lean_array_push(v_fst_1490_, v___x_1505_);
v___x_1516_ = l_Lean_Expr_isAppOf(v_a_1500_, v_name_1501_);
lean_dec(v_name_1501_);
lean_dec(v_a_1500_);
if (v___x_1516_ == 0)
{
lean_object* v___x_1517_; 
lean_del_object(v___x_1503_);
lean_inc(v___x_1497_);
v___x_1517_ = l_Lean_Meta_isType(v___x_1497_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; uint8_t v___x_1519_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1518_);
lean_dec_ref(v___x_1517_);
v___x_1519_ = lean_unbox(v_a_1518_);
if (v___x_1519_ == 0)
{
lean_object* v_ref_1520_; lean_object* v_quotContext_1521_; lean_object* v_currMacroScope_1522_; uint8_t v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v_ref_1520_ = lean_ctor_get(v___y_1482_, 5);
v_quotContext_1521_ = lean_ctor_get(v___y_1482_, 10);
v_currMacroScope_1522_ = lean_ctor_get(v___y_1482_, 11);
v___x_1523_ = lean_unbox(v_a_1518_);
lean_dec(v_a_1518_);
v___x_1524_ = l_Lean_SourceInfo_fromRef(v_ref_1520_, v___x_1523_);
v___x_1525_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1526_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1);
v___x_1527_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__2));
lean_inc(v_currMacroScope_1522_);
lean_inc(v_quotContext_1521_);
v___x_1528_ = l_Lean_addMacroScope(v_quotContext_1521_, v___x_1527_, v_currMacroScope_1522_);
v___x_1529_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__6));
lean_inc(v___x_1524_);
v___x_1530_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1524_);
lean_ctor_set(v___x_1530_, 1, v___x_1526_);
lean_ctor_set(v___x_1530_, 2, v___x_1528_);
lean_ctor_set(v___x_1530_, 3, v___x_1529_);
v___x_1531_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
lean_inc(v___x_1524_);
v___x_1532_ = l_Lean_Syntax_node1(v___x_1524_, v___x_1531_, v___x_1505_);
v___x_1533_ = l_Lean_Syntax_node2(v___x_1524_, v___x_1525_, v___x_1530_, v___x_1532_);
v_a_1508_ = v___x_1533_;
goto v___jp_1507_;
}
else
{
lean_object* v_ref_1534_; lean_object* v_quotContext_1535_; lean_object* v_currMacroScope_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
lean_dec(v_a_1518_);
v_ref_1534_ = lean_ctor_get(v___y_1482_, 5);
v_quotContext_1535_ = lean_ctor_get(v___y_1482_, 10);
v_currMacroScope_1536_ = lean_ctor_get(v___y_1482_, 11);
v___x_1537_ = l_Lean_SourceInfo_fromRef(v_ref_1534_, v___x_1516_);
v___x_1538_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1539_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8);
v___x_1540_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__9));
lean_inc(v_currMacroScope_1536_);
lean_inc(v_quotContext_1535_);
v___x_1541_ = l_Lean_addMacroScope(v_quotContext_1535_, v___x_1540_, v_currMacroScope_1536_);
v___x_1542_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__12));
lean_inc(v___x_1537_);
v___x_1543_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1537_);
lean_ctor_set(v___x_1543_, 1, v___x_1539_);
lean_ctor_set(v___x_1543_, 2, v___x_1541_);
lean_ctor_set(v___x_1543_, 3, v___x_1542_);
v___x_1544_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
lean_inc(v___x_1537_);
v___x_1545_ = l_Lean_Syntax_node1(v___x_1537_, v___x_1544_, v___x_1505_);
v___x_1546_ = l_Lean_Syntax_node2(v___x_1537_, v___x_1538_, v___x_1543_, v___x_1545_);
v_a_1508_ = v___x_1546_;
goto v___jp_1507_;
}
}
else
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1554_; 
lean_dec_ref(v___x_1506_);
lean_dec(v___x_1505_);
lean_del_object(v___x_1493_);
lean_dec(v_snd_1491_);
lean_dec_ref(v___y_1482_);
lean_dec(v_a_1478_);
lean_dec(v_auxFunName_1476_);
lean_dec_ref(v_indVal_1475_);
v_a_1547_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1549_ = v___x_1517_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1517_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
if (v_isShared_1550_ == 0)
{
v___x_1552_ = v___x_1549_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_a_1547_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
else
{
lean_object* v_ref_1555_; uint8_t v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1565_; 
v_ref_1555_ = lean_ctor_get(v___y_1482_, 5);
v___x_1556_ = 0;
v___x_1557_ = l_Lean_SourceInfo_fromRef(v_ref_1555_, v___x_1556_);
v___x_1558_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
lean_inc(v_auxFunName_1476_);
v___x_1559_ = lean_mk_syntax_ident(v_auxFunName_1476_);
v___x_1560_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1561_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_1562_ = l_Array_append___redArg(v___x_1561_, v_levelInsts_1477_);
v___x_1563_ = lean_array_push(v___x_1562_, v___x_1505_);
lean_inc(v___x_1557_);
if (v_isShared_1504_ == 0)
{
lean_ctor_set_tag(v___x_1503_, 1);
lean_ctor_set(v___x_1503_, 2, v___x_1563_);
lean_ctor_set(v___x_1503_, 1, v___x_1560_);
lean_ctor_set(v___x_1503_, 0, v___x_1557_);
v___x_1565_ = v___x_1503_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1557_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v___x_1560_);
lean_ctor_set(v_reuseFailAlloc_1567_, 2, v___x_1563_);
v___x_1565_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
lean_object* v___x_1566_; 
v___x_1566_ = l_Lean_Syntax_node2(v___x_1557_, v___x_1558_, v___x_1559_, v___x_1565_);
v_a_1508_ = v___x_1566_;
goto v___jp_1507_;
}
}
v___jp_1507_:
{
lean_object* v___x_1509_; lean_object* v___x_1511_; 
v___x_1509_ = lean_array_push(v_snd_1491_, v_a_1508_);
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 1, v___x_1509_);
lean_ctor_set(v___x_1493_, 0, v___x_1506_);
v___x_1511_ = v___x_1493_;
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
v___x_1513_ = lean_nat_add(v_a_1478_, v___x_1512_);
lean_dec(v_a_1478_);
v_a_1478_ = v___x_1513_;
v_b_1479_ = v___x_1511_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
lean_del_object(v___x_1493_);
lean_dec(v_snd_1491_);
lean_dec(v_fst_1490_);
lean_dec(v_a_1489_);
lean_dec_ref(v___y_1482_);
lean_dec(v_a_1478_);
lean_dec(v_auxFunName_1476_);
lean_dec_ref(v_indVal_1475_);
v_a_1571_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1573_ = v___x_1498_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1498_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1574_ == 0)
{
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1571_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
}
else
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
lean_dec_ref(v___y_1482_);
lean_dec_ref(v_b_1479_);
lean_dec(v_a_1478_);
lean_dec(v_auxFunName_1476_);
lean_dec_ref(v_indVal_1475_);
v_a_1580_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1488_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1488_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1580_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg___boxed(lean_object* v_upperBound_1588_, lean_object* v___x_1589_, lean_object* v_xs_1590_, lean_object* v_indVal_1591_, lean_object* v_auxFunName_1592_, lean_object* v_levelInsts_1593_, lean_object* v_a_1594_, lean_object* v_b_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg(v_upperBound_1588_, v___x_1589_, v_xs_1590_, v_indVal_1591_, v_auxFunName_1592_, v_levelInsts_1593_, v_a_1594_, v_b_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
lean_dec(v___y_1599_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
lean_dec_ref(v_levelInsts_1593_);
lean_dec_ref(v_xs_1590_);
lean_dec(v___x_1589_);
lean_dec(v_upperBound_1588_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3___redArg(lean_object* v_upperBound_1602_, lean_object* v___x_1603_, lean_object* v_xs_1604_, lean_object* v_indVal_1605_, lean_object* v_auxFunName_1606_, lean_object* v_levelInsts_1607_, lean_object* v_a_1608_, lean_object* v_b_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
uint8_t v___x_1617_; 
v___x_1617_ = lean_nat_dec_lt(v_a_1608_, v_upperBound_1602_);
if (v___x_1617_ == 0)
{
lean_object* v___x_1618_; 
lean_dec_ref(v___y_1614_);
lean_dec(v_auxFunName_1606_);
lean_dec_ref(v_indVal_1605_);
v___x_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1618_, 0, v_b_1609_);
return v___x_1618_;
}
else
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg___closed__1));
v___x_1620_ = l_Lean_Core_mkFreshUserName(v___x_1619_, v___y_1614_, v___y_1615_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; lean_object* v_fst_1622_; lean_object* v_snd_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1711_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_a_1621_);
lean_dec_ref(v___x_1620_);
v_fst_1622_ = lean_ctor_get(v_b_1609_, 0);
v_snd_1623_ = lean_ctor_get(v_b_1609_, 1);
v_isSharedCheck_1711_ = !lean_is_exclusive(v_b_1609_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1625_ = v_b_1609_;
v_isShared_1626_ = v_isSharedCheck_1711_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_snd_1623_);
lean_inc(v_fst_1622_);
lean_dec(v_b_1609_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1711_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1627_ = l_Lean_instInhabitedExpr;
v___x_1628_ = lean_nat_add(v___x_1603_, v_a_1608_);
v___x_1629_ = lean_array_get_borrowed(v___x_1627_, v_xs_1604_, v___x_1628_);
lean_dec(v___x_1628_);
lean_inc(v___y_1615_);
lean_inc_ref(v___y_1614_);
lean_inc(v___y_1613_);
lean_inc_ref(v___y_1612_);
lean_inc(v___x_1629_);
v___x_1630_ = lean_infer_type(v___x_1629_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_toConstantVal_1631_; lean_object* v_a_1632_; lean_object* v_name_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1700_; 
v_toConstantVal_1631_ = lean_ctor_get(v_indVal_1605_, 0);
lean_inc_ref(v_toConstantVal_1631_);
v_a_1632_ = lean_ctor_get(v___x_1630_, 0);
lean_inc(v_a_1632_);
lean_dec_ref(v___x_1630_);
v_name_1633_ = lean_ctor_get(v_toConstantVal_1631_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v_toConstantVal_1631_);
if (v_isSharedCheck_1700_ == 0)
{
lean_object* v_unused_1701_; lean_object* v_unused_1702_; 
v_unused_1701_ = lean_ctor_get(v_toConstantVal_1631_, 2);
lean_dec(v_unused_1701_);
v_unused_1702_ = lean_ctor_get(v_toConstantVal_1631_, 1);
lean_dec(v_unused_1702_);
v___x_1635_ = v_toConstantVal_1631_;
v_isShared_1636_ = v_isSharedCheck_1700_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_name_1633_);
lean_dec(v_toConstantVal_1631_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1700_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v_a_1640_; uint8_t v___x_1648_; 
v___x_1637_ = lean_mk_syntax_ident(v_a_1621_);
lean_inc(v___x_1637_);
v___x_1638_ = lean_array_push(v_fst_1622_, v___x_1637_);
v___x_1648_ = l_Lean_Expr_isAppOf(v_a_1632_, v_name_1633_);
lean_dec(v_name_1633_);
lean_dec(v_a_1632_);
if (v___x_1648_ == 0)
{
lean_object* v___x_1649_; 
lean_del_object(v___x_1635_);
lean_inc(v___x_1629_);
v___x_1649_ = l_Lean_Meta_isType(v___x_1629_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v_a_1650_; uint8_t v___x_1651_; 
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_a_1650_);
lean_dec_ref(v___x_1649_);
v___x_1651_ = lean_unbox(v_a_1650_);
if (v___x_1651_ == 0)
{
lean_object* v_ref_1652_; lean_object* v_quotContext_1653_; lean_object* v_currMacroScope_1654_; uint8_t v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v_ref_1652_ = lean_ctor_get(v___y_1614_, 5);
v_quotContext_1653_ = lean_ctor_get(v___y_1614_, 10);
v_currMacroScope_1654_ = lean_ctor_get(v___y_1614_, 11);
v___x_1655_ = lean_unbox(v_a_1650_);
lean_dec(v_a_1650_);
v___x_1656_ = l_Lean_SourceInfo_fromRef(v_ref_1652_, v___x_1655_);
v___x_1657_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1658_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1);
v___x_1659_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__2));
lean_inc(v_currMacroScope_1654_);
lean_inc(v_quotContext_1653_);
v___x_1660_ = l_Lean_addMacroScope(v_quotContext_1653_, v___x_1659_, v_currMacroScope_1654_);
v___x_1661_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__6));
lean_inc(v___x_1656_);
v___x_1662_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1656_);
lean_ctor_set(v___x_1662_, 1, v___x_1658_);
lean_ctor_set(v___x_1662_, 2, v___x_1660_);
lean_ctor_set(v___x_1662_, 3, v___x_1661_);
v___x_1663_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
lean_inc(v___x_1656_);
v___x_1664_ = l_Lean_Syntax_node1(v___x_1656_, v___x_1663_, v___x_1637_);
v___x_1665_ = l_Lean_Syntax_node2(v___x_1656_, v___x_1657_, v___x_1662_, v___x_1664_);
v_a_1640_ = v___x_1665_;
goto v___jp_1639_;
}
else
{
lean_object* v_ref_1666_; lean_object* v_quotContext_1667_; lean_object* v_currMacroScope_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
lean_dec(v_a_1650_);
v_ref_1666_ = lean_ctor_get(v___y_1614_, 5);
v_quotContext_1667_ = lean_ctor_get(v___y_1614_, 10);
v_currMacroScope_1668_ = lean_ctor_get(v___y_1614_, 11);
v___x_1669_ = l_Lean_SourceInfo_fromRef(v_ref_1666_, v___x_1648_);
v___x_1670_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1671_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8);
v___x_1672_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__9));
lean_inc(v_currMacroScope_1668_);
lean_inc(v_quotContext_1667_);
v___x_1673_ = l_Lean_addMacroScope(v_quotContext_1667_, v___x_1672_, v_currMacroScope_1668_);
v___x_1674_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__12));
lean_inc(v___x_1669_);
v___x_1675_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1669_);
lean_ctor_set(v___x_1675_, 1, v___x_1671_);
lean_ctor_set(v___x_1675_, 2, v___x_1673_);
lean_ctor_set(v___x_1675_, 3, v___x_1674_);
v___x_1676_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
lean_inc(v___x_1669_);
v___x_1677_ = l_Lean_Syntax_node1(v___x_1669_, v___x_1676_, v___x_1637_);
v___x_1678_ = l_Lean_Syntax_node2(v___x_1669_, v___x_1670_, v___x_1675_, v___x_1677_);
v_a_1640_ = v___x_1678_;
goto v___jp_1639_;
}
}
else
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
lean_dec_ref(v___x_1638_);
lean_dec(v___x_1637_);
lean_del_object(v___x_1625_);
lean_dec(v_snd_1623_);
lean_dec_ref(v___y_1614_);
lean_dec(v_auxFunName_1606_);
lean_dec_ref(v_indVal_1605_);
v_a_1679_ = lean_ctor_get(v___x_1649_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1649_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1649_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1679_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
}
else
{
lean_object* v_ref_1687_; uint8_t v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1697_; 
v_ref_1687_ = lean_ctor_get(v___y_1614_, 5);
v___x_1688_ = 0;
v___x_1689_ = l_Lean_SourceInfo_fromRef(v_ref_1687_, v___x_1688_);
v___x_1690_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
lean_inc(v_auxFunName_1606_);
v___x_1691_ = lean_mk_syntax_ident(v_auxFunName_1606_);
v___x_1692_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1693_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_1694_ = l_Array_append___redArg(v___x_1693_, v_levelInsts_1607_);
v___x_1695_ = lean_array_push(v___x_1694_, v___x_1637_);
lean_inc(v___x_1689_);
if (v_isShared_1636_ == 0)
{
lean_ctor_set_tag(v___x_1635_, 1);
lean_ctor_set(v___x_1635_, 2, v___x_1695_);
lean_ctor_set(v___x_1635_, 1, v___x_1692_);
lean_ctor_set(v___x_1635_, 0, v___x_1689_);
v___x_1697_ = v___x_1635_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v___x_1689_);
lean_ctor_set(v_reuseFailAlloc_1699_, 1, v___x_1692_);
lean_ctor_set(v_reuseFailAlloc_1699_, 2, v___x_1695_);
v___x_1697_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Lean_Syntax_node2(v___x_1689_, v___x_1690_, v___x_1691_, v___x_1697_);
v_a_1640_ = v___x_1698_;
goto v___jp_1639_;
}
}
v___jp_1639_:
{
lean_object* v___x_1641_; lean_object* v___x_1643_; 
v___x_1641_ = lean_array_push(v_snd_1623_, v_a_1640_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 1, v___x_1641_);
lean_ctor_set(v___x_1625_, 0, v___x_1638_);
v___x_1643_ = v___x_1625_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1638_);
lean_ctor_set(v_reuseFailAlloc_1647_, 1, v___x_1641_);
v___x_1643_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1644_ = lean_unsigned_to_nat(1u);
v___x_1645_ = lean_nat_add(v_a_1608_, v___x_1644_);
v___x_1646_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg(v_upperBound_1602_, v___x_1603_, v_xs_1604_, v_indVal_1605_, v_auxFunName_1606_, v_levelInsts_1607_, v___x_1645_, v___x_1643_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
return v___x_1646_;
}
}
}
}
else
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
lean_del_object(v___x_1625_);
lean_dec(v_snd_1623_);
lean_dec(v_fst_1622_);
lean_dec(v_a_1621_);
lean_dec_ref(v___y_1614_);
lean_dec(v_auxFunName_1606_);
lean_dec_ref(v_indVal_1605_);
v_a_1703_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1705_ = v___x_1630_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1630_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1703_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
}
else
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1719_; 
lean_dec_ref(v___y_1614_);
lean_dec_ref(v_b_1609_);
lean_dec(v_auxFunName_1606_);
lean_dec_ref(v_indVal_1605_);
v_a_1712_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1714_ = v___x_1620_;
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1620_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1712_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3___redArg___boxed(lean_object* v_upperBound_1720_, lean_object* v___x_1721_, lean_object* v_xs_1722_, lean_object* v_indVal_1723_, lean_object* v_auxFunName_1724_, lean_object* v_levelInsts_1725_, lean_object* v_a_1726_, lean_object* v_b_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3___redArg(v_upperBound_1720_, v___x_1721_, v_xs_1722_, v_indVal_1723_, v_auxFunName_1724_, v_levelInsts_1725_, v_a_1726_, v_b_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
lean_dec(v___y_1733_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec(v_a_1726_);
lean_dec_ref(v_levelInsts_1725_);
lean_dec_ref(v_xs_1722_);
lean_dec(v___x_1721_);
lean_dec(v_upperBound_1720_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__2(size_t v_sz_1736_, size_t v_i_1737_, lean_object* v_bs_1738_){
_start:
{
uint8_t v___x_1739_; 
v___x_1739_ = lean_usize_dec_lt(v_i_1737_, v_sz_1736_);
if (v___x_1739_ == 0)
{
return v_bs_1738_;
}
else
{
lean_object* v_v_1740_; lean_object* v___x_1741_; lean_object* v_bs_x27_1742_; size_t v___x_1743_; size_t v___x_1744_; lean_object* v___x_1745_; 
v_v_1740_ = lean_array_uget(v_bs_1738_, v_i_1737_);
v___x_1741_ = lean_unsigned_to_nat(0u);
v_bs_x27_1742_ = lean_array_uset(v_bs_1738_, v_i_1737_, v___x_1741_);
v___x_1743_ = ((size_t)1ULL);
v___x_1744_ = lean_usize_add(v_i_1737_, v___x_1743_);
v___x_1745_ = lean_array_uset(v_bs_x27_1742_, v_i_1737_, v_v_1740_);
v_i_1737_ = v___x_1744_;
v_bs_1738_ = v___x_1745_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__2___boxed(lean_object* v_sz_1747_, lean_object* v_i_1748_, lean_object* v_bs_1749_){
_start:
{
size_t v_sz_boxed_1750_; size_t v_i_boxed_1751_; lean_object* v_res_1752_; 
v_sz_boxed_1750_ = lean_unbox_usize(v_sz_1747_);
lean_dec(v_sz_1747_);
v_i_boxed_1751_ = lean_unbox_usize(v_i_1748_);
lean_dec(v_i_1748_);
v_res_1752_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__2(v_sz_boxed_1750_, v_i_boxed_1751_, v_bs_1749_);
return v_res_1752_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1760_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__9));
v___x_1761_ = l_Lean_mkAtom(v___x_1760_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1(lean_object* v_indVal_1763_, lean_object* v___x_1764_, lean_object* v___x_1765_, lean_object* v_numParams_1766_, lean_object* v_header_1767_, lean_object* v_auxFunName_1768_, lean_object* v_levelInsts_1769_, lean_object* v_numFields_1770_, lean_object* v___f_1771_, lean_object* v_head_1772_, lean_object* v_a_1773_, lean_object* v_name_1774_, lean_object* v_xs_1775_, lean_object* v_x_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
lean_object* v_numIndices_1784_; lean_object* v___x_1785_; 
v_numIndices_1784_ = lean_ctor_get(v_indVal_1763_, 2);
lean_inc_ref(v___x_1765_);
lean_inc(v___x_1764_);
v___x_1785_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg(v_numIndices_1784_, v___x_1764_, v___x_1765_, v___y_1781_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v_a_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
lean_inc(v_a_1786_);
lean_dec_ref(v___x_1785_);
lean_inc_ref(v___x_1765_);
v___x_1787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1765_);
lean_ctor_set(v___x_1787_, 1, v___x_1765_);
lean_inc_ref(v___y_1781_);
lean_inc(v_auxFunName_1768_);
lean_inc_ref(v_indVal_1763_);
v___x_1788_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4___redArg(v_numParams_1766_, v_header_1767_, v_xs_1775_, v_indVal_1763_, v_auxFunName_1768_, v_levelInsts_1769_, v___x_1764_, v___x_1787_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; lean_object* v_fst_1790_; lean_object* v_snd_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1910_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_a_1789_);
lean_dec_ref(v___x_1788_);
v_fst_1790_ = lean_ctor_get(v_a_1789_, 0);
v_snd_1791_ = lean_ctor_get(v_a_1789_, 1);
v_isSharedCheck_1910_ = !lean_is_exclusive(v_a_1789_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1793_ = v_a_1789_;
v_isShared_1794_ = v_isSharedCheck_1910_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_snd_1791_);
lean_inc(v_fst_1790_);
lean_dec(v_a_1789_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1910_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1794_ == 0)
{
v___x_1796_ = v___x_1793_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_fst_1790_);
lean_ctor_set(v_reuseFailAlloc_1909_, 1, v_snd_1791_);
v___x_1796_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
lean_object* v___x_1797_; 
lean_inc_ref(v___y_1781_);
v___x_1797_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3___redArg(v_numFields_1770_, v_numParams_1766_, v_xs_1775_, v_indVal_1763_, v_auxFunName_1768_, v_levelInsts_1769_, v___x_1764_, v___x_1796_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_);
lean_dec(v___x_1764_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; lean_object* v_ref_1799_; lean_object* v_quotContext_1800_; lean_object* v_currMacroScope_1801_; lean_object* v___x_1802_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
lean_inc(v_a_1798_);
lean_dec_ref(v___x_1797_);
v_ref_1799_ = lean_ctor_get(v___y_1781_, 5);
v_quotContext_1800_ = lean_ctor_get(v___y_1781_, 10);
v_currMacroScope_1801_ = lean_ctor_get(v___y_1781_, 11);
lean_inc_ref(v___f_1771_);
lean_inc(v___y_1782_);
lean_inc_ref(v___y_1781_);
lean_inc(v___y_1780_);
lean_inc_ref(v___y_1779_);
lean_inc(v___y_1778_);
lean_inc_ref(v___y_1777_);
v___x_1802_ = lean_apply_7(v___f_1771_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, lean_box(0));
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_a_1803_; lean_object* v_fst_1804_; lean_object* v_snd_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1892_; 
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
lean_inc(v_a_1803_);
lean_dec_ref(v___x_1802_);
v_fst_1804_ = lean_ctor_get(v_a_1798_, 0);
v_snd_1805_ = lean_ctor_get(v_a_1798_, 1);
v_isSharedCheck_1892_ = !lean_is_exclusive(v_a_1798_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1807_ = v_a_1798_;
v_isShared_1808_ = v_isSharedCheck_1892_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_snd_1805_);
lean_inc(v_fst_1804_);
lean_dec(v_a_1798_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1892_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
uint8_t v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1814_; 
v___x_1809_ = 0;
v___x_1810_ = l_Lean_SourceInfo_fromRef(v_ref_1799_, v___x_1809_);
v___x_1811_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_1812_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__4));
lean_inc(v___x_1810_);
if (v_isShared_1808_ == 0)
{
lean_ctor_set_tag(v___x_1807_, 2);
lean_ctor_set(v___x_1807_, 1, v___x_1812_);
lean_ctor_set(v___x_1807_, 0, v___x_1810_);
v___x_1814_ = v___x_1807_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1810_);
lean_ctor_set(v_reuseFailAlloc_1891_, 1, v___x_1812_);
v___x_1814_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___y_1831_; lean_object* v___x_1877_; 
v___x_1815_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__3));
v___x_1816_ = lean_mk_syntax_ident(v_head_1772_);
lean_inc(v___x_1810_);
v___x_1817_ = l_Lean_Syntax_node2(v___x_1810_, v___x_1815_, v___x_1814_, v___x_1816_);
v___x_1818_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__4));
v___x_1819_ = lean_box(0);
v___x_1820_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_1821_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_1822_ = l_Array_append___redArg(v___x_1821_, v_fst_1804_);
lean_dec(v_fst_1804_);
lean_inc(v___x_1810_);
v___x_1823_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1810_);
lean_ctor_set(v___x_1823_, 1, v___x_1820_);
lean_ctor_set(v___x_1823_, 2, v___x_1822_);
v___x_1824_ = l_Lean_Syntax_node2(v___x_1810_, v___x_1811_, v___x_1817_, v___x_1823_);
v___x_1825_ = lean_array_push(v_a_1786_, v___x_1824_);
v___x_1826_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__2, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__2_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__2);
lean_inc(v_currMacroScope_1801_);
lean_inc(v_quotContext_1800_);
v___x_1827_ = l_Lean_addMacroScope(v_quotContext_1800_, v___x_1818_, v_currMacroScope_1801_);
v___x_1828_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__10));
lean_inc(v_a_1803_);
v___x_1829_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1829_, 0, v_a_1803_);
lean_ctor_set(v___x_1829_, 1, v___x_1826_);
lean_ctor_set(v___x_1829_, 2, v___x_1827_);
lean_ctor_set(v___x_1829_, 3, v___x_1828_);
lean_inc(v_name_1774_);
v___x_1877_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_1819_, v_name_1774_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v___x_1878_; 
v___x_1878_ = l_Lean_quoteNameMk(v_name_1774_);
v___y_1831_ = v___x_1878_;
goto v___jp_1830_;
}
else
{
lean_object* v_val_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
lean_dec(v_name_1774_);
v_val_1879_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_val_1879_);
lean_dec_ref(v___x_1877_);
v___x_1880_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__16));
v___x_1881_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__17));
v___x_1882_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__18));
v___x_1883_ = lean_string_intercalate(v___x_1882_, v_val_1879_);
v___x_1884_ = lean_string_append(v___x_1881_, v___x_1883_);
lean_dec_ref(v___x_1883_);
v___x_1885_ = lean_box(2);
v___x_1886_ = l_Lean_Syntax_mkNameLit(v___x_1884_, v___x_1885_);
v___x_1887_ = lean_unsigned_to_nat(1u);
v___x_1888_ = lean_mk_empty_array_with_capacity(v___x_1887_);
v___x_1889_ = lean_array_push(v___x_1888_, v___x_1886_);
v___x_1890_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1885_);
lean_ctor_set(v___x_1890_, 1, v___x_1880_);
lean_ctor_set(v___x_1890_, 2, v___x_1889_);
v___y_1831_ = v___x_1890_;
goto v___jp_1830_;
}
v___jp_1830_:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1832_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__12));
v___x_1833_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__13));
lean_inc(v_a_1803_);
v___x_1834_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1834_, 0, v_a_1803_);
lean_ctor_set(v___x_1834_, 1, v___x_1833_);
v___x_1835_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__9));
v___x_1836_ = l_Lean_Syntax_SepArray_ofElems(v___x_1835_, v_a_1773_);
v___x_1837_ = l_Array_append___redArg(v___x_1821_, v___x_1836_);
lean_dec_ref(v___x_1836_);
lean_inc(v_a_1803_);
v___x_1838_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1838_, 0, v_a_1803_);
lean_ctor_set(v___x_1838_, 1, v___x_1820_);
lean_ctor_set(v___x_1838_, 2, v___x_1837_);
v___x_1839_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__14));
lean_inc(v_a_1803_);
v___x_1840_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1840_, 0, v_a_1803_);
lean_ctor_set(v___x_1840_, 1, v___x_1839_);
lean_inc(v_a_1803_);
v___x_1841_ = l_Lean_Syntax_node3(v_a_1803_, v___x_1832_, v___x_1834_, v___x_1838_, v___x_1840_);
lean_inc(v_a_1803_);
v___x_1842_ = l_Lean_Syntax_node2(v_a_1803_, v___x_1820_, v___y_1831_, v___x_1841_);
v___x_1843_ = l_Lean_Syntax_node2(v_a_1803_, v___x_1811_, v___x_1829_, v___x_1842_);
v___x_1844_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm(v___x_1843_, v_snd_1805_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_);
lean_dec(v_snd_1805_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v_a_1845_; lean_object* v___x_1846_; 
v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
lean_inc(v_a_1845_);
lean_dec_ref(v___x_1844_);
lean_inc(v___y_1782_);
lean_inc(v___y_1780_);
lean_inc_ref(v___y_1779_);
lean_inc(v___y_1778_);
lean_inc_ref(v___y_1777_);
v___x_1846_ = lean_apply_7(v___f_1771_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, lean_box(0));
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1868_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1849_ = v___x_1846_;
v_isShared_1850_ = v_isSharedCheck_1868_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1846_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1868_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; size_t v_sz_1854_; size_t v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1866_; 
v___x_1851_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__1));
v___x_1852_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__2));
lean_inc(v_a_1847_);
v___x_1853_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1853_, 0, v_a_1847_);
lean_ctor_set(v___x_1853_, 1, v___x_1852_);
v_sz_1854_ = lean_array_size(v___x_1825_);
v___x_1855_ = ((size_t)0ULL);
v___x_1856_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__2(v_sz_1854_, v___x_1855_, v___x_1825_);
v___x_1857_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__3);
v___x_1858_ = l_Lean_mkSepArray(v___x_1856_, v___x_1857_);
lean_dec_ref(v___x_1856_);
v___x_1859_ = l_Array_append___redArg(v___x_1821_, v___x_1858_);
lean_dec_ref(v___x_1858_);
lean_inc(v_a_1847_);
v___x_1860_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1860_, 0, v_a_1847_);
lean_ctor_set(v___x_1860_, 1, v___x_1820_);
lean_ctor_set(v___x_1860_, 2, v___x_1859_);
lean_inc(v_a_1847_);
v___x_1861_ = l_Lean_Syntax_node1(v_a_1847_, v___x_1820_, v___x_1860_);
v___x_1862_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__4));
lean_inc(v_a_1847_);
v___x_1863_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1863_, 0, v_a_1847_);
lean_ctor_set(v___x_1863_, 1, v___x_1862_);
v___x_1864_ = l_Lean_Syntax_node4(v_a_1847_, v___x_1851_, v___x_1853_, v___x_1861_, v___x_1863_, v_a_1845_);
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 0, v___x_1864_);
v___x_1866_ = v___x_1849_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v___x_1864_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
lean_dec(v_a_1845_);
lean_dec_ref(v___x_1825_);
v_a_1869_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1871_ = v___x_1846_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1846_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1869_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
else
{
lean_dec_ref(v___x_1825_);
lean_dec_ref(v___y_1781_);
lean_dec_ref(v___f_1771_);
return v___x_1844_;
}
}
}
}
}
else
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
lean_dec(v_a_1798_);
lean_dec(v_a_1786_);
lean_dec_ref(v___y_1781_);
lean_dec(v_name_1774_);
lean_dec(v_head_1772_);
lean_dec_ref(v___f_1771_);
v_a_1893_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1895_ = v___x_1802_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1802_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1896_ == 0)
{
v___x_1898_ = v___x_1895_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_a_1893_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
else
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1908_; 
lean_dec(v_a_1786_);
lean_dec_ref(v___y_1781_);
lean_dec(v_name_1774_);
lean_dec(v_head_1772_);
lean_dec_ref(v___f_1771_);
v_a_1901_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1903_ = v___x_1797_;
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1797_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1901_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
}
}
}
else
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1918_; 
lean_dec(v_a_1786_);
lean_dec_ref(v___y_1781_);
lean_dec(v_name_1774_);
lean_dec(v_head_1772_);
lean_dec_ref(v___f_1771_);
lean_dec(v_auxFunName_1768_);
lean_dec(v___x_1764_);
lean_dec_ref(v_indVal_1763_);
v_a_1911_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1913_ = v___x_1788_;
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1788_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
lean_dec_ref(v___y_1781_);
lean_dec(v_name_1774_);
lean_dec(v_head_1772_);
lean_dec_ref(v___f_1771_);
lean_dec(v_auxFunName_1768_);
lean_dec_ref(v___x_1765_);
lean_dec(v___x_1764_);
lean_dec_ref(v_indVal_1763_);
v_a_1919_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1785_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1785_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_indVal_1927_ = _args[0];
lean_object* v___x_1928_ = _args[1];
lean_object* v___x_1929_ = _args[2];
lean_object* v_numParams_1930_ = _args[3];
lean_object* v_header_1931_ = _args[4];
lean_object* v_auxFunName_1932_ = _args[5];
lean_object* v_levelInsts_1933_ = _args[6];
lean_object* v_numFields_1934_ = _args[7];
lean_object* v___f_1935_ = _args[8];
lean_object* v_head_1936_ = _args[9];
lean_object* v_a_1937_ = _args[10];
lean_object* v_name_1938_ = _args[11];
lean_object* v_xs_1939_ = _args[12];
lean_object* v_x_1940_ = _args[13];
lean_object* v___y_1941_ = _args[14];
lean_object* v___y_1942_ = _args[15];
lean_object* v___y_1943_ = _args[16];
lean_object* v___y_1944_ = _args[17];
lean_object* v___y_1945_ = _args[18];
lean_object* v___y_1946_ = _args[19];
lean_object* v___y_1947_ = _args[20];
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1(v_indVal_1927_, v___x_1928_, v___x_1929_, v_numParams_1930_, v_header_1931_, v_auxFunName_1932_, v_levelInsts_1933_, v_numFields_1934_, v___f_1935_, v_head_1936_, v_a_1937_, v_name_1938_, v_xs_1939_, v_x_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
lean_dec(v___y_1946_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
lean_dec_ref(v_x_1940_);
lean_dec_ref(v_xs_1939_);
lean_dec_ref(v_a_1937_);
lean_dec(v_numFields_1934_);
lean_dec_ref(v_levelInsts_1933_);
lean_dec_ref(v_header_1931_);
lean_dec(v_numParams_1930_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg(lean_object* v_a_1950_, lean_object* v_indVal_1951_, lean_object* v_auxFunName_1952_, lean_object* v_levelInsts_1953_, lean_object* v_header_1954_, lean_object* v_as_x27_1955_, lean_object* v_b_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
if (lean_obj_tag(v_as_x27_1955_) == 0)
{
lean_object* v___x_1964_; 
lean_dec_ref(v_header_1954_);
lean_dec_ref(v_levelInsts_1953_);
lean_dec(v_auxFunName_1952_);
lean_dec_ref(v_indVal_1951_);
lean_dec_ref(v_a_1950_);
v___x_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1964_, 0, v_b_1956_);
return v___x_1964_;
}
else
{
lean_object* v_head_1965_; lean_object* v_tail_1966_; lean_object* v___x_1967_; 
v_head_1965_ = lean_ctor_get(v_as_x27_1955_, 0);
lean_inc(v_head_1965_);
v_tail_1966_ = lean_ctor_get(v_as_x27_1955_, 1);
lean_inc(v_tail_1966_);
lean_dec_ref(v_as_x27_1955_);
lean_inc(v_head_1965_);
v___x_1967_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__1(v_head_1965_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; lean_object* v_toConstantVal_1969_; lean_object* v_numParams_1970_; lean_object* v_numFields_1971_; lean_object* v_name_1972_; lean_object* v_type_1973_; lean_object* v___f_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___f_1977_; uint8_t v___x_1978_; lean_object* v___x_1979_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1968_);
lean_dec_ref(v___x_1967_);
v_toConstantVal_1969_ = lean_ctor_get(v_a_1968_, 0);
lean_inc_ref(v_toConstantVal_1969_);
v_numParams_1970_ = lean_ctor_get(v_a_1968_, 3);
lean_inc(v_numParams_1970_);
v_numFields_1971_ = lean_ctor_get(v_a_1968_, 4);
lean_inc(v_numFields_1971_);
lean_dec(v_a_1968_);
v_name_1972_ = lean_ctor_get(v_toConstantVal_1969_, 0);
lean_inc(v_name_1972_);
v_type_1973_ = lean_ctor_get(v_toConstantVal_1969_, 2);
lean_inc_ref(v_type_1973_);
lean_dec_ref(v_toConstantVal_1969_);
v___f_1974_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___closed__0));
v___x_1975_ = lean_unsigned_to_nat(0u);
v___x_1976_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__0));
lean_inc_ref(v_a_1950_);
lean_inc_ref(v_levelInsts_1953_);
lean_inc(v_auxFunName_1952_);
lean_inc_ref(v_header_1954_);
lean_inc_ref(v_indVal_1951_);
v___f_1977_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___boxed), 21, 12);
lean_closure_set(v___f_1977_, 0, v_indVal_1951_);
lean_closure_set(v___f_1977_, 1, v___x_1975_);
lean_closure_set(v___f_1977_, 2, v___x_1976_);
lean_closure_set(v___f_1977_, 3, v_numParams_1970_);
lean_closure_set(v___f_1977_, 4, v_header_1954_);
lean_closure_set(v___f_1977_, 5, v_auxFunName_1952_);
lean_closure_set(v___f_1977_, 6, v_levelInsts_1953_);
lean_closure_set(v___f_1977_, 7, v_numFields_1971_);
lean_closure_set(v___f_1977_, 8, v___f_1974_);
lean_closure_set(v___f_1977_, 9, v_head_1965_);
lean_closure_set(v___f_1977_, 10, v_a_1950_);
lean_closure_set(v___f_1977_, 11, v_name_1972_);
v___x_1978_ = 0;
v___x_1979_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__2___redArg(v_type_1973_, v___f_1977_, v___x_1978_, v___x_1978_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; lean_object* v___x_1981_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_a_1980_);
lean_dec_ref(v___x_1979_);
v___x_1981_ = lean_array_push(v_b_1956_, v_a_1980_);
v_as_x27_1955_ = v_tail_1966_;
v_b_1956_ = v___x_1981_;
goto _start;
}
else
{
lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1990_; 
lean_dec(v_tail_1966_);
lean_dec_ref(v_b_1956_);
lean_dec_ref(v_header_1954_);
lean_dec_ref(v_levelInsts_1953_);
lean_dec(v_auxFunName_1952_);
lean_dec_ref(v_indVal_1951_);
lean_dec_ref(v_a_1950_);
v_a_1983_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1985_ = v___x_1979_;
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___x_1979_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1986_ == 0)
{
v___x_1988_ = v___x_1985_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_a_1983_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
}
else
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_1998_; 
lean_dec(v_tail_1966_);
lean_dec(v_head_1965_);
lean_dec_ref(v_b_1956_);
lean_dec_ref(v_header_1954_);
lean_dec_ref(v_levelInsts_1953_);
lean_dec(v_auxFunName_1952_);
lean_dec_ref(v_indVal_1951_);
lean_dec_ref(v_a_1950_);
v_a_1991_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1993_ = v___x_1967_;
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1967_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1996_; 
if (v_isShared_1994_ == 0)
{
v___x_1996_ = v___x_1993_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_a_1991_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___boxed(lean_object* v_a_1999_, lean_object* v_indVal_2000_, lean_object* v_auxFunName_2001_, lean_object* v_levelInsts_2002_, lean_object* v_header_2003_, lean_object* v_as_x27_2004_, lean_object* v_b_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg(v_a_1999_, v_indVal_2000_, v_auxFunName_2001_, v_levelInsts_2002_, v_header_2003_, v_as_x27_2004_, v_b_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__7(size_t v_sz_2014_, size_t v_i_2015_, lean_object* v_bs_2016_){
_start:
{
uint8_t v___x_2017_; 
v___x_2017_ = lean_usize_dec_lt(v_i_2015_, v_sz_2014_);
if (v___x_2017_ == 0)
{
return v_bs_2016_;
}
else
{
lean_object* v_v_2018_; lean_object* v___x_2019_; lean_object* v_bs_x27_2020_; size_t v___x_2021_; size_t v___x_2022_; lean_object* v___x_2023_; 
v_v_2018_ = lean_array_uget(v_bs_2016_, v_i_2015_);
v___x_2019_ = lean_unsigned_to_nat(0u);
v_bs_x27_2020_ = lean_array_uset(v_bs_2016_, v_i_2015_, v___x_2019_);
v___x_2021_ = ((size_t)1ULL);
v___x_2022_ = lean_usize_add(v_i_2015_, v___x_2021_);
v___x_2023_ = lean_array_uset(v_bs_x27_2020_, v_i_2015_, v_v_2018_);
v_i_2015_ = v___x_2022_;
v_bs_2016_ = v___x_2023_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__7___boxed(lean_object* v_sz_2025_, lean_object* v_i_2026_, lean_object* v_bs_2027_){
_start:
{
size_t v_sz_boxed_2028_; size_t v_i_boxed_2029_; lean_object* v_res_2030_; 
v_sz_boxed_2028_ = lean_unbox_usize(v_sz_2025_);
lean_dec(v_sz_2025_);
v_i_boxed_2029_ = lean_unbox_usize(v_i_2026_);
lean_dec(v_i_2026_);
v_res_2030_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__7(v_sz_boxed_2028_, v_i_boxed_2029_, v_bs_2027_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts(lean_object* v_header_2031_, lean_object* v_indVal_2032_, lean_object* v_auxFunName_2033_, lean_object* v_levelInsts_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_){
_start:
{
size_t v_sz_2042_; size_t v___x_2043_; lean_object* v___x_2044_; 
v_sz_2042_ = lean_array_size(v_levelInsts_2034_);
v___x_2043_ = ((size_t)0ULL);
lean_inc_ref(v_a_2039_);
lean_inc_ref(v_levelInsts_2034_);
v___x_2044_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg(v_sz_2042_, v___x_2043_, v_levelInsts_2034_, v_a_2039_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v_a_2045_; lean_object* v_ctors_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; 
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
lean_inc(v_a_2045_);
lean_dec_ref(v___x_2044_);
v_ctors_2046_ = lean_ctor_get(v_indVal_2032_, 4);
lean_inc(v_ctors_2046_);
v___x_2047_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__0));
v___x_2048_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg(v_a_2045_, v_indVal_2032_, v_auxFunName_2033_, v_levelInsts_2034_, v_header_2031_, v_ctors_2046_, v___x_2047_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2058_; 
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2051_ = v___x_2048_;
v_isShared_2052_ = v_isSharedCheck_2058_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2048_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2058_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
size_t v_sz_2053_; lean_object* v___x_2054_; lean_object* v___x_2056_; 
v_sz_2053_ = lean_array_size(v_a_2049_);
v___x_2054_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__7(v_sz_2053_, v___x_2043_, v_a_2049_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 0, v___x_2054_);
v___x_2056_ = v___x_2051_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2054_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
else
{
return v___x_2048_;
}
}
else
{
lean_dec_ref(v_levelInsts_2034_);
lean_dec(v_auxFunName_2033_);
lean_dec_ref(v_indVal_2032_);
lean_dec_ref(v_header_2031_);
return v___x_2044_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts___boxed(lean_object* v_header_2059_, lean_object* v_indVal_2060_, lean_object* v_auxFunName_2061_, lean_object* v_levelInsts_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts(v_header_2059_, v_indVal_2060_, v_auxFunName_2061_, v_levelInsts_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_);
lean_dec(v_a_2068_);
lean_dec_ref(v_a_2067_);
lean_dec(v_a_2066_);
lean_dec_ref(v_a_2065_);
lean_dec(v_a_2064_);
lean_dec_ref(v_a_2063_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0(size_t v_sz_2071_, size_t v_i_2072_, lean_object* v_bs_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
lean_object* v___x_2081_; 
lean_inc_ref(v___y_2078_);
v___x_2081_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___redArg(v_sz_2071_, v_i_2072_, v_bs_2073_, v___y_2078_);
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0___boxed(lean_object* v_sz_2082_, lean_object* v_i_2083_, lean_object* v_bs_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
size_t v_sz_boxed_2092_; size_t v_i_boxed_2093_; lean_object* v_res_2094_; 
v_sz_boxed_2092_ = lean_unbox_usize(v_sz_2082_);
lean_dec(v_sz_2082_);
v_i_boxed_2093_ = lean_unbox_usize(v_i_2083_);
lean_dec(v_i_2083_);
v_res_2094_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__0(v_sz_boxed_2092_, v_i_boxed_2093_, v_bs_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3(lean_object* v_upperBound_2095_, lean_object* v___x_2096_, lean_object* v_xs_2097_, lean_object* v_indVal_2098_, lean_object* v_auxFunName_2099_, lean_object* v_levelInsts_2100_, lean_object* v_inst_2101_, lean_object* v_R_2102_, lean_object* v_a_2103_, lean_object* v_b_2104_, lean_object* v_c_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v___x_2113_; 
lean_inc_ref(v___y_2110_);
v___x_2113_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3___redArg(v_upperBound_2095_, v___x_2096_, v_xs_2097_, v_indVal_2098_, v_auxFunName_2099_, v_levelInsts_2100_, v_a_2103_, v_b_2104_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3___boxed(lean_object** _args){
lean_object* v_upperBound_2114_ = _args[0];
lean_object* v___x_2115_ = _args[1];
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
v_res_2132_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3(v_upperBound_2114_, v___x_2115_, v_xs_2116_, v_indVal_2117_, v_auxFunName_2118_, v_levelInsts_2119_, v_inst_2120_, v_R_2121_, v_a_2122_, v_b_2123_, v_c_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec(v_a_2122_);
lean_dec_ref(v_levelInsts_2119_);
lean_dec_ref(v_xs_2116_);
lean_dec(v___x_2115_);
lean_dec(v_upperBound_2114_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4(lean_object* v_upperBound_2133_, lean_object* v_header_2134_, lean_object* v_xs_2135_, lean_object* v_indVal_2136_, lean_object* v_auxFunName_2137_, lean_object* v_levelInsts_2138_, lean_object* v_inst_2139_, lean_object* v_R_2140_, lean_object* v_a_2141_, lean_object* v_b_2142_, lean_object* v_c_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_){
_start:
{
lean_object* v___x_2151_; 
lean_inc_ref(v___y_2148_);
v___x_2151_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4___redArg(v_upperBound_2133_, v_header_2134_, v_xs_2135_, v_indVal_2136_, v_auxFunName_2137_, v_levelInsts_2138_, v_a_2141_, v_b_2142_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_2152_ = _args[0];
lean_object* v_header_2153_ = _args[1];
lean_object* v_xs_2154_ = _args[2];
lean_object* v_indVal_2155_ = _args[3];
lean_object* v_auxFunName_2156_ = _args[4];
lean_object* v_levelInsts_2157_ = _args[5];
lean_object* v_inst_2158_ = _args[6];
lean_object* v_R_2159_ = _args[7];
lean_object* v_a_2160_ = _args[8];
lean_object* v_b_2161_ = _args[9];
lean_object* v_c_2162_ = _args[10];
lean_object* v___y_2163_ = _args[11];
lean_object* v___y_2164_ = _args[12];
lean_object* v___y_2165_ = _args[13];
lean_object* v___y_2166_ = _args[14];
lean_object* v___y_2167_ = _args[15];
lean_object* v___y_2168_ = _args[16];
lean_object* v___y_2169_ = _args[17];
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4(v_upperBound_2152_, v_header_2153_, v_xs_2154_, v_indVal_2155_, v_auxFunName_2156_, v_levelInsts_2157_, v_inst_2158_, v_R_2159_, v_a_2160_, v_b_2161_, v_c_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v_a_2160_);
lean_dec_ref(v_levelInsts_2157_);
lean_dec_ref(v_xs_2154_);
lean_dec_ref(v_header_2153_);
lean_dec(v_upperBound_2152_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5(lean_object* v_upperBound_2171_, lean_object* v_inst_2172_, lean_object* v_R_2173_, lean_object* v_a_2174_, lean_object* v_b_2175_, lean_object* v_c_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
lean_object* v___x_2184_; 
v___x_2184_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___redArg(v_upperBound_2171_, v_a_2174_, v_b_2175_, v___y_2181_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5___boxed(lean_object* v_upperBound_2185_, lean_object* v_inst_2186_, lean_object* v_R_2187_, lean_object* v_a_2188_, lean_object* v_b_2189_, lean_object* v_c_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v_res_2198_; 
v_res_2198_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__5(v_upperBound_2185_, v_inst_2186_, v_R_2187_, v_a_2188_, v_b_2189_, v_c_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec(v_upperBound_2185_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6(lean_object* v_a_2199_, lean_object* v_indVal_2200_, lean_object* v_auxFunName_2201_, lean_object* v_levelInsts_2202_, lean_object* v_header_2203_, lean_object* v_as_2204_, lean_object* v_as_x27_2205_, lean_object* v_b_2206_, lean_object* v_a_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_){
_start:
{
lean_object* v___x_2215_; 
v___x_2215_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg(v_a_2199_, v_indVal_2200_, v_auxFunName_2201_, v_levelInsts_2202_, v_header_2203_, v_as_x27_2205_, v_b_2206_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___boxed(lean_object* v_a_2216_, lean_object* v_indVal_2217_, lean_object* v_auxFunName_2218_, lean_object* v_levelInsts_2219_, lean_object* v_header_2220_, lean_object* v_as_2221_, lean_object* v_as_x27_2222_, lean_object* v_b_2223_, lean_object* v_a_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6(v_a_2216_, v_indVal_2217_, v_auxFunName_2218_, v_levelInsts_2219_, v_header_2220_, v_as_2221_, v_as_x27_2222_, v_b_2223_, v_a_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
lean_dec(v_as_2221_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4(lean_object* v_upperBound_2233_, lean_object* v___x_2234_, lean_object* v_xs_2235_, lean_object* v_indVal_2236_, lean_object* v_auxFunName_2237_, lean_object* v_levelInsts_2238_, lean_object* v_inst_2239_, lean_object* v_R_2240_, lean_object* v_a_2241_, lean_object* v_b_2242_, lean_object* v_c_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_){
_start:
{
lean_object* v___x_2251_; 
lean_inc_ref(v___y_2248_);
v___x_2251_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___redArg(v_upperBound_2233_, v___x_2234_, v_xs_2235_, v_indVal_2236_, v_auxFunName_2237_, v_levelInsts_2238_, v_a_2241_, v_b_2242_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_);
return v___x_2251_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_2252_ = _args[0];
lean_object* v___x_2253_ = _args[1];
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
v_res_2270_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__3_spec__4(v_upperBound_2252_, v___x_2253_, v_xs_2254_, v_indVal_2255_, v_auxFunName_2256_, v_levelInsts_2257_, v_inst_2258_, v_R_2259_, v_a_2260_, v_b_2261_, v_c_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec_ref(v_levelInsts_2257_);
lean_dec_ref(v_xs_2254_);
lean_dec(v___x_2253_);
lean_dec(v_upperBound_2252_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6(lean_object* v_upperBound_2271_, lean_object* v_header_2272_, lean_object* v_xs_2273_, lean_object* v_indVal_2274_, lean_object* v_auxFunName_2275_, lean_object* v_levelInsts_2276_, lean_object* v_inst_2277_, lean_object* v_R_2278_, lean_object* v_a_2279_, lean_object* v_b_2280_, lean_object* v_c_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v___x_2289_; 
lean_inc_ref(v___y_2286_);
v___x_2289_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6___redArg(v_upperBound_2271_, v_header_2272_, v_xs_2273_, v_indVal_2274_, v_auxFunName_2275_, v_levelInsts_2276_, v_a_2279_, v_b_2280_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6___boxed(lean_object** _args){
lean_object* v_upperBound_2290_ = _args[0];
lean_object* v_header_2291_ = _args[1];
lean_object* v_xs_2292_ = _args[2];
lean_object* v_indVal_2293_ = _args[3];
lean_object* v_auxFunName_2294_ = _args[4];
lean_object* v_levelInsts_2295_ = _args[5];
lean_object* v_inst_2296_ = _args[6];
lean_object* v_R_2297_ = _args[7];
lean_object* v_a_2298_ = _args[8];
lean_object* v_b_2299_ = _args[9];
lean_object* v_c_2300_ = _args[10];
lean_object* v___y_2301_ = _args[11];
lean_object* v___y_2302_ = _args[12];
lean_object* v___y_2303_ = _args[13];
lean_object* v___y_2304_ = _args[14];
lean_object* v___y_2305_ = _args[15];
lean_object* v___y_2306_ = _args[16];
lean_object* v___y_2307_ = _args[17];
_start:
{
lean_object* v_res_2308_; 
v_res_2308_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__4_spec__6(v_upperBound_2290_, v_header_2291_, v_xs_2292_, v_indVal_2293_, v_auxFunName_2294_, v_levelInsts_2295_, v_inst_2296_, v_R_2297_, v_a_2298_, v_b_2299_, v_c_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec_ref(v_levelInsts_2295_);
lean_dec_ref(v_xs_2292_);
lean_dec_ref(v_header_2291_);
lean_dec(v_upperBound_2290_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody(lean_object* v_header_2322_, lean_object* v_indVal_2323_, lean_object* v_auxFunName_2324_, lean_object* v_levelInsts_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_){
_start:
{
lean_object* v___x_2333_; 
lean_inc_ref(v_indVal_2323_);
lean_inc_ref(v_header_2322_);
v___x_2333_ = l_Lean_Elab_Deriving_mkDiscrs(v_header_2322_, v_indVal_2323_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v_a_2334_; lean_object* v___x_2335_; 
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
lean_inc(v_a_2334_);
lean_dec_ref(v___x_2333_);
v___x_2335_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts(v_header_2322_, v_indVal_2323_, v_auxFunName_2324_, v_levelInsts_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2366_; 
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2338_ = v___x_2335_;
v_isShared_2339_ = v_isSharedCheck_2366_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2335_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2366_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v_ref_2340_; uint8_t v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; size_t v_sz_2349_; size_t v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2364_; 
v_ref_2340_ = lean_ctor_get(v_a_2330_, 5);
v___x_2341_ = 0;
v___x_2342_ = l_Lean_SourceInfo_fromRef(v_ref_2340_, v___x_2341_);
v___x_2343_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__0));
v___x_2344_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__1));
lean_inc(v___x_2342_);
v___x_2345_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2342_);
lean_ctor_set(v___x_2345_, 1, v___x_2343_);
v___x_2346_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_2347_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
lean_inc(v___x_2342_);
v___x_2348_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2342_);
lean_ctor_set(v___x_2348_, 1, v___x_2346_);
lean_ctor_set(v___x_2348_, 2, v___x_2347_);
v_sz_2349_ = lean_array_size(v_a_2334_);
v___x_2350_ = ((size_t)0ULL);
v___x_2351_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__2(v_sz_2349_, v___x_2350_, v_a_2334_);
v___x_2352_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody_mkAlts_spec__6___redArg___lam__1___closed__3);
v___x_2353_ = l_Lean_mkSepArray(v___x_2351_, v___x_2352_);
lean_dec_ref(v___x_2351_);
v___x_2354_ = l_Array_append___redArg(v___x_2347_, v___x_2353_);
lean_dec_ref(v___x_2353_);
lean_inc(v___x_2342_);
v___x_2355_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2342_);
lean_ctor_set(v___x_2355_, 1, v___x_2346_);
lean_ctor_set(v___x_2355_, 2, v___x_2354_);
v___x_2356_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__2));
lean_inc(v___x_2342_);
v___x_2357_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2342_);
lean_ctor_set(v___x_2357_, 1, v___x_2356_);
v___x_2358_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___closed__4));
v___x_2359_ = l_Array_append___redArg(v___x_2347_, v_a_2336_);
lean_dec(v_a_2336_);
lean_inc(v___x_2342_);
v___x_2360_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2342_);
lean_ctor_set(v___x_2360_, 1, v___x_2346_);
lean_ctor_set(v___x_2360_, 2, v___x_2359_);
lean_inc(v___x_2342_);
v___x_2361_ = l_Lean_Syntax_node1(v___x_2342_, v___x_2358_, v___x_2360_);
lean_inc_ref(v___x_2348_);
v___x_2362_ = l_Lean_Syntax_node6(v___x_2342_, v___x_2344_, v___x_2345_, v___x_2348_, v___x_2348_, v___x_2355_, v___x_2357_, v___x_2361_);
if (v_isShared_2339_ == 0)
{
lean_ctor_set(v___x_2338_, 0, v___x_2362_);
v___x_2364_ = v___x_2338_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v___x_2362_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
else
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2374_; 
lean_dec(v_a_2334_);
v_a_2367_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2369_ = v___x_2335_;
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2335_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2372_; 
if (v_isShared_2370_ == 0)
{
v___x_2372_ = v___x_2369_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_a_2367_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
}
else
{
lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2382_; 
lean_dec_ref(v_levelInsts_2325_);
lean_dec(v_auxFunName_2324_);
lean_dec_ref(v_indVal_2323_);
lean_dec_ref(v_header_2322_);
v_a_2375_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2377_ = v___x_2333_;
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___x_2333_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2380_; 
if (v_isShared_2378_ == 0)
{
v___x_2380_ = v___x_2377_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_a_2375_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody___boxed(lean_object* v_header_2383_, lean_object* v_indVal_2384_, lean_object* v_auxFunName_2385_, lean_object* v_levelInsts_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_){
_start:
{
lean_object* v_res_2394_; 
v_res_2394_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody(v_header_2383_, v_indVal_2384_, v_auxFunName_2385_, v_levelInsts_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
lean_dec(v_a_2390_);
lean_dec_ref(v_a_2389_);
lean_dec(v_a_2388_);
lean_dec_ref(v_a_2387_);
return v_res_2394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__0___redArg(lean_object* v_a_2395_, lean_object* v_b_2396_){
_start:
{
lean_object* v_array_2397_; lean_object* v_start_2398_; lean_object* v_stop_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2412_; 
v_array_2397_ = lean_ctor_get(v_a_2395_, 0);
v_start_2398_ = lean_ctor_get(v_a_2395_, 1);
v_stop_2399_ = lean_ctor_get(v_a_2395_, 2);
v_isSharedCheck_2412_ = !lean_is_exclusive(v_a_2395_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2401_ = v_a_2395_;
v_isShared_2402_ = v_isSharedCheck_2412_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_stop_2399_);
lean_inc(v_start_2398_);
lean_inc(v_array_2397_);
lean_dec(v_a_2395_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2412_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
uint8_t v___x_2403_; 
v___x_2403_ = lean_nat_dec_lt(v_start_2398_, v_stop_2399_);
if (v___x_2403_ == 0)
{
lean_del_object(v___x_2401_);
lean_dec(v_stop_2399_);
lean_dec(v_start_2398_);
lean_dec_ref(v_array_2397_);
return v_b_2396_;
}
else
{
lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2407_; 
v___x_2404_ = lean_unsigned_to_nat(1u);
v___x_2405_ = lean_nat_add(v_start_2398_, v___x_2404_);
lean_inc_ref(v_array_2397_);
if (v_isShared_2402_ == 0)
{
lean_ctor_set(v___x_2401_, 1, v___x_2405_);
v___x_2407_ = v___x_2401_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_array_2397_);
lean_ctor_set(v_reuseFailAlloc_2411_, 1, v___x_2405_);
lean_ctor_set(v_reuseFailAlloc_2411_, 2, v_stop_2399_);
v___x_2407_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2408_ = lean_array_fget(v_array_2397_, v_start_2398_);
lean_dec(v_start_2398_);
lean_dec_ref(v_array_2397_);
v___x_2409_ = lean_array_push(v_b_2396_, v___x_2408_);
v_a_2395_ = v___x_2407_;
v_b_2396_ = v___x_2409_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__12(void){
_start:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2443_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__3));
v___x_2444_ = l_String_toRawSubstring_x27(v___x_2443_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1(lean_object* v_argNames_2520_, lean_object* v_levelInsts_2521_, lean_object* v_as_2522_, size_t v_sz_2523_, size_t v_i_2524_, lean_object* v_b_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
uint8_t v___x_2533_; 
v___x_2533_ = lean_usize_dec_lt(v_i_2524_, v_sz_2523_);
if (v___x_2533_ == 0)
{
lean_object* v___x_2534_; 
lean_dec_ref(v___y_2530_);
lean_dec_ref(v_argNames_2520_);
v___x_2534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2534_, 0, v_b_2525_);
return v___x_2534_;
}
else
{
lean_object* v_snd_2535_; lean_object* v_fst_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2708_; 
v_snd_2535_ = lean_ctor_get(v_b_2525_, 1);
v_fst_2536_ = lean_ctor_get(v_b_2525_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v_b_2525_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2538_ = v_b_2525_;
v_isShared_2539_ = v_isSharedCheck_2708_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_snd_2535_);
lean_inc(v_fst_2536_);
lean_dec(v_b_2525_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2708_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v_array_2540_; lean_object* v_start_2541_; lean_object* v_stop_2542_; uint8_t v___x_2543_; 
v_array_2540_ = lean_ctor_get(v_snd_2535_, 0);
v_start_2541_ = lean_ctor_get(v_snd_2535_, 1);
v_stop_2542_ = lean_ctor_get(v_snd_2535_, 2);
v___x_2543_ = lean_nat_dec_lt(v_start_2541_, v_stop_2542_);
if (v___x_2543_ == 0)
{
lean_object* v___x_2545_; 
lean_dec_ref(v___y_2530_);
lean_dec_ref(v_argNames_2520_);
if (v_isShared_2539_ == 0)
{
v___x_2545_ = v___x_2538_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_fst_2536_);
lean_ctor_set(v_reuseFailAlloc_2547_, 1, v_snd_2535_);
v___x_2545_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
lean_object* v___x_2546_; 
v___x_2546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2545_);
return v___x_2546_;
}
}
else
{
lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2704_; 
lean_inc(v_stop_2542_);
lean_inc(v_start_2541_);
lean_inc_ref(v_array_2540_);
v_isSharedCheck_2704_ = !lean_is_exclusive(v_snd_2535_);
if (v_isSharedCheck_2704_ == 0)
{
lean_object* v_unused_2705_; lean_object* v_unused_2706_; lean_object* v_unused_2707_; 
v_unused_2705_ = lean_ctor_get(v_snd_2535_, 2);
lean_dec(v_unused_2705_);
v_unused_2706_ = lean_ctor_get(v_snd_2535_, 1);
lean_dec(v_unused_2706_);
v_unused_2707_ = lean_ctor_get(v_snd_2535_, 0);
lean_dec(v_unused_2707_);
v___x_2549_ = v_snd_2535_;
v_isShared_2550_ = v_isSharedCheck_2704_;
goto v_resetjp_2548_;
}
else
{
lean_dec(v_snd_2535_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2704_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v_a_2551_; lean_object* v___x_2552_; 
v_a_2551_ = lean_array_uget_borrowed(v_as_2522_, v_i_2524_);
lean_inc(v_a_2551_);
v___x_2552_ = l_Lean_Elab_Deriving_mkInductArgNames(v_a_2551_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; lean_object* v_numParams_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2559_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_a_2553_);
lean_dec_ref(v___x_2552_);
v_numParams_2554_ = lean_ctor_get(v_a_2551_, 1);
v___x_2555_ = lean_array_fget(v_array_2540_, v_start_2541_);
v___x_2556_ = lean_unsigned_to_nat(1u);
v___x_2557_ = lean_nat_add(v_start_2541_, v___x_2556_);
lean_dec(v_start_2541_);
if (v_isShared_2550_ == 0)
{
lean_ctor_set(v___x_2549_, 1, v___x_2557_);
v___x_2559_ = v___x_2549_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_array_2540_);
lean_ctor_set(v_reuseFailAlloc_2695_, 1, v___x_2557_);
lean_ctor_set(v_reuseFailAlloc_2695_, 2, v_stop_2542_);
v___x_2559_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
lean_object* v_lower_2561_; lean_object* v_upper_2562_; lean_object* v___x_2692_; lean_object* v___x_2693_; uint8_t v___x_2694_; 
v___x_2692_ = lean_unsigned_to_nat(0u);
v___x_2693_ = lean_array_get_size(v_a_2553_);
v___x_2694_ = lean_nat_dec_le(v_numParams_2554_, v___x_2692_);
if (v___x_2694_ == 0)
{
lean_inc(v_numParams_2554_);
v_lower_2561_ = v_numParams_2554_;
v_upper_2562_ = v___x_2693_;
goto v___jp_2560_;
}
else
{
v_lower_2561_ = v___x_2692_;
v_upper_2562_ = v___x_2693_;
goto v___jp_2560_;
}
v___jp_2560_:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2563_ = l_Array_toSubarray___redArg(v_a_2553_, v_lower_2561_, v_upper_2562_);
lean_inc_ref(v___x_2563_);
v___x_2564_ = l_Subarray_copy___redArg(v___x_2563_);
v___x_2565_ = l_Lean_Elab_Deriving_mkImplicitBinders(v___x_2564_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v_a_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc(v_a_2566_);
lean_dec_ref(v___x_2565_);
v___x_2567_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2554_);
lean_inc_ref(v_argNames_2520_);
v___x_2568_ = l_Array_toSubarray___redArg(v_argNames_2520_, v___x_2567_, v_numParams_2554_);
v___x_2569_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__0));
v___x_2570_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__0___redArg(v___x_2568_, v___x_2569_);
v___x_2571_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__0___redArg(v___x_2563_, v___x_2569_);
v_a_2572_ = l_Array_append___redArg(v___x_2570_, v___x_2571_);
lean_dec_ref(v___x_2571_);
v___x_2573_ = lean_array_get_size(v_a_2572_);
v___x_2574_ = l_Array_toSubarray___redArg(v_a_2572_, v___x_2567_, v___x_2573_);
v___x_2575_ = l_Subarray_copy___redArg(v___x_2574_);
lean_inc(v_a_2551_);
v___x_2576_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v_a_2551_, v___x_2575_, v___y_2530_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v_a_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; 
v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
lean_inc(v_a_2577_);
lean_dec_ref(v___x_2576_);
v___x_2578_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__2));
v___x_2579_ = l_Lean_Core_mkFreshUserName(v___x_2578_, v___y_2530_, v___y_2531_);
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v_a_2580_; lean_object* v___x_2581_; 
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
lean_inc(v_a_2580_);
lean_dec_ref(v___x_2579_);
lean_inc_ref(v_argNames_2520_);
lean_inc(v_a_2551_);
v___x_2581_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr(v_a_2551_, v_argNames_2520_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v_a_2582_; lean_object* v_ref_2583_; lean_object* v_quotContext_2584_; lean_object* v_currMacroScope_2585_; uint8_t v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2655_; 
v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
lean_inc(v_a_2582_);
lean_dec_ref(v___x_2581_);
v_ref_2583_ = lean_ctor_get(v___y_2530_, 5);
v_quotContext_2584_ = lean_ctor_get(v___y_2530_, 10);
v_currMacroScope_2585_ = lean_ctor_get(v___y_2530_, 11);
v___x_2586_ = 0;
v___x_2587_ = l_Lean_SourceInfo_fromRef(v_ref_2583_, v___x_2586_);
v___x_2588_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__4));
v___x_2589_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__6));
v___x_2590_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__8));
v___x_2591_ = lean_mk_syntax_ident(v_a_2580_);
lean_inc(v___x_2587_);
v___x_2592_ = l_Lean_Syntax_node1(v___x_2587_, v___x_2590_, v___x_2591_);
v___x_2593_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_2594_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_2595_ = l_Array_append___redArg(v___x_2594_, v_a_2566_);
lean_dec(v_a_2566_);
lean_inc(v___x_2587_);
v___x_2596_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2587_);
lean_ctor_set(v___x_2596_, 1, v___x_2593_);
lean_ctor_set(v___x_2596_, 2, v___x_2595_);
v___x_2597_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__10));
v___x_2598_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__11));
lean_inc(v___x_2587_);
v___x_2599_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2587_);
lean_ctor_set(v___x_2599_, 1, v___x_2598_);
v___x_2600_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_2601_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__12);
v___x_2602_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__13));
lean_inc(v_currMacroScope_2585_);
lean_inc(v_quotContext_2584_);
v___x_2603_ = l_Lean_addMacroScope(v_quotContext_2584_, v___x_2602_, v_currMacroScope_2585_);
v___x_2604_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__26));
lean_inc(v___x_2587_);
v___x_2605_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2605_, 0, v___x_2587_);
lean_ctor_set(v___x_2605_, 1, v___x_2601_);
lean_ctor_set(v___x_2605_, 2, v___x_2603_);
lean_ctor_set(v___x_2605_, 3, v___x_2604_);
lean_inc(v___x_2587_);
v___x_2606_ = l_Lean_Syntax_node1(v___x_2587_, v___x_2593_, v_a_2577_);
lean_inc(v___x_2587_);
v___x_2607_ = l_Lean_Syntax_node2(v___x_2587_, v___x_2600_, v___x_2605_, v___x_2606_);
lean_inc(v___x_2587_);
v___x_2608_ = l_Lean_Syntax_node2(v___x_2587_, v___x_2597_, v___x_2599_, v___x_2607_);
lean_inc(v___x_2587_);
v___x_2609_ = l_Lean_Syntax_node1(v___x_2587_, v___x_2593_, v___x_2608_);
v___x_2610_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__27));
lean_inc(v___x_2587_);
v___x_2611_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2587_);
lean_ctor_set(v___x_2611_, 1, v___x_2610_);
v___x_2612_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__29));
v___x_2613_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__30));
lean_inc(v___x_2587_);
v___x_2614_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2587_);
lean_ctor_set(v___x_2614_, 1, v___x_2613_);
lean_inc(v___x_2587_);
v___x_2615_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2587_);
lean_ctor_set(v___x_2615_, 1, v___x_2593_);
lean_ctor_set(v___x_2615_, 2, v___x_2594_);
v___x_2616_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__32));
v___x_2617_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__34));
v___x_2618_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__36));
v___x_2619_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1);
v___x_2620_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__2));
lean_inc(v_currMacroScope_2585_);
lean_inc(v_quotContext_2584_);
v___x_2621_ = l_Lean_addMacroScope(v_quotContext_2584_, v___x_2620_, v_currMacroScope_2585_);
v___x_2622_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__6));
lean_inc(v___x_2587_);
v___x_2623_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2587_);
lean_ctor_set(v___x_2623_, 1, v___x_2619_);
lean_ctor_set(v___x_2623_, 2, v___x_2621_);
lean_ctor_set(v___x_2623_, 3, v___x_2622_);
lean_inc_ref(v___x_2615_);
lean_inc(v___x_2587_);
v___x_2624_ = l_Lean_Syntax_node2(v___x_2587_, v___x_2618_, v___x_2623_, v___x_2615_);
v___x_2625_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__38));
v___x_2626_ = lean_mk_syntax_ident(v___x_2555_);
v___x_2627_ = l_Array_append___redArg(v___x_2594_, v_levelInsts_2521_);
lean_inc(v___x_2587_);
v___x_2628_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2628_, 0, v___x_2587_);
lean_ctor_set(v___x_2628_, 1, v___x_2593_);
lean_ctor_set(v___x_2628_, 2, v___x_2627_);
lean_inc(v___x_2587_);
v___x_2629_ = l_Lean_Syntax_node2(v___x_2587_, v___x_2600_, v___x_2626_, v___x_2628_);
lean_inc_ref(v___x_2615_);
lean_inc_ref(v___x_2611_);
lean_inc(v___x_2587_);
v___x_2630_ = l_Lean_Syntax_node3(v___x_2587_, v___x_2625_, v___x_2611_, v___x_2615_, v___x_2629_);
lean_inc_ref_n(v___x_2615_, 2);
lean_inc(v___x_2587_);
v___x_2631_ = l_Lean_Syntax_node3(v___x_2587_, v___x_2593_, v___x_2615_, v___x_2615_, v___x_2630_);
lean_inc(v___x_2587_);
v___x_2632_ = l_Lean_Syntax_node2(v___x_2587_, v___x_2617_, v___x_2624_, v___x_2631_);
v___x_2633_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__9));
lean_inc(v___x_2587_);
v___x_2634_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2587_);
lean_ctor_set(v___x_2634_, 1, v___x_2633_);
v___x_2635_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8);
v___x_2636_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__9));
lean_inc(v_currMacroScope_2585_);
lean_inc(v_quotContext_2584_);
v___x_2637_ = l_Lean_addMacroScope(v_quotContext_2584_, v___x_2636_, v_currMacroScope_2585_);
v___x_2638_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__12));
lean_inc(v___x_2587_);
v___x_2639_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2639_, 0, v___x_2587_);
lean_ctor_set(v___x_2639_, 1, v___x_2635_);
lean_ctor_set(v___x_2639_, 2, v___x_2637_);
lean_ctor_set(v___x_2639_, 3, v___x_2638_);
lean_inc_ref(v___x_2615_);
lean_inc(v___x_2587_);
v___x_2640_ = l_Lean_Syntax_node2(v___x_2587_, v___x_2618_, v___x_2639_, v___x_2615_);
lean_inc_ref(v___x_2615_);
lean_inc_ref(v___x_2611_);
lean_inc(v___x_2587_);
v___x_2641_ = l_Lean_Syntax_node3(v___x_2587_, v___x_2625_, v___x_2611_, v___x_2615_, v_a_2582_);
lean_inc_ref_n(v___x_2615_, 2);
lean_inc(v___x_2587_);
v___x_2642_ = l_Lean_Syntax_node3(v___x_2587_, v___x_2593_, v___x_2615_, v___x_2615_, v___x_2641_);
lean_inc(v___x_2587_);
v___x_2643_ = l_Lean_Syntax_node2(v___x_2587_, v___x_2617_, v___x_2640_, v___x_2642_);
lean_inc(v___x_2587_);
v___x_2644_ = l_Lean_Syntax_node3(v___x_2587_, v___x_2593_, v___x_2632_, v___x_2634_, v___x_2643_);
lean_inc(v___x_2587_);
v___x_2645_ = l_Lean_Syntax_node1(v___x_2587_, v___x_2616_, v___x_2644_);
v___x_2646_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__40));
lean_inc_ref(v___x_2615_);
lean_inc(v___x_2587_);
v___x_2647_ = l_Lean_Syntax_node1(v___x_2587_, v___x_2646_, v___x_2615_);
v___x_2648_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__10));
lean_inc(v___x_2587_);
v___x_2649_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2587_);
lean_ctor_set(v___x_2649_, 1, v___x_2648_);
lean_inc_ref(v___x_2615_);
lean_inc(v___x_2587_);
v___x_2650_ = l_Lean_Syntax_node6(v___x_2587_, v___x_2612_, v___x_2614_, v___x_2615_, v___x_2645_, v___x_2647_, v___x_2615_, v___x_2649_);
lean_inc(v___x_2587_);
v___x_2651_ = l_Lean_Syntax_node5(v___x_2587_, v___x_2589_, v___x_2592_, v___x_2596_, v___x_2609_, v___x_2611_, v___x_2650_);
v___x_2652_ = l_Lean_Syntax_node1(v___x_2587_, v___x_2588_, v___x_2651_);
v___x_2653_ = lean_array_push(v_fst_2536_, v___x_2652_);
if (v_isShared_2539_ == 0)
{
lean_ctor_set(v___x_2538_, 1, v___x_2559_);
lean_ctor_set(v___x_2538_, 0, v___x_2653_);
v___x_2655_ = v___x_2538_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v___x_2653_);
lean_ctor_set(v_reuseFailAlloc_2659_, 1, v___x_2559_);
v___x_2655_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
size_t v___x_2656_; size_t v___x_2657_; 
v___x_2656_ = ((size_t)1ULL);
v___x_2657_ = lean_usize_add(v_i_2524_, v___x_2656_);
v_i_2524_ = v___x_2657_;
v_b_2525_ = v___x_2655_;
goto _start;
}
}
else
{
lean_object* v_a_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2667_; 
lean_dec(v_a_2580_);
lean_dec(v_a_2577_);
lean_dec(v_a_2566_);
lean_dec_ref(v___x_2559_);
lean_dec(v___x_2555_);
lean_del_object(v___x_2538_);
lean_dec(v_fst_2536_);
lean_dec_ref(v___y_2530_);
lean_dec_ref(v_argNames_2520_);
v_a_2660_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2662_ = v___x_2581_;
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_a_2660_);
lean_dec(v___x_2581_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2665_; 
if (v_isShared_2663_ == 0)
{
v___x_2665_ = v___x_2662_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_a_2660_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
}
else
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2675_; 
lean_dec(v_a_2577_);
lean_dec(v_a_2566_);
lean_dec_ref(v___x_2559_);
lean_dec(v___x_2555_);
lean_del_object(v___x_2538_);
lean_dec(v_fst_2536_);
lean_dec_ref(v___y_2530_);
lean_dec_ref(v_argNames_2520_);
v_a_2668_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2670_ = v___x_2579_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2579_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2673_; 
if (v_isShared_2671_ == 0)
{
v___x_2673_ = v___x_2670_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2668_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
}
else
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2683_; 
lean_dec(v_a_2566_);
lean_dec_ref(v___x_2559_);
lean_dec(v___x_2555_);
lean_del_object(v___x_2538_);
lean_dec(v_fst_2536_);
lean_dec_ref(v___y_2530_);
lean_dec_ref(v_argNames_2520_);
v_a_2676_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2678_ = v___x_2576_;
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2576_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2681_; 
if (v_isShared_2679_ == 0)
{
v___x_2681_ = v___x_2678_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2676_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
}
else
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
lean_dec_ref(v___x_2563_);
lean_dec_ref(v___x_2559_);
lean_dec(v___x_2555_);
lean_del_object(v___x_2538_);
lean_dec(v_fst_2536_);
lean_dec_ref(v___y_2530_);
lean_dec_ref(v_argNames_2520_);
v_a_2684_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2686_ = v___x_2565_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2565_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2684_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
}
}
}
else
{
lean_object* v_a_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2703_; 
lean_del_object(v___x_2549_);
lean_dec(v_stop_2542_);
lean_dec(v_start_2541_);
lean_dec_ref(v_array_2540_);
lean_del_object(v___x_2538_);
lean_dec(v_fst_2536_);
lean_dec_ref(v___y_2530_);
lean_dec_ref(v_argNames_2520_);
v_a_2696_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2698_ = v___x_2552_;
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_a_2696_);
lean_dec(v___x_2552_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2701_; 
if (v_isShared_2699_ == 0)
{
v___x_2701_ = v___x_2698_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_a_2696_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___boxed(lean_object* v_argNames_2709_, lean_object* v_levelInsts_2710_, lean_object* v_as_2711_, lean_object* v_sz_2712_, lean_object* v_i_2713_, lean_object* v_b_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_){
_start:
{
size_t v_sz_boxed_2722_; size_t v_i_boxed_2723_; lean_object* v_res_2724_; 
v_sz_boxed_2722_ = lean_unbox_usize(v_sz_2712_);
lean_dec(v_sz_2712_);
v_i_boxed_2723_ = lean_unbox_usize(v_i_2713_);
lean_dec(v_i_2713_);
v_res_2724_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1(v_argNames_2709_, v_levelInsts_2710_, v_as_2711_, v_sz_boxed_2722_, v_i_boxed_2723_, v_b_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
lean_dec(v___y_2720_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec(v___y_2716_);
lean_dec_ref(v___y_2715_);
lean_dec_ref(v_as_2711_);
lean_dec_ref(v_levelInsts_2710_);
return v_res_2724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls(lean_object* v_ctx_2725_, lean_object* v_argNames_2726_, lean_object* v_levelInsts_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_){
_start:
{
lean_object* v_typeInfos_2735_; lean_object* v_auxFunNames_2736_; lean_object* v___x_2737_; lean_object* v_letDecls_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; size_t v_sz_2742_; size_t v___x_2743_; lean_object* v___x_2744_; 
v_typeInfos_2735_ = lean_ctor_get(v_ctx_2725_, 1);
lean_inc_ref(v_typeInfos_2735_);
v_auxFunNames_2736_ = lean_ctor_get(v_ctx_2725_, 2);
lean_inc_ref(v_auxFunNames_2736_);
lean_dec_ref(v_ctx_2725_);
v___x_2737_ = lean_unsigned_to_nat(0u);
v_letDecls_2738_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__0));
v___x_2739_ = lean_array_get_size(v_auxFunNames_2736_);
v___x_2740_ = l_Array_toSubarray___redArg(v_auxFunNames_2736_, v___x_2737_, v___x_2739_);
v___x_2741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2741_, 0, v_letDecls_2738_);
lean_ctor_set(v___x_2741_, 1, v___x_2740_);
v_sz_2742_ = lean_array_size(v_typeInfos_2735_);
v___x_2743_ = ((size_t)0ULL);
lean_inc_ref(v_a_2732_);
v___x_2744_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1(v_argNames_2726_, v_levelInsts_2727_, v_typeInfos_2735_, v_sz_2742_, v___x_2743_, v___x_2741_, v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_);
lean_dec_ref(v_typeInfos_2735_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v_a_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2753_; 
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2747_ = v___x_2744_;
v_isShared_2748_ = v_isSharedCheck_2753_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_a_2745_);
lean_dec(v___x_2744_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2753_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v_fst_2749_; lean_object* v___x_2751_; 
v_fst_2749_ = lean_ctor_get(v_a_2745_, 0);
lean_inc(v_fst_2749_);
lean_dec(v_a_2745_);
if (v_isShared_2748_ == 0)
{
lean_ctor_set(v___x_2747_, 0, v_fst_2749_);
v___x_2751_ = v___x_2747_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_fst_2749_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
}
else
{
lean_object* v_a_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2761_; 
v_a_2754_ = lean_ctor_get(v___x_2744_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2756_ = v___x_2744_;
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_a_2754_);
lean_dec(v___x_2744_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2759_; 
if (v_isShared_2757_ == 0)
{
v___x_2759_ = v___x_2756_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_a_2754_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls___boxed(lean_object* v_ctx_2762_, lean_object* v_argNames_2763_, lean_object* v_levelInsts_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_){
_start:
{
lean_object* v_res_2772_; 
v_res_2772_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls(v_ctx_2762_, v_argNames_2763_, v_levelInsts_2764_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_);
lean_dec(v_a_2770_);
lean_dec_ref(v_a_2769_);
lean_dec(v_a_2768_);
lean_dec_ref(v_a_2767_);
lean_dec(v_a_2766_);
lean_dec_ref(v_a_2765_);
lean_dec_ref(v_levelInsts_2764_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__0(lean_object* v_inst_2773_, lean_object* v_R_2774_, lean_object* v_a_2775_, lean_object* v_b_2776_){
_start:
{
lean_object* v___x_2777_; 
v___x_2777_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__0___redArg(v_a_2775_, v_b_2776_);
return v___x_2777_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__2(size_t v_sz_2778_, size_t v_i_2779_, lean_object* v_bs_2780_){
_start:
{
uint8_t v___x_2781_; 
v___x_2781_ = lean_usize_dec_lt(v_i_2779_, v_sz_2778_);
if (v___x_2781_ == 0)
{
return v_bs_2780_;
}
else
{
lean_object* v_v_2782_; lean_object* v___x_2783_; lean_object* v_bs_x27_2784_; size_t v___x_2785_; size_t v___x_2786_; lean_object* v___x_2787_; 
v_v_2782_ = lean_array_uget(v_bs_2780_, v_i_2779_);
v___x_2783_ = lean_unsigned_to_nat(0u);
v_bs_x27_2784_ = lean_array_uset(v_bs_2780_, v_i_2779_, v___x_2783_);
v___x_2785_ = ((size_t)1ULL);
v___x_2786_ = lean_usize_add(v_i_2779_, v___x_2785_);
v___x_2787_ = lean_array_uset(v_bs_x27_2784_, v_i_2779_, v_v_2782_);
v_i_2779_ = v___x_2786_;
v_bs_2780_ = v___x_2787_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__2___boxed(lean_object* v_sz_2789_, lean_object* v_i_2790_, lean_object* v_bs_2791_){
_start:
{
size_t v_sz_boxed_2792_; size_t v_i_boxed_2793_; lean_object* v_res_2794_; 
v_sz_boxed_2792_ = lean_unbox_usize(v_sz_2789_);
lean_dec(v_sz_2789_);
v_i_boxed_2793_ = lean_unbox_usize(v_i_2790_);
lean_dec(v_i_2790_);
v_res_2794_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__2(v_sz_boxed_2792_, v_i_boxed_2793_, v_bs_2791_);
return v_res_2794_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2805_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__0___redArg___closed__4));
v___x_2806_ = l_String_toRawSubstring_x27(v___x_2805_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg(size_t v_sz_2827_, size_t v_i_2828_, lean_object* v_bs_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
uint8_t v___x_2833_; 
v___x_2833_ = lean_usize_dec_lt(v_i_2828_, v_sz_2827_);
if (v___x_2833_ == 0)
{
lean_object* v___x_2834_; 
lean_dec_ref(v___y_2830_);
v___x_2834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2834_, 0, v_bs_2829_);
return v___x_2834_;
}
else
{
lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2835_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__1));
v___x_2836_ = l_Lean_Core_mkFreshUserName(v___x_2835_, v___y_2830_, v___y_2831_);
if (lean_obj_tag(v___x_2836_) == 0)
{
lean_object* v_a_2837_; lean_object* v_ref_2838_; lean_object* v_quotContext_2839_; lean_object* v_currMacroScope_2840_; lean_object* v_v_2841_; lean_object* v___x_2842_; lean_object* v_bs_x27_2843_; lean_object* v___x_2844_; uint8_t v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; size_t v___x_2874_; size_t v___x_2875_; lean_object* v___x_2876_; 
v_a_2837_ = lean_ctor_get(v___x_2836_, 0);
lean_inc(v_a_2837_);
lean_dec_ref(v___x_2836_);
v_ref_2838_ = lean_ctor_get(v___y_2830_, 5);
v_quotContext_2839_ = lean_ctor_get(v___y_2830_, 10);
v_currMacroScope_2840_ = lean_ctor_get(v___y_2830_, 11);
v_v_2841_ = lean_array_uget(v_bs_2829_, v_i_2828_);
v___x_2842_ = lean_unsigned_to_nat(0u);
v_bs_x27_2843_ = lean_array_uset(v_bs_2829_, v_i_2828_, v___x_2842_);
v___x_2844_ = lean_mk_syntax_ident(v_a_2837_);
v___x_2845_ = 0;
v___x_2846_ = l_Lean_SourceInfo_fromRef(v_ref_2838_, v___x_2845_);
v___x_2847_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__3));
v___x_2848_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__4));
lean_inc(v___x_2846_);
v___x_2849_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2846_);
lean_ctor_set(v___x_2849_, 1, v___x_2848_);
v___x_2850_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
lean_inc(v___x_2844_);
lean_inc(v___x_2846_);
v___x_2851_ = l_Lean_Syntax_node1(v___x_2846_, v___x_2850_, v___x_2844_);
v___x_2852_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__11));
lean_inc(v___x_2846_);
v___x_2853_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2846_);
lean_ctor_set(v___x_2853_, 1, v___x_2852_);
v___x_2854_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__6));
v___x_2855_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__5);
v___x_2856_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__6));
lean_inc(v_currMacroScope_2840_);
lean_inc(v_quotContext_2839_);
v___x_2857_ = l_Lean_addMacroScope(v_quotContext_2839_, v___x_2856_, v_currMacroScope_2840_);
v___x_2858_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__12));
lean_inc(v___x_2846_);
v___x_2859_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2859_, 0, v___x_2846_);
lean_ctor_set(v___x_2859_, 1, v___x_2855_);
lean_ctor_set(v___x_2859_, 2, v___x_2857_);
lean_ctor_set(v___x_2859_, 3, v___x_2858_);
v___x_2860_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__7));
lean_inc(v___x_2846_);
v___x_2861_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2846_);
lean_ctor_set(v___x_2861_, 1, v___x_2860_);
v___x_2862_ = lean_mk_syntax_ident(v_v_2841_);
lean_inc(v___x_2846_);
v___x_2863_ = l_Lean_Syntax_node1(v___x_2846_, v___x_2850_, v___x_2862_);
v___x_2864_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__10));
lean_inc(v___x_2846_);
v___x_2865_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2846_);
lean_ctor_set(v___x_2865_, 1, v___x_2864_);
lean_inc(v___x_2846_);
v___x_2866_ = l_Lean_Syntax_node4(v___x_2846_, v___x_2854_, v___x_2859_, v___x_2861_, v___x_2863_, v___x_2865_);
lean_inc(v___x_2846_);
v___x_2867_ = l_Lean_Syntax_node2(v___x_2846_, v___x_2850_, v___x_2853_, v___x_2866_);
v___x_2868_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
lean_inc(v___x_2846_);
v___x_2869_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2846_);
lean_ctor_set(v___x_2869_, 1, v___x_2850_);
lean_ctor_set(v___x_2869_, 2, v___x_2868_);
v___x_2870_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__13));
lean_inc(v___x_2846_);
v___x_2871_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2846_);
lean_ctor_set(v___x_2871_, 1, v___x_2870_);
v___x_2872_ = l_Lean_Syntax_node5(v___x_2846_, v___x_2847_, v___x_2849_, v___x_2851_, v___x_2867_, v___x_2869_, v___x_2871_);
v___x_2873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2873_, 0, v___x_2844_);
lean_ctor_set(v___x_2873_, 1, v___x_2872_);
v___x_2874_ = ((size_t)1ULL);
v___x_2875_ = lean_usize_add(v_i_2828_, v___x_2874_);
v___x_2876_ = lean_array_uset(v_bs_x27_2843_, v_i_2828_, v___x_2873_);
v_i_2828_ = v___x_2875_;
v_bs_2829_ = v___x_2876_;
goto _start;
}
else
{
lean_object* v_a_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2885_; 
lean_dec_ref(v___y_2830_);
lean_dec_ref(v_bs_2829_);
v_a_2878_ = lean_ctor_get(v___x_2836_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2880_ = v___x_2836_;
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_a_2878_);
lean_dec(v___x_2836_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2883_; 
if (v_isShared_2881_ == 0)
{
v___x_2883_ = v___x_2880_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_a_2878_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___boxed(lean_object* v_sz_2886_, lean_object* v_i_2887_, lean_object* v_bs_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
size_t v_sz_boxed_2892_; size_t v_i_boxed_2893_; lean_object* v_res_2894_; 
v_sz_boxed_2892_ = lean_unbox_usize(v_sz_2886_);
lean_dec(v_sz_2886_);
v_i_boxed_2893_ = lean_unbox_usize(v_i_2887_);
lean_dec(v_i_2887_);
v_res_2894_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg(v_sz_boxed_2892_, v_i_boxed_2893_, v_bs_2888_, v___y_2889_, v___y_2890_);
lean_dec(v___y_2890_);
return v_res_2894_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__1(size_t v_sz_2895_, size_t v_i_2896_, lean_object* v_bs_2897_){
_start:
{
uint8_t v___x_2898_; 
v___x_2898_ = lean_usize_dec_lt(v_i_2896_, v_sz_2895_);
if (v___x_2898_ == 0)
{
return v_bs_2897_;
}
else
{
lean_object* v_v_2899_; lean_object* v___x_2900_; lean_object* v_bs_x27_2901_; size_t v___x_2902_; size_t v___x_2903_; lean_object* v___x_2904_; 
v_v_2899_ = lean_array_uget(v_bs_2897_, v_i_2896_);
v___x_2900_ = lean_unsigned_to_nat(0u);
v_bs_x27_2901_ = lean_array_uset(v_bs_2897_, v_i_2896_, v___x_2900_);
v___x_2902_ = ((size_t)1ULL);
v___x_2903_ = lean_usize_add(v_i_2896_, v___x_2902_);
v___x_2904_ = lean_array_uset(v_bs_x27_2901_, v_i_2896_, v_v_2899_);
v_i_2896_ = v___x_2903_;
v_bs_2897_ = v___x_2904_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__1___boxed(lean_object* v_sz_2906_, lean_object* v_i_2907_, lean_object* v_bs_2908_){
_start:
{
size_t v_sz_boxed_2909_; size_t v_i_boxed_2910_; lean_object* v_res_2911_; 
v_sz_boxed_2909_ = lean_unbox_usize(v_sz_2906_);
lean_dec(v_sz_2906_);
v_i_boxed_2910_ = lean_unbox_usize(v_i_2907_);
lean_dec(v_i_2907_);
v_res_2911_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__1(v_sz_boxed_2909_, v_i_boxed_2910_, v_bs_2908_);
return v_res_2911_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__7(void){
_start:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; 
v___x_2919_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__7));
v___x_2920_ = l_String_toRawSubstring_x27(v___x_2919_);
return v___x_2920_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20(void){
_start:
{
lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2945_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__19));
v___x_2946_ = l_Lean_stringToMessageData(v___x_2945_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction(lean_object* v_ctx_2947_, lean_object* v_i_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_){
_start:
{
lean_object* v_typeInfos_2956_; lean_object* v_auxFunNames_2957_; uint8_t v_usePartial_2958_; lean_object* v___x_2959_; lean_object* v_indVal_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v_typeInfos_2956_ = lean_ctor_get(v_ctx_2947_, 1);
v_auxFunNames_2957_ = lean_ctor_get(v_ctx_2947_, 2);
v_usePartial_2958_ = lean_ctor_get_uint8(v_ctx_2947_, sizeof(void*)*3);
v___x_2959_ = l_Lean_instInhabitedInductiveVal_default;
v_indVal_2960_ = lean_array_get(v___x_2959_, v_typeInfos_2956_, v_i_2948_);
v___x_2961_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__0));
v___x_2962_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__14));
v___x_2963_ = lean_unsigned_to_nat(1u);
lean_inc(v_indVal_2960_);
v___x_2964_ = l_Lean_Elab_Deriving_mkHeader(v___x_2962_, v___x_2963_, v_indVal_2960_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v_toConstantVal_2965_; lean_object* v_a_2966_; lean_object* v_levelParams_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_3206_; 
v_toConstantVal_2965_ = lean_ctor_get(v_indVal_2960_, 0);
lean_inc_ref(v_toConstantVal_2965_);
v_a_2966_ = lean_ctor_get(v___x_2964_, 0);
lean_inc(v_a_2966_);
lean_dec_ref(v___x_2964_);
v_levelParams_2967_ = lean_ctor_get(v_toConstantVal_2965_, 1);
v_isSharedCheck_3206_ = !lean_is_exclusive(v_toConstantVal_2965_);
if (v_isSharedCheck_3206_ == 0)
{
lean_object* v_unused_3207_; lean_object* v_unused_3208_; 
v_unused_3207_ = lean_ctor_get(v_toConstantVal_2965_, 2);
lean_dec(v_unused_3207_);
v_unused_3208_ = lean_ctor_get(v_toConstantVal_2965_, 0);
lean_dec(v_unused_3208_);
v___x_2969_ = v_toConstantVal_2965_;
v_isShared_2970_ = v_isSharedCheck_3206_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_levelParams_2967_);
lean_dec(v_toConstantVal_2965_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_3206_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2971_; size_t v_sz_2972_; size_t v___x_2973_; lean_object* v___x_2974_; 
v___x_2971_ = lean_array_mk(v_levelParams_2967_);
v_sz_2972_ = lean_array_size(v___x_2971_);
v___x_2973_ = ((size_t)0ULL);
lean_inc_ref(v_a_2953_);
v___x_2974_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg(v_sz_2972_, v___x_2973_, v___x_2971_, v_a_2953_, v_a_2954_);
if (lean_obj_tag(v___x_2974_) == 0)
{
lean_object* v_a_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_3197_; 
v_a_2975_ = lean_ctor_get(v___x_2974_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_2977_ = v___x_2974_;
v_isShared_2978_ = v_isSharedCheck_3197_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_a_2975_);
lean_dec(v___x_2974_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_3197_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2979_; lean_object* v_fst_2980_; lean_object* v_snd_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_3196_; 
v___x_2979_ = l_Array_unzip___redArg(v_a_2975_);
lean_dec(v_a_2975_);
v_fst_2980_ = lean_ctor_get(v___x_2979_, 0);
v_snd_2981_ = lean_ctor_get(v___x_2979_, 1);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_2983_ = v___x_2979_;
v_isShared_2984_ = v_isSharedCheck_3196_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_snd_2981_);
lean_inc(v_fst_2980_);
lean_dec(v___x_2979_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_3196_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2985_; lean_object* v_auxFunName_2986_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v_a_2993_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v_body_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; size_t v_sz_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_2985_ = lean_box(0);
v_auxFunName_2986_ = lean_array_get(v___x_2985_, v_auxFunNames_2957_, v_i_2948_);
v_sz_3178_ = lean_array_size(v_fst_2980_);
v___x_3179_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__2(v_sz_3178_, v___x_2973_, v_fst_2980_);
lean_inc_ref(v___x_3179_);
lean_inc(v_auxFunName_2986_);
lean_inc(v_indVal_2960_);
lean_inc(v_a_2966_);
v___x_3180_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprBody(v_a_2966_, v_indVal_2960_, v_auxFunName_2986_, v___x_3179_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_);
if (lean_obj_tag(v___x_3180_) == 0)
{
if (v_usePartial_2958_ == 0)
{
lean_object* v_a_3181_; 
lean_dec_ref(v___x_3179_);
lean_dec_ref(v_ctx_2947_);
v_a_3181_ = lean_ctor_get(v___x_3180_, 0);
lean_inc(v_a_3181_);
lean_dec_ref(v___x_3180_);
v_body_3126_ = v_a_3181_;
v___y_3127_ = v_a_2949_;
v___y_3128_ = v_a_2950_;
v___y_3129_ = v_a_2951_;
v___y_3130_ = v_a_2952_;
v___y_3131_ = v_a_2953_;
v___y_3132_ = v_a_2954_;
goto v___jp_3125_;
}
else
{
lean_object* v_a_3182_; lean_object* v_argNames_3183_; lean_object* v___x_3184_; 
v_a_3182_ = lean_ctor_get(v___x_3180_, 0);
lean_inc(v_a_3182_);
lean_dec_ref(v___x_3180_);
v_argNames_3183_ = lean_ctor_get(v_a_2966_, 1);
lean_inc_ref(v_argNames_3183_);
v___x_3184_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls(v_ctx_2947_, v_argNames_3183_, v___x_3179_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_);
lean_dec_ref(v___x_3179_);
if (lean_obj_tag(v___x_3184_) == 0)
{
lean_object* v_a_3185_; lean_object* v___x_3186_; 
v_a_3185_ = lean_ctor_get(v___x_3184_, 0);
lean_inc(v_a_3185_);
lean_dec_ref(v___x_3184_);
v___x_3186_ = l_Lean_Elab_Deriving_mkLet(v_a_3185_, v_a_3182_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_);
lean_dec(v_a_3185_);
if (lean_obj_tag(v___x_3186_) == 0)
{
lean_object* v_a_3187_; 
v_a_3187_ = lean_ctor_get(v___x_3186_, 0);
lean_inc(v_a_3187_);
lean_dec_ref(v___x_3186_);
v_body_3126_ = v_a_3187_;
v___y_3127_ = v_a_2949_;
v___y_3128_ = v_a_2950_;
v___y_3129_ = v_a_2951_;
v___y_3130_ = v_a_2952_;
v___y_3131_ = v_a_2953_;
v___y_3132_ = v_a_2954_;
goto v___jp_3125_;
}
else
{
lean_dec(v_auxFunName_2986_);
lean_del_object(v___x_2983_);
lean_dec(v_snd_2981_);
lean_del_object(v___x_2977_);
lean_del_object(v___x_2969_);
lean_dec(v_a_2966_);
lean_dec(v_indVal_2960_);
return v___x_3186_;
}
}
else
{
lean_object* v_a_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3195_; 
lean_dec(v_a_3182_);
lean_dec(v_auxFunName_2986_);
lean_del_object(v___x_2983_);
lean_dec(v_snd_2981_);
lean_del_object(v___x_2977_);
lean_del_object(v___x_2969_);
lean_dec(v_a_2966_);
lean_dec(v_indVal_2960_);
v_a_3188_ = lean_ctor_get(v___x_3184_, 0);
v_isSharedCheck_3195_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3190_ = v___x_3184_;
v_isShared_3191_ = v_isSharedCheck_3195_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_a_3188_);
lean_dec(v___x_3184_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3195_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
lean_object* v___x_3193_; 
if (v_isShared_3191_ == 0)
{
v___x_3193_ = v___x_3190_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v_a_3188_);
v___x_3193_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
return v___x_3193_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3179_);
lean_dec(v_auxFunName_2986_);
lean_del_object(v___x_2983_);
lean_dec(v_snd_2981_);
lean_del_object(v___x_2977_);
lean_del_object(v___x_2969_);
lean_dec(v_a_2966_);
lean_dec(v_indVal_2960_);
lean_dec_ref(v_ctx_2947_);
return v___x_3180_;
}
v___jp_2987_:
{
lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; size_t v_sz_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
v___x_2994_ = lean_array_pop(v___y_2989_);
v___x_2995_ = l_Array_append___redArg(v___x_2994_, v_snd_2981_);
lean_dec(v_snd_2981_);
v___x_2996_ = lean_mk_empty_array_with_capacity(v___x_2963_);
v___x_2997_ = lean_array_push(v___x_2996_, v_a_2993_);
v_sz_2998_ = lean_array_size(v___x_2997_);
v___x_2999_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__1(v_sz_2998_, v___x_2973_, v___x_2997_);
v___x_3000_ = l_Array_append___redArg(v___x_2995_, v___x_2999_);
lean_dec_ref(v___x_2999_);
if (v_usePartial_2958_ == 0)
{
lean_object* v_ref_3001_; lean_object* v_quotContext_3002_; lean_object* v_currMacroScope_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3013_; 
v_ref_3001_ = lean_ctor_get(v___y_2988_, 5);
lean_inc(v_ref_3001_);
v_quotContext_3002_ = lean_ctor_get(v___y_2988_, 10);
lean_inc(v_quotContext_3002_);
v_currMacroScope_3003_ = lean_ctor_get(v___y_2988_, 11);
lean_inc(v_currMacroScope_3003_);
lean_dec_ref(v___y_2988_);
v___x_3004_ = l_Lean_SourceInfo_fromRef(v_ref_3001_, v_usePartial_2958_);
lean_dec(v_ref_3001_);
v___x_3005_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__0));
v___x_3006_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__1));
lean_inc_ref(v___y_2991_);
v___x_3007_ = l_Lean_Name_mkStr4(v___x_2961_, v___y_2991_, v___x_3005_, v___x_3006_);
v___x_3008_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__2));
lean_inc_ref(v___y_2991_);
v___x_3009_ = l_Lean_Name_mkStr4(v___x_2961_, v___y_2991_, v___x_3005_, v___x_3008_);
v___x_3010_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_3011_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
lean_inc(v___x_3004_);
if (v_isShared_2970_ == 0)
{
lean_ctor_set_tag(v___x_2969_, 1);
lean_ctor_set(v___x_2969_, 2, v___x_3011_);
lean_ctor_set(v___x_2969_, 1, v___x_3010_);
lean_ctor_set(v___x_2969_, 0, v___x_3004_);
v___x_3013_ = v___x_2969_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v___x_3004_);
lean_ctor_set(v_reuseFailAlloc_3055_, 1, v___x_3010_);
lean_ctor_set(v_reuseFailAlloc_3055_, 2, v___x_3011_);
v___x_3013_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3019_; 
lean_inc_ref_n(v___x_3013_, 7);
lean_inc(v___x_3004_);
v___x_3014_ = l_Lean_Syntax_node7(v___x_3004_, v___x_3009_, v___x_3013_, v___x_3013_, v___x_3013_, v___x_3013_, v___x_3013_, v___x_3013_, v___x_3013_);
v___x_3015_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__3));
lean_inc_ref(v___y_2991_);
v___x_3016_ = l_Lean_Name_mkStr4(v___x_2961_, v___y_2991_, v___x_3005_, v___x_3015_);
v___x_3017_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__4));
lean_inc(v___x_3004_);
if (v_isShared_2984_ == 0)
{
lean_ctor_set_tag(v___x_2983_, 2);
lean_ctor_set(v___x_2983_, 1, v___x_3017_);
lean_ctor_set(v___x_2983_, 0, v___x_3004_);
v___x_3019_ = v___x_2983_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v___x_3004_);
lean_ctor_set(v_reuseFailAlloc_3054_, 1, v___x_3017_);
v___x_3019_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3052_; 
v___x_3020_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__5));
lean_inc_ref(v___y_2991_);
v___x_3021_ = l_Lean_Name_mkStr4(v___x_2961_, v___y_2991_, v___x_3005_, v___x_3020_);
v___x_3022_ = lean_mk_syntax_ident(v_auxFunName_2986_);
lean_inc_ref(v___x_3013_);
lean_inc(v___x_3004_);
v___x_3023_ = l_Lean_Syntax_node2(v___x_3004_, v___x_3021_, v___x_3022_, v___x_3013_);
v___x_3024_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__6));
lean_inc_ref(v___y_2991_);
v___x_3025_ = l_Lean_Name_mkStr4(v___x_2961_, v___y_2991_, v___x_3005_, v___x_3024_);
v___x_3026_ = l_Array_append___redArg(v___x_3011_, v___x_3000_);
lean_dec_ref(v___x_3000_);
lean_inc(v___x_3004_);
v___x_3027_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3027_, 0, v___x_3004_);
lean_ctor_set(v___x_3027_, 1, v___x_3010_);
lean_ctor_set(v___x_3027_, 2, v___x_3026_);
v___x_3028_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__9));
lean_inc_ref(v___y_2991_);
v___x_3029_ = l_Lean_Name_mkStr4(v___x_2961_, v___y_2991_, v___y_2992_, v___x_3028_);
v___x_3030_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__11));
lean_inc(v___x_3004_);
v___x_3031_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3004_);
lean_ctor_set(v___x_3031_, 1, v___x_3030_);
v___x_3032_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__7, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__7_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__7);
v___x_3033_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__8));
v___x_3034_ = l_Lean_addMacroScope(v_quotContext_3002_, v___x_3033_, v_currMacroScope_3003_);
v___x_3035_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__14));
lean_inc(v___x_3004_);
v___x_3036_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3004_);
lean_ctor_set(v___x_3036_, 1, v___x_3032_);
lean_ctor_set(v___x_3036_, 2, v___x_3034_);
lean_ctor_set(v___x_3036_, 3, v___x_3035_);
lean_inc(v___x_3004_);
v___x_3037_ = l_Lean_Syntax_node2(v___x_3004_, v___x_3029_, v___x_3031_, v___x_3036_);
lean_inc(v___x_3004_);
v___x_3038_ = l_Lean_Syntax_node1(v___x_3004_, v___x_3010_, v___x_3037_);
lean_inc(v___x_3004_);
v___x_3039_ = l_Lean_Syntax_node2(v___x_3004_, v___x_3025_, v___x_3027_, v___x_3038_);
v___x_3040_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__15));
lean_inc_ref(v___y_2991_);
v___x_3041_ = l_Lean_Name_mkStr4(v___x_2961_, v___y_2991_, v___x_3005_, v___x_3040_);
v___x_3042_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__27));
lean_inc(v___x_3004_);
v___x_3043_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3043_, 0, v___x_3004_);
lean_ctor_set(v___x_3043_, 1, v___x_3042_);
v___x_3044_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__16));
v___x_3045_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__17));
v___x_3046_ = l_Lean_Name_mkStr4(v___x_2961_, v___y_2991_, v___x_3044_, v___x_3045_);
lean_inc_ref_n(v___x_3013_, 2);
lean_inc(v___x_3004_);
v___x_3047_ = l_Lean_Syntax_node2(v___x_3004_, v___x_3046_, v___x_3013_, v___x_3013_);
lean_inc_ref(v___x_3013_);
lean_inc(v___x_3004_);
v___x_3048_ = l_Lean_Syntax_node4(v___x_3004_, v___x_3041_, v___x_3043_, v___y_2990_, v___x_3047_, v___x_3013_);
lean_inc(v___x_3004_);
v___x_3049_ = l_Lean_Syntax_node5(v___x_3004_, v___x_3016_, v___x_3019_, v___x_3023_, v___x_3039_, v___x_3048_, v___x_3013_);
v___x_3050_ = l_Lean_Syntax_node2(v___x_3004_, v___x_3007_, v___x_3014_, v___x_3049_);
if (v_isShared_2978_ == 0)
{
lean_ctor_set(v___x_2977_, 0, v___x_3050_);
v___x_3052_ = v___x_2977_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v___x_3050_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
}
}
else
{
lean_object* v_ref_3056_; lean_object* v_quotContext_3057_; lean_object* v_currMacroScope_3058_; uint8_t v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3069_; 
v_ref_3056_ = lean_ctor_get(v___y_2988_, 5);
lean_inc(v_ref_3056_);
v_quotContext_3057_ = lean_ctor_get(v___y_2988_, 10);
lean_inc(v_quotContext_3057_);
v_currMacroScope_3058_ = lean_ctor_get(v___y_2988_, 11);
lean_inc(v_currMacroScope_3058_);
lean_dec_ref(v___y_2988_);
v___x_3059_ = 0;
v___x_3060_ = l_Lean_SourceInfo_fromRef(v_ref_3056_, v___x_3059_);
lean_dec(v_ref_3056_);
v___x_3061_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__0));
v___x_3062_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__1));
lean_inc_ref(v___y_2991_);
v___x_3063_ = l_Lean_Name_mkStr4(v___x_2961_, v___y_2991_, v___x_3061_, v___x_3062_);
v___x_3064_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__2));
lean_inc_ref(v___y_2991_);
v___x_3065_ = l_Lean_Name_mkStr4(v___x_2961_, v___y_2991_, v___x_3061_, v___x_3064_);
v___x_3066_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_3067_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
lean_inc(v___x_3060_);
if (v_isShared_2970_ == 0)
{
lean_ctor_set_tag(v___x_2969_, 1);
lean_ctor_set(v___x_2969_, 2, v___x_3067_);
lean_ctor_set(v___x_2969_, 1, v___x_3066_);
lean_ctor_set(v___x_2969_, 0, v___x_3060_);
v___x_3069_ = v___x_2969_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v___x_3060_);
lean_ctor_set(v_reuseFailAlloc_3116_, 1, v___x_3066_);
lean_ctor_set(v_reuseFailAlloc_3116_, 2, v___x_3067_);
v___x_3069_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3073_; 
v___x_3070_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__18));
lean_inc_ref(v___y_2991_);
v___x_3071_ = l_Lean_Name_mkStr4(v___x_2961_, v___y_2991_, v___x_3061_, v___x_3070_);
lean_inc(v___x_3060_);
if (v_isShared_2984_ == 0)
{
lean_ctor_set_tag(v___x_2983_, 2);
lean_ctor_set(v___x_2983_, 1, v___x_3070_);
lean_ctor_set(v___x_2983_, 0, v___x_3060_);
v___x_3073_ = v___x_2983_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v___x_3060_);
lean_ctor_set(v_reuseFailAlloc_3115_, 1, v___x_3070_);
v___x_3073_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3113_; 
lean_inc(v___x_3060_);
v___x_3074_ = l_Lean_Syntax_node1(v___x_3060_, v___x_3071_, v___x_3073_);
lean_inc(v___x_3060_);
v___x_3075_ = l_Lean_Syntax_node1(v___x_3060_, v___x_3066_, v___x_3074_);
lean_inc_ref_n(v___x_3069_, 6);
lean_inc(v___x_3060_);
v___x_3076_ = l_Lean_Syntax_node7(v___x_3060_, v___x_3065_, v___x_3069_, v___x_3069_, v___x_3069_, v___x_3069_, v___x_3069_, v___x_3069_, v___x_3075_);
v___x_3077_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__3));
lean_inc_ref(v___y_2991_);
v___x_3078_ = l_Lean_Name_mkStr4(v___x_2961_, v___y_2991_, v___x_3061_, v___x_3077_);
v___x_3079_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__4));
lean_inc(v___x_3060_);
v___x_3080_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3080_, 0, v___x_3060_);
lean_ctor_set(v___x_3080_, 1, v___x_3079_);
v___x_3081_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__5));
lean_inc_ref(v___y_2991_);
v___x_3082_ = l_Lean_Name_mkStr4(v___x_2961_, v___y_2991_, v___x_3061_, v___x_3081_);
v___x_3083_ = lean_mk_syntax_ident(v_auxFunName_2986_);
lean_inc_ref(v___x_3069_);
lean_inc(v___x_3060_);
v___x_3084_ = l_Lean_Syntax_node2(v___x_3060_, v___x_3082_, v___x_3083_, v___x_3069_);
v___x_3085_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__6));
lean_inc_ref(v___y_2991_);
v___x_3086_ = l_Lean_Name_mkStr4(v___x_2961_, v___y_2991_, v___x_3061_, v___x_3085_);
v___x_3087_ = l_Array_append___redArg(v___x_3067_, v___x_3000_);
lean_dec_ref(v___x_3000_);
lean_inc(v___x_3060_);
v___x_3088_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3060_);
lean_ctor_set(v___x_3088_, 1, v___x_3066_);
lean_ctor_set(v___x_3088_, 2, v___x_3087_);
v___x_3089_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__9));
lean_inc_ref(v___y_2991_);
v___x_3090_ = l_Lean_Name_mkStr4(v___x_2961_, v___y_2991_, v___y_2992_, v___x_3089_);
v___x_3091_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__11));
lean_inc(v___x_3060_);
v___x_3092_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3092_, 0, v___x_3060_);
lean_ctor_set(v___x_3092_, 1, v___x_3091_);
v___x_3093_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__7, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__7_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__7);
v___x_3094_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__8));
v___x_3095_ = l_Lean_addMacroScope(v_quotContext_3057_, v___x_3094_, v_currMacroScope_3058_);
v___x_3096_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__14));
lean_inc(v___x_3060_);
v___x_3097_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3097_, 0, v___x_3060_);
lean_ctor_set(v___x_3097_, 1, v___x_3093_);
lean_ctor_set(v___x_3097_, 2, v___x_3095_);
lean_ctor_set(v___x_3097_, 3, v___x_3096_);
lean_inc(v___x_3060_);
v___x_3098_ = l_Lean_Syntax_node2(v___x_3060_, v___x_3090_, v___x_3092_, v___x_3097_);
lean_inc(v___x_3060_);
v___x_3099_ = l_Lean_Syntax_node1(v___x_3060_, v___x_3066_, v___x_3098_);
lean_inc(v___x_3060_);
v___x_3100_ = l_Lean_Syntax_node2(v___x_3060_, v___x_3086_, v___x_3088_, v___x_3099_);
v___x_3101_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__15));
lean_inc_ref(v___y_2991_);
v___x_3102_ = l_Lean_Name_mkStr4(v___x_2961_, v___y_2991_, v___x_3061_, v___x_3101_);
v___x_3103_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__27));
lean_inc(v___x_3060_);
v___x_3104_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3104_, 0, v___x_3060_);
lean_ctor_set(v___x_3104_, 1, v___x_3103_);
v___x_3105_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__16));
v___x_3106_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__17));
v___x_3107_ = l_Lean_Name_mkStr4(v___x_2961_, v___y_2991_, v___x_3105_, v___x_3106_);
lean_inc_ref_n(v___x_3069_, 2);
lean_inc(v___x_3060_);
v___x_3108_ = l_Lean_Syntax_node2(v___x_3060_, v___x_3107_, v___x_3069_, v___x_3069_);
lean_inc_ref(v___x_3069_);
lean_inc(v___x_3060_);
v___x_3109_ = l_Lean_Syntax_node4(v___x_3060_, v___x_3102_, v___x_3104_, v___y_2990_, v___x_3108_, v___x_3069_);
lean_inc(v___x_3060_);
v___x_3110_ = l_Lean_Syntax_node5(v___x_3060_, v___x_3078_, v___x_3080_, v___x_3084_, v___x_3100_, v___x_3109_, v___x_3069_);
v___x_3111_ = l_Lean_Syntax_node2(v___x_3060_, v___x_3063_, v___x_3076_, v___x_3110_);
if (v_isShared_2978_ == 0)
{
lean_ctor_set(v___x_2977_, 0, v___x_3111_);
v___x_3113_ = v___x_2977_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v___x_3111_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
}
}
v___jp_3117_:
{
if (lean_obj_tag(v___y_3123_) == 0)
{
lean_object* v_a_3124_; 
v_a_3124_ = lean_ctor_get(v___y_3123_, 0);
lean_inc(v_a_3124_);
lean_dec_ref(v___y_3123_);
lean_inc_ref(v___y_3118_);
v___y_2988_ = v___y_3118_;
v___y_2989_ = v___y_3119_;
v___y_2990_ = v___y_3120_;
v___y_2991_ = v___y_3121_;
v___y_2992_ = v___y_3122_;
v_a_2993_ = v_a_3124_;
goto v___jp_2987_;
}
else
{
lean_dec_ref(v___y_3122_);
lean_dec_ref(v___y_3121_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
lean_dec(v_auxFunName_2986_);
lean_del_object(v___x_2983_);
lean_dec(v_snd_2981_);
lean_del_object(v___x_2977_);
lean_del_object(v___x_2969_);
return v___y_3123_;
}
}
v___jp_3125_:
{
lean_object* v_binders_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; uint8_t v___x_3141_; 
v_binders_3133_ = lean_ctor_get(v_a_2966_, 0);
lean_inc_ref(v_binders_3133_);
lean_dec(v_a_2966_);
v___x_3134_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__1));
v___x_3135_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__2));
v___x_3136_ = lean_box(0);
v___x_3137_ = lean_array_get_size(v_binders_3133_);
v___x_3138_ = lean_nat_sub(v___x_3137_, v___x_2963_);
v___x_3139_ = lean_array_get_borrowed(v___x_3136_, v_binders_3133_, v___x_3138_);
lean_dec(v___x_3138_);
v___x_3140_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__3));
lean_inc(v___x_3139_);
v___x_3141_ = l_Lean_Syntax_isOfKind(v___x_3139_, v___x_3140_);
if (v___x_3141_ == 0)
{
lean_object* v___x_3142_; lean_object* v___x_3143_; 
lean_dec(v_indVal_2960_);
v___x_3142_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20);
lean_inc_ref(v___y_3127_);
v___x_3143_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v___x_3142_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_);
v___y_3118_ = v___y_3131_;
v___y_3119_ = v_binders_3133_;
v___y_3120_ = v_body_3126_;
v___y_3121_ = v___x_3134_;
v___y_3122_ = v___x_3135_;
v___y_3123_ = v___x_3143_;
goto v___jp_3117_;
}
else
{
lean_object* v___x_3144_; uint8_t v___x_3145_; 
v___x_3144_ = l_Lean_Syntax_getArg(v___x_3139_, v___x_2963_);
lean_inc(v___x_3144_);
v___x_3145_ = l_Lean_Syntax_matchesNull(v___x_3144_, v___x_2963_);
if (v___x_3145_ == 0)
{
lean_object* v___x_3146_; lean_object* v___x_3147_; 
lean_dec(v___x_3144_);
lean_dec(v_indVal_2960_);
v___x_3146_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20);
lean_inc_ref(v___y_3127_);
v___x_3147_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v___x_3146_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_);
v___y_3118_ = v___y_3131_;
v___y_3119_ = v_binders_3133_;
v___y_3120_ = v_body_3126_;
v___y_3121_ = v___x_3134_;
v___y_3122_ = v___x_3135_;
v___y_3123_ = v___x_3147_;
goto v___jp_3117_;
}
else
{
lean_object* v___x_3148_; lean_object* v___x_3149_; uint8_t v___x_3150_; 
v___x_3148_ = lean_unsigned_to_nat(2u);
v___x_3149_ = l_Lean_Syntax_getArg(v___x_3139_, v___x_3148_);
lean_inc(v___x_3149_);
v___x_3150_ = l_Lean_Syntax_matchesNull(v___x_3149_, v___x_3148_);
if (v___x_3150_ == 0)
{
lean_object* v___x_3151_; lean_object* v___x_3152_; 
lean_dec(v___x_3149_);
lean_dec(v___x_3144_);
lean_dec(v_indVal_2960_);
v___x_3151_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20);
lean_inc_ref(v___y_3127_);
v___x_3152_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v___x_3151_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_);
v___y_3118_ = v___y_3131_;
v___y_3119_ = v_binders_3133_;
v___y_3120_ = v_body_3126_;
v___y_3121_ = v___x_3134_;
v___y_3122_ = v___x_3135_;
v___y_3123_ = v___x_3152_;
goto v___jp_3117_;
}
else
{
lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; uint8_t v___x_3156_; 
v___x_3153_ = lean_unsigned_to_nat(0u);
v___x_3154_ = lean_unsigned_to_nat(3u);
v___x_3155_ = l_Lean_Syntax_getArg(v___x_3139_, v___x_3154_);
v___x_3156_ = l_Lean_Syntax_matchesNull(v___x_3155_, v___x_3153_);
if (v___x_3156_ == 0)
{
lean_object* v___x_3157_; lean_object* v___x_3158_; 
lean_dec(v___x_3149_);
lean_dec(v___x_3144_);
lean_dec(v_indVal_2960_);
v___x_3157_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___closed__20);
lean_inc_ref(v___y_3127_);
v___x_3158_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0___redArg(v___x_3157_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_);
v___y_3118_ = v___y_3131_;
v___y_3119_ = v_binders_3133_;
v___y_3120_ = v_body_3126_;
v___y_3121_ = v___x_3134_;
v___y_3122_ = v___x_3135_;
v___y_3123_ = v___x_3158_;
goto v___jp_3117_;
}
else
{
lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3159_ = l_Lean_Syntax_getArg(v___x_3149_, v___x_2963_);
lean_dec(v___x_3149_);
v___x_3160_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType(v_indVal_2960_, v___x_3159_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_);
if (lean_obj_tag(v___x_3160_) == 0)
{
lean_object* v_a_3161_; lean_object* v_ref_3162_; lean_object* v___x_3163_; uint8_t v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
v_a_3161_ = lean_ctor_get(v___x_3160_, 0);
lean_inc(v_a_3161_);
lean_dec_ref(v___x_3160_);
v_ref_3162_ = lean_ctor_get(v___y_3131_, 5);
v___x_3163_ = l_Lean_Syntax_getArg(v___x_3144_, v___x_3153_);
lean_dec(v___x_3144_);
v___x_3164_ = 0;
v___x_3165_ = l_Lean_SourceInfo_fromRef(v_ref_3162_, v___x_3164_);
v___x_3166_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__4));
lean_inc(v___x_3165_);
v___x_3167_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3165_);
lean_ctor_set(v___x_3167_, 1, v___x_3166_);
v___x_3168_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
lean_inc(v___x_3165_);
v___x_3169_ = l_Lean_Syntax_node1(v___x_3165_, v___x_3168_, v___x_3163_);
v___x_3170_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__11));
lean_inc(v___x_3165_);
v___x_3171_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3165_);
lean_ctor_set(v___x_3171_, 1, v___x_3170_);
lean_inc(v___x_3165_);
v___x_3172_ = l_Lean_Syntax_node2(v___x_3165_, v___x_3168_, v___x_3171_, v_a_3161_);
v___x_3173_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
lean_inc(v___x_3165_);
v___x_3174_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3165_);
lean_ctor_set(v___x_3174_, 1, v___x_3168_);
lean_ctor_set(v___x_3174_, 2, v___x_3173_);
v___x_3175_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__13));
lean_inc(v___x_3165_);
v___x_3176_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3176_, 0, v___x_3165_);
lean_ctor_set(v___x_3176_, 1, v___x_3175_);
v___x_3177_ = l_Lean_Syntax_node5(v___x_3165_, v___x_3140_, v___x_3167_, v___x_3169_, v___x_3172_, v___x_3174_, v___x_3176_);
lean_inc_ref(v___y_3131_);
v___y_2988_ = v___y_3131_;
v___y_2989_ = v_binders_3133_;
v___y_2990_ = v_body_3126_;
v___y_2991_ = v___x_3134_;
v___y_2992_ = v___x_3135_;
v_a_2993_ = v___x_3177_;
goto v___jp_2987_;
}
else
{
lean_dec(v___x_3144_);
v___y_3118_ = v___y_3131_;
v___y_3119_ = v_binders_3133_;
v___y_3120_ = v_body_3126_;
v___y_3121_ = v___x_3134_;
v___y_3122_ = v___x_3135_;
v___y_3123_ = v___x_3160_;
goto v___jp_3117_;
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
lean_object* v_a_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3205_; 
lean_del_object(v___x_2969_);
lean_dec(v_a_2966_);
lean_dec(v_indVal_2960_);
lean_dec_ref(v_ctx_2947_);
v_a_3198_ = lean_ctor_get(v___x_2974_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3200_ = v___x_2974_;
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_a_3198_);
lean_dec(v___x_2974_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3203_; 
if (v_isShared_3201_ == 0)
{
v___x_3203_ = v___x_3200_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_3198_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
}
}
}
else
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3216_; 
lean_dec(v_indVal_2960_);
lean_dec_ref(v_ctx_2947_);
v_a_3209_ = lean_ctor_get(v___x_2964_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3211_ = v___x_2964_;
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_2964_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3214_; 
if (v_isShared_3212_ == 0)
{
v___x_3214_ = v___x_3211_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_a_3209_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction___boxed(lean_object* v_ctx_3217_, lean_object* v_i_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_){
_start:
{
lean_object* v_res_3226_; 
v_res_3226_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction(v_ctx_3217_, v_i_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_);
lean_dec(v_a_3224_);
lean_dec_ref(v_a_3223_);
lean_dec(v_a_3222_);
lean_dec_ref(v_a_3221_);
lean_dec(v_a_3220_);
lean_dec_ref(v_a_3219_);
lean_dec(v_i_3218_);
return v_res_3226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0(size_t v_sz_3227_, size_t v_i_3228_, lean_object* v_bs_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_){
_start:
{
lean_object* v___x_3237_; 
lean_inc_ref(v___y_3234_);
v___x_3237_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg(v_sz_3227_, v_i_3228_, v_bs_3229_, v___y_3234_, v___y_3235_);
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___boxed(lean_object* v_sz_3238_, lean_object* v_i_3239_, lean_object* v_bs_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_){
_start:
{
size_t v_sz_boxed_3248_; size_t v_i_boxed_3249_; lean_object* v_res_3250_; 
v_sz_boxed_3248_ = lean_unbox_usize(v_sz_3238_);
lean_dec(v_sz_3238_);
v_i_boxed_3249_ = lean_unbox_usize(v_i_3239_);
lean_dec(v_i_3239_);
v_res_3250_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0(v_sz_boxed_3248_, v_i_boxed_3249_, v_bs_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_);
lean_dec(v___y_3246_);
lean_dec_ref(v___y_3245_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3241_);
return v_res_3250_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0___redArg(lean_object* v_upperBound_3251_, lean_object* v_ctx_3252_, lean_object* v_a_3253_, lean_object* v_b_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_){
_start:
{
uint8_t v___x_3262_; 
v___x_3262_ = lean_nat_dec_lt(v_a_3253_, v_upperBound_3251_);
if (v___x_3262_ == 0)
{
lean_object* v___x_3263_; 
lean_dec(v_a_3253_);
lean_dec_ref(v_ctx_3252_);
v___x_3263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3263_, 0, v_b_3254_);
return v___x_3263_;
}
else
{
lean_object* v___x_3264_; 
lean_inc_ref(v_ctx_3252_);
v___x_3264_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction(v_ctx_3252_, v_a_3253_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_);
if (lean_obj_tag(v___x_3264_) == 0)
{
lean_object* v_a_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
v_a_3265_ = lean_ctor_get(v___x_3264_, 0);
lean_inc(v_a_3265_);
lean_dec_ref(v___x_3264_);
v___x_3266_ = lean_array_push(v_b_3254_, v_a_3265_);
v___x_3267_ = lean_unsigned_to_nat(1u);
v___x_3268_ = lean_nat_add(v_a_3253_, v___x_3267_);
lean_dec(v_a_3253_);
v_a_3253_ = v___x_3268_;
v_b_3254_ = v___x_3266_;
goto _start;
}
else
{
lean_object* v_a_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3277_; 
lean_dec_ref(v_b_3254_);
lean_dec(v_a_3253_);
lean_dec_ref(v_ctx_3252_);
v_a_3270_ = lean_ctor_get(v___x_3264_, 0);
v_isSharedCheck_3277_ = !lean_is_exclusive(v___x_3264_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3272_ = v___x_3264_;
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_a_3270_);
lean_dec(v___x_3264_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___x_3275_; 
if (v_isShared_3273_ == 0)
{
v___x_3275_ = v___x_3272_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_a_3270_);
v___x_3275_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
return v___x_3275_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0___redArg___boxed(lean_object* v_upperBound_3278_, lean_object* v_ctx_3279_, lean_object* v_a_3280_, lean_object* v_b_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_){
_start:
{
lean_object* v_res_3289_; 
v_res_3289_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0___redArg(v_upperBound_3278_, v_ctx_3279_, v_a_3280_, v_b_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3286_);
lean_dec(v___y_3285_);
lean_dec_ref(v___y_3284_);
lean_dec(v___y_3283_);
lean_dec_ref(v___y_3282_);
lean_dec(v_upperBound_3278_);
return v_res_3289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions(lean_object* v_ctx_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_){
_start:
{
lean_object* v_typeInfos_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v_auxDefs_3308_; lean_object* v___x_3309_; 
v_typeInfos_3305_ = lean_ctor_get(v_ctx_3297_, 1);
v___x_3306_ = lean_array_get_size(v_typeInfos_3305_);
v___x_3307_ = lean_unsigned_to_nat(0u);
v_auxDefs_3308_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__0));
v___x_3309_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0___redArg(v___x_3306_, v_ctx_3297_, v___x_3307_, v_auxDefs_3308_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_);
if (lean_obj_tag(v___x_3309_) == 0)
{
lean_object* v_a_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3330_; 
v_a_3310_ = lean_ctor_get(v___x_3309_, 0);
v_isSharedCheck_3330_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3330_ == 0)
{
v___x_3312_ = v___x_3309_;
v_isShared_3313_ = v_isSharedCheck_3330_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_a_3310_);
lean_dec(v___x_3309_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3330_;
goto v_resetjp_3311_;
}
v_resetjp_3311_:
{
lean_object* v_ref_3314_; uint8_t v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3328_; 
v_ref_3314_ = lean_ctor_get(v_a_3302_, 5);
v___x_3315_ = 0;
v___x_3316_ = l_Lean_SourceInfo_fromRef(v_ref_3314_, v___x_3315_);
v___x_3317_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions___closed__0));
v___x_3318_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions___closed__1));
lean_inc(v___x_3316_);
v___x_3319_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3316_);
lean_ctor_set(v___x_3319_, 1, v___x_3317_);
v___x_3320_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_3321_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
v___x_3322_ = l_Array_append___redArg(v___x_3321_, v_a_3310_);
lean_dec(v_a_3310_);
lean_inc(v___x_3316_);
v___x_3323_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3316_);
lean_ctor_set(v___x_3323_, 1, v___x_3320_);
lean_ctor_set(v___x_3323_, 2, v___x_3322_);
v___x_3324_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions___closed__2));
lean_inc(v___x_3316_);
v___x_3325_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3316_);
lean_ctor_set(v___x_3325_, 1, v___x_3324_);
v___x_3326_ = l_Lean_Syntax_node3(v___x_3316_, v___x_3318_, v___x_3319_, v___x_3323_, v___x_3325_);
if (v_isShared_3313_ == 0)
{
lean_ctor_set(v___x_3312_, 0, v___x_3326_);
v___x_3328_ = v___x_3312_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v___x_3326_);
v___x_3328_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
return v___x_3328_;
}
}
}
else
{
lean_object* v_a_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3338_; 
v_a_3331_ = lean_ctor_get(v___x_3309_, 0);
v_isSharedCheck_3338_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3338_ == 0)
{
v___x_3333_ = v___x_3309_;
v_isShared_3334_ = v_isSharedCheck_3338_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_a_3331_);
lean_dec(v___x_3309_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3338_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
lean_object* v___x_3336_; 
if (v_isShared_3334_ == 0)
{
v___x_3336_ = v___x_3333_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v_a_3331_);
v___x_3336_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
return v___x_3336_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions___boxed(lean_object* v_ctx_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_){
_start:
{
lean_object* v_res_3347_; 
v_res_3347_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions(v_ctx_3339_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_);
lean_dec(v_a_3345_);
lean_dec_ref(v_a_3344_);
lean_dec(v_a_3343_);
lean_dec_ref(v_a_3342_);
lean_dec(v_a_3341_);
lean_dec_ref(v_a_3340_);
return v_res_3347_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0(lean_object* v_upperBound_3348_, lean_object* v_ctx_3349_, lean_object* v_inst_3350_, lean_object* v_R_3351_, lean_object* v_a_3352_, lean_object* v_b_3353_, lean_object* v_c_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_){
_start:
{
lean_object* v___x_3362_; 
v___x_3362_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0___redArg(v_upperBound_3348_, v_ctx_3349_, v_a_3352_, v_b_3353_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_);
return v___x_3362_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0___boxed(lean_object* v_upperBound_3363_, lean_object* v_ctx_3364_, lean_object* v_inst_3365_, lean_object* v_R_3366_, lean_object* v_a_3367_, lean_object* v_b_3368_, lean_object* v_c_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_){
_start:
{
lean_object* v_res_3377_; 
v_res_3377_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions_spec__0(v_upperBound_3363_, v_ctx_3364_, v_inst_3365_, v_R_3366_, v_a_3367_, v_b_3368_, v_c_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
lean_dec(v___y_3375_);
lean_dec_ref(v___y_3374_);
lean_dec(v___y_3373_);
lean_dec_ref(v___y_3372_);
lean_dec(v___y_3371_);
lean_dec_ref(v___y_3370_);
lean_dec(v_upperBound_3363_);
return v_res_3377_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0_spec__0(lean_object* v_a_3378_, lean_object* v_as_3379_, size_t v_i_3380_, size_t v_stop_3381_){
_start:
{
uint8_t v___x_3382_; 
v___x_3382_ = lean_usize_dec_eq(v_i_3380_, v_stop_3381_);
if (v___x_3382_ == 0)
{
lean_object* v___x_3383_; uint8_t v___x_3384_; 
v___x_3383_ = lean_array_uget_borrowed(v_as_3379_, v_i_3380_);
v___x_3384_ = lean_name_eq(v_a_3378_, v___x_3383_);
if (v___x_3384_ == 0)
{
size_t v___x_3385_; size_t v___x_3386_; 
v___x_3385_ = ((size_t)1ULL);
v___x_3386_ = lean_usize_add(v_i_3380_, v___x_3385_);
v_i_3380_ = v___x_3386_;
goto _start;
}
else
{
return v___x_3384_;
}
}
else
{
uint8_t v___x_3388_; 
v___x_3388_ = 0;
return v___x_3388_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0_spec__0___boxed(lean_object* v_a_3389_, lean_object* v_as_3390_, lean_object* v_i_3391_, lean_object* v_stop_3392_){
_start:
{
size_t v_i_boxed_3393_; size_t v_stop_boxed_3394_; uint8_t v_res_3395_; lean_object* v_r_3396_; 
v_i_boxed_3393_ = lean_unbox_usize(v_i_3391_);
lean_dec(v_i_3391_);
v_stop_boxed_3394_ = lean_unbox_usize(v_stop_3392_);
lean_dec(v_stop_3392_);
v_res_3395_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0_spec__0(v_a_3389_, v_as_3390_, v_i_boxed_3393_, v_stop_boxed_3394_);
lean_dec_ref(v_as_3390_);
lean_dec(v_a_3389_);
v_r_3396_ = lean_box(v_res_3395_);
return v_r_3396_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0(lean_object* v_as_3397_, lean_object* v_a_3398_){
_start:
{
lean_object* v___x_3399_; lean_object* v___x_3400_; uint8_t v___x_3401_; 
v___x_3399_ = lean_unsigned_to_nat(0u);
v___x_3400_ = lean_array_get_size(v_as_3397_);
v___x_3401_ = lean_nat_dec_lt(v___x_3399_, v___x_3400_);
if (v___x_3401_ == 0)
{
return v___x_3401_;
}
else
{
if (v___x_3401_ == 0)
{
return v___x_3401_;
}
else
{
size_t v___x_3402_; size_t v___x_3403_; uint8_t v___x_3404_; 
v___x_3402_ = ((size_t)0ULL);
v___x_3403_ = lean_usize_of_nat(v___x_3400_);
v___x_3404_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0_spec__0(v_a_3398_, v_as_3397_, v___x_3402_, v___x_3403_);
return v___x_3404_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0___boxed(lean_object* v_as_3405_, lean_object* v_a_3406_){
_start:
{
uint8_t v_res_3407_; lean_object* v_r_3408_; 
v_res_3407_ = l_Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0(v_as_3405_, v_a_3406_);
lean_dec(v_a_3406_);
lean_dec_ref(v_as_3405_);
v_r_3408_ = lean_box(v_res_3407_);
return v_r_3408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg(size_t v_sz_3415_, size_t v_i_3416_, lean_object* v_bs_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_){
_start:
{
uint8_t v___x_3421_; 
v___x_3421_ = lean_usize_dec_lt(v_i_3416_, v_sz_3415_);
if (v___x_3421_ == 0)
{
lean_object* v___x_3422_; 
lean_dec_ref(v___y_3418_);
v___x_3422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3422_, 0, v_bs_3417_);
return v___x_3422_;
}
else
{
lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3423_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__1));
v___x_3424_ = l_Lean_Core_mkFreshUserName(v___x_3423_, v___y_3418_, v___y_3419_);
if (lean_obj_tag(v___x_3424_) == 0)
{
lean_object* v_a_3425_; lean_object* v_ref_3426_; lean_object* v_quotContext_3427_; lean_object* v_currMacroScope_3428_; lean_object* v_v_3429_; lean_object* v___x_3430_; lean_object* v_bs_x27_3431_; lean_object* v___x_3432_; uint8_t v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; size_t v___x_3459_; size_t v___x_3460_; lean_object* v___x_3461_; 
v_a_3425_ = lean_ctor_get(v___x_3424_, 0);
lean_inc(v_a_3425_);
lean_dec_ref(v___x_3424_);
v_ref_3426_ = lean_ctor_get(v___y_3418_, 5);
v_quotContext_3427_ = lean_ctor_get(v___y_3418_, 10);
v_currMacroScope_3428_ = lean_ctor_get(v___y_3418_, 11);
v_v_3429_ = lean_array_uget(v_bs_3417_, v_i_3416_);
v___x_3430_ = lean_unsigned_to_nat(0u);
v_bs_x27_3431_ = lean_array_uset(v_bs_3417_, v_i_3416_, v___x_3430_);
v___x_3432_ = lean_mk_syntax_ident(v_a_3425_);
v___x_3433_ = 0;
v___x_3434_ = l_Lean_SourceInfo_fromRef(v_ref_3426_, v___x_3433_);
v___x_3435_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg___closed__1));
v___x_3436_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__13));
lean_inc(v___x_3434_);
v___x_3437_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3434_);
lean_ctor_set(v___x_3437_, 1, v___x_3436_);
v___x_3438_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_3439_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__11));
lean_inc(v___x_3434_);
v___x_3440_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3440_, 0, v___x_3434_);
lean_ctor_set(v___x_3440_, 1, v___x_3439_);
lean_inc(v___x_3432_);
lean_inc(v___x_3434_);
v___x_3441_ = l_Lean_Syntax_node2(v___x_3434_, v___x_3438_, v___x_3432_, v___x_3440_);
v___x_3442_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__6));
v___x_3443_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__5);
v___x_3444_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__6));
lean_inc(v_currMacroScope_3428_);
lean_inc(v_quotContext_3427_);
v___x_3445_ = l_Lean_addMacroScope(v_quotContext_3427_, v___x_3444_, v_currMacroScope_3428_);
v___x_3446_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunction_spec__0___redArg___closed__12));
lean_inc(v___x_3434_);
v___x_3447_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3447_, 0, v___x_3434_);
lean_ctor_set(v___x_3447_, 1, v___x_3443_);
lean_ctor_set(v___x_3447_, 2, v___x_3445_);
lean_ctor_set(v___x_3447_, 3, v___x_3446_);
v___x_3448_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__7));
lean_inc(v___x_3434_);
v___x_3449_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3449_, 0, v___x_3434_);
lean_ctor_set(v___x_3449_, 1, v___x_3448_);
v___x_3450_ = lean_mk_syntax_ident(v_v_3429_);
lean_inc(v___x_3434_);
v___x_3451_ = l_Lean_Syntax_node1(v___x_3434_, v___x_3438_, v___x_3450_);
v___x_3452_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__10));
lean_inc(v___x_3434_);
v___x_3453_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3434_);
lean_ctor_set(v___x_3453_, 1, v___x_3452_);
lean_inc(v___x_3434_);
v___x_3454_ = l_Lean_Syntax_node4(v___x_3434_, v___x_3442_, v___x_3447_, v___x_3449_, v___x_3451_, v___x_3453_);
v___x_3455_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__14));
lean_inc(v___x_3434_);
v___x_3456_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3456_, 0, v___x_3434_);
lean_ctor_set(v___x_3456_, 1, v___x_3455_);
v___x_3457_ = l_Lean_Syntax_node4(v___x_3434_, v___x_3435_, v___x_3437_, v___x_3441_, v___x_3454_, v___x_3456_);
v___x_3458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3432_);
lean_ctor_set(v___x_3458_, 1, v___x_3457_);
v___x_3459_ = ((size_t)1ULL);
v___x_3460_ = lean_usize_add(v_i_3416_, v___x_3459_);
v___x_3461_ = lean_array_uset(v_bs_x27_3431_, v_i_3416_, v___x_3458_);
v_i_3416_ = v___x_3460_;
v_bs_3417_ = v___x_3461_;
goto _start;
}
else
{
lean_object* v_a_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3470_; 
lean_dec_ref(v___y_3418_);
lean_dec_ref(v_bs_3417_);
v_a_3463_ = lean_ctor_get(v___x_3424_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3465_ = v___x_3424_;
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___x_3424_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3468_; 
if (v_isShared_3466_ == 0)
{
v___x_3468_ = v___x_3465_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_a_3463_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
return v___x_3468_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg___boxed(lean_object* v_sz_3471_, lean_object* v_i_3472_, lean_object* v_bs_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_){
_start:
{
size_t v_sz_boxed_3477_; size_t v_i_boxed_3478_; lean_object* v_res_3479_; 
v_sz_boxed_3477_ = lean_unbox_usize(v_sz_3471_);
lean_dec(v_sz_3471_);
v_i_boxed_3478_ = lean_unbox_usize(v_i_3472_);
lean_dec(v_i_3472_);
v_res_3479_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg(v_sz_boxed_3477_, v_i_boxed_3478_, v_bs_3473_, v___y_3474_, v___y_3475_);
lean_dec(v___y_3475_);
return v_res_3479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__2(size_t v_sz_3480_, size_t v_i_3481_, lean_object* v_bs_3482_){
_start:
{
uint8_t v___x_3483_; 
v___x_3483_ = lean_usize_dec_lt(v_i_3481_, v_sz_3480_);
if (v___x_3483_ == 0)
{
return v_bs_3482_;
}
else
{
lean_object* v_v_3484_; lean_object* v___x_3485_; lean_object* v_bs_x27_3486_; size_t v___x_3487_; size_t v___x_3488_; lean_object* v___x_3489_; 
v_v_3484_ = lean_array_uget(v_bs_3482_, v_i_3481_);
v___x_3485_ = lean_unsigned_to_nat(0u);
v_bs_x27_3486_ = lean_array_uset(v_bs_3482_, v_i_3481_, v___x_3485_);
v___x_3487_ = ((size_t)1ULL);
v___x_3488_ = lean_usize_add(v_i_3481_, v___x_3487_);
v___x_3489_ = lean_array_uset(v_bs_x27_3486_, v_i_3481_, v_v_3484_);
v_i_3481_ = v___x_3488_;
v_bs_3482_ = v___x_3489_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__2___boxed(lean_object* v_sz_3491_, lean_object* v_i_3492_, lean_object* v_bs_3493_){
_start:
{
size_t v_sz_boxed_3494_; size_t v_i_boxed_3495_; lean_object* v_res_3496_; 
v_sz_boxed_3494_ = lean_unbox_usize(v_sz_3491_);
lean_dec(v_sz_3491_);
v_i_boxed_3495_ = lean_unbox_usize(v_i_3492_);
lean_dec(v_i_3492_);
v_res_3496_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__2(v_sz_boxed_3494_, v_i_boxed_3495_, v_bs_3493_);
return v_res_3496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3(lean_object* v_typeNames_3537_, lean_object* v_as_3538_, size_t v_sz_3539_, size_t v_i_3540_, lean_object* v_b_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_){
_start:
{
lean_object* v_a_3550_; uint8_t v___x_3554_; 
v___x_3554_ = lean_usize_dec_lt(v_i_3540_, v_sz_3539_);
if (v___x_3554_ == 0)
{
lean_object* v___x_3555_; 
lean_dec_ref(v___y_3546_);
v___x_3555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3555_, 0, v_b_3541_);
return v___x_3555_;
}
else
{
lean_object* v_snd_3556_; lean_object* v_fst_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3768_; 
v_snd_3556_ = lean_ctor_get(v_b_3541_, 1);
v_fst_3557_ = lean_ctor_get(v_b_3541_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v_b_3541_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3559_ = v_b_3541_;
v_isShared_3560_ = v_isSharedCheck_3768_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_snd_3556_);
lean_inc(v_fst_3557_);
lean_dec(v_b_3541_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3768_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v_array_3561_; lean_object* v_start_3562_; lean_object* v_stop_3563_; uint8_t v___x_3564_; 
v_array_3561_ = lean_ctor_get(v_snd_3556_, 0);
v_start_3562_ = lean_ctor_get(v_snd_3556_, 1);
v_stop_3563_ = lean_ctor_get(v_snd_3556_, 2);
v___x_3564_ = lean_nat_dec_lt(v_start_3562_, v_stop_3563_);
if (v___x_3564_ == 0)
{
lean_object* v___x_3566_; 
lean_dec_ref(v___y_3546_);
if (v_isShared_3560_ == 0)
{
v___x_3566_ = v___x_3559_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_fst_3557_);
lean_ctor_set(v_reuseFailAlloc_3568_, 1, v_snd_3556_);
v___x_3566_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
lean_object* v___x_3567_; 
v___x_3567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3567_, 0, v___x_3566_);
return v___x_3567_;
}
}
else
{
lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3764_; 
lean_inc(v_stop_3563_);
lean_inc(v_start_3562_);
lean_inc_ref(v_array_3561_);
v_isSharedCheck_3764_ = !lean_is_exclusive(v_snd_3556_);
if (v_isSharedCheck_3764_ == 0)
{
lean_object* v_unused_3765_; lean_object* v_unused_3766_; lean_object* v_unused_3767_; 
v_unused_3765_ = lean_ctor_get(v_snd_3556_, 2);
lean_dec(v_unused_3765_);
v_unused_3766_ = lean_ctor_get(v_snd_3556_, 1);
lean_dec(v_unused_3766_);
v_unused_3767_ = lean_ctor_get(v_snd_3556_, 0);
lean_dec(v_unused_3767_);
v___x_3570_ = v_snd_3556_;
v_isShared_3571_ = v_isSharedCheck_3764_;
goto v_resetjp_3569_;
}
else
{
lean_dec(v_snd_3556_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3764_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v_a_3572_; lean_object* v_toConstantVal_3573_; lean_object* v_name_3574_; lean_object* v_levelParams_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3762_; 
v_a_3572_ = lean_array_uget_borrowed(v_as_3538_, v_i_3540_);
v_toConstantVal_3573_ = lean_ctor_get(v_a_3572_, 0);
lean_inc_ref(v_toConstantVal_3573_);
v_name_3574_ = lean_ctor_get(v_toConstantVal_3573_, 0);
v_levelParams_3575_ = lean_ctor_get(v_toConstantVal_3573_, 1);
v_isSharedCheck_3762_ = !lean_is_exclusive(v_toConstantVal_3573_);
if (v_isSharedCheck_3762_ == 0)
{
lean_object* v_unused_3763_; 
v_unused_3763_ = lean_ctor_get(v_toConstantVal_3573_, 2);
lean_dec(v_unused_3763_);
v___x_3577_ = v_toConstantVal_3573_;
v_isShared_3578_ = v_isSharedCheck_3762_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_levelParams_3575_);
lean_inc(v_name_3574_);
lean_dec(v_toConstantVal_3573_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3762_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3583_; 
v___x_3579_ = lean_array_fget(v_array_3561_, v_start_3562_);
v___x_3580_ = lean_unsigned_to_nat(1u);
v___x_3581_ = lean_nat_add(v_start_3562_, v___x_3580_);
lean_dec(v_start_3562_);
if (v_isShared_3571_ == 0)
{
lean_ctor_set(v___x_3570_, 1, v___x_3581_);
v___x_3583_ = v___x_3570_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v_array_3561_);
lean_ctor_set(v_reuseFailAlloc_3761_, 1, v___x_3581_);
lean_ctor_set(v_reuseFailAlloc_3761_, 2, v_stop_3563_);
v___x_3583_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
uint8_t v___x_3584_; 
v___x_3584_ = l_Array_contains___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__0(v_typeNames_3537_, v_name_3574_);
if (v___x_3584_ == 0)
{
lean_object* v___x_3586_; 
lean_dec(v___x_3579_);
lean_del_object(v___x_3577_);
lean_dec(v_levelParams_3575_);
lean_dec(v_name_3574_);
if (v_isShared_3560_ == 0)
{
lean_ctor_set(v___x_3559_, 1, v___x_3583_);
v___x_3586_ = v___x_3559_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v_fst_3557_);
lean_ctor_set(v_reuseFailAlloc_3587_, 1, v___x_3583_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
v_a_3550_ = v___x_3586_;
goto v___jp_3549_;
}
}
else
{
lean_object* v___x_3588_; 
lean_del_object(v___x_3559_);
lean_inc(v_a_3572_);
v___x_3588_ = l_Lean_Elab_Deriving_mkInductArgNames(v_a_3572_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_);
if (lean_obj_tag(v___x_3588_) == 0)
{
lean_object* v_a_3589_; lean_object* v___x_3590_; 
v_a_3589_ = lean_ctor_get(v___x_3588_, 0);
lean_inc(v_a_3589_);
lean_dec_ref(v___x_3588_);
lean_inc(v_a_3589_);
v___x_3590_ = l_Lean_Elab_Deriving_mkImplicitBinders(v_a_3589_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_);
if (lean_obj_tag(v___x_3590_) == 0)
{
lean_object* v_a_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; 
v_a_3591_ = lean_ctor_get(v___x_3590_, 0);
lean_inc(v_a_3591_);
lean_dec_ref(v___x_3590_);
v___x_3592_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__14));
lean_inc(v_a_3589_);
lean_inc(v_a_3572_);
v___x_3593_ = l_Lean_Elab_Deriving_mkInstImplicitBinders(v___x_3592_, v_a_3572_, v_a_3589_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_);
if (lean_obj_tag(v___x_3593_) == 0)
{
lean_object* v_a_3594_; lean_object* v___x_3595_; size_t v_sz_3596_; size_t v___x_3597_; lean_object* v___x_3598_; 
v_a_3594_ = lean_ctor_get(v___x_3593_, 0);
lean_inc(v_a_3594_);
lean_dec_ref(v___x_3593_);
v___x_3595_ = lean_array_mk(v_levelParams_3575_);
v_sz_3596_ = lean_array_size(v___x_3595_);
v___x_3597_ = ((size_t)0ULL);
lean_inc_ref(v___y_3546_);
v___x_3598_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg(v_sz_3596_, v___x_3597_, v___x_3595_, v___y_3546_, v___y_3547_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_object* v_a_3599_; lean_object* v___x_3600_; lean_object* v_fst_3601_; lean_object* v_snd_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3728_; 
v_a_3599_ = lean_ctor_get(v___x_3598_, 0);
lean_inc(v_a_3599_);
lean_dec_ref(v___x_3598_);
v___x_3600_ = l_Array_unzip___redArg(v_a_3599_);
lean_dec(v_a_3599_);
v_fst_3601_ = lean_ctor_get(v___x_3600_, 0);
v_snd_3602_ = lean_ctor_get(v___x_3600_, 1);
v_isSharedCheck_3728_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3604_ = v___x_3600_;
v_isShared_3605_ = v_isSharedCheck_3728_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_snd_3602_);
lean_inc(v_fst_3601_);
lean_dec(v___x_3600_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3728_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v___x_3606_; 
lean_inc(v_a_3589_);
lean_inc(v_a_3572_);
v___x_3606_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v_a_3572_, v_a_3589_, v___y_3546_);
if (lean_obj_tag(v___x_3606_) == 0)
{
lean_object* v_a_3607_; lean_object* v___x_3608_; 
v_a_3607_ = lean_ctor_get(v___x_3606_, 0);
lean_inc(v_a_3607_);
lean_dec_ref(v___x_3606_);
lean_inc(v_a_3572_);
v___x_3608_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType(v_a_3572_, v_a_3607_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_);
if (lean_obj_tag(v___x_3608_) == 0)
{
lean_object* v_a_3609_; lean_object* v___x_3610_; 
v_a_3609_ = lean_ctor_get(v___x_3608_, 0);
lean_inc(v_a_3609_);
lean_dec_ref(v___x_3608_);
lean_inc(v_a_3572_);
v___x_3610_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr(v_a_3572_, v_a_3589_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_);
if (lean_obj_tag(v___x_3610_) == 0)
{
lean_object* v_a_3611_; lean_object* v___x_3612_; 
v_a_3611_ = lean_ctor_get(v___x_3610_, 0);
lean_inc(v_a_3611_);
lean_dec_ref(v___x_3610_);
v___x_3612_ = l_Lean_Elab_Deriving_mkInstName(v___x_3592_, v_name_3574_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_);
if (lean_obj_tag(v___x_3612_) == 0)
{
lean_object* v_a_3613_; lean_object* v_ref_3614_; lean_object* v_quotContext_3615_; lean_object* v_currMacroScope_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; uint8_t v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3626_; 
v_a_3613_ = lean_ctor_get(v___x_3612_, 0);
lean_inc(v_a_3613_);
lean_dec_ref(v___x_3612_);
v_ref_3614_ = lean_ctor_get(v___y_3546_, 5);
v_quotContext_3615_ = lean_ctor_get(v___y_3546_, 10);
v_currMacroScope_3616_ = lean_ctor_get(v___y_3546_, 11);
v___x_3617_ = l_Array_append___redArg(v_a_3591_, v_a_3594_);
lean_dec(v_a_3594_);
v___x_3618_ = l_Array_append___redArg(v___x_3617_, v_snd_3602_);
lean_dec(v_snd_3602_);
v___x_3619_ = 0;
v___x_3620_ = l_Lean_SourceInfo_fromRef(v_ref_3614_, v___x_3619_);
v___x_3621_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__0));
v___x_3622_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__1));
v___x_3623_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_3624_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType___closed__8);
lean_inc(v___x_3620_);
if (v_isShared_3578_ == 0)
{
lean_ctor_set_tag(v___x_3577_, 1);
lean_ctor_set(v___x_3577_, 2, v___x_3624_);
lean_ctor_set(v___x_3577_, 1, v___x_3623_);
lean_ctor_set(v___x_3577_, 0, v___x_3620_);
v___x_3626_ = v___x_3577_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v___x_3620_);
lean_ctor_set(v_reuseFailAlloc_3695_, 1, v___x_3623_);
lean_ctor_set(v_reuseFailAlloc_3695_, 2, v___x_3624_);
v___x_3626_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; size_t v_sz_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3693_; 
lean_inc_ref_n(v___x_3626_, 7);
lean_inc(v___x_3620_);
v___x_3627_ = l_Lean_Syntax_node7(v___x_3620_, v___x_3622_, v___x_3626_, v___x_3626_, v___x_3626_, v___x_3626_, v___x_3626_, v___x_3626_, v___x_3626_);
v___x_3628_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__2));
v___x_3629_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__3));
v___x_3630_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__5));
lean_inc_ref(v___x_3626_);
lean_inc(v___x_3620_);
v___x_3631_ = l_Lean_Syntax_node1(v___x_3620_, v___x_3630_, v___x_3626_);
lean_inc(v___x_3620_);
v___x_3632_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3632_, 0, v___x_3620_);
lean_ctor_set(v___x_3632_, 1, v___x_3628_);
v___x_3633_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__6));
v___x_3634_ = lean_mk_syntax_ident(v_a_3613_);
lean_inc_ref(v___x_3626_);
lean_inc(v___x_3620_);
v___x_3635_ = l_Lean_Syntax_node2(v___x_3620_, v___x_3633_, v___x_3634_, v___x_3626_);
lean_inc(v___x_3620_);
v___x_3636_ = l_Lean_Syntax_node1(v___x_3620_, v___x_3623_, v___x_3635_);
v___x_3637_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__8));
v___x_3638_ = l_Array_append___redArg(v___x_3624_, v___x_3618_);
lean_dec_ref(v___x_3618_);
lean_inc(v___x_3620_);
v___x_3639_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3639_, 0, v___x_3620_);
lean_ctor_set(v___x_3639_, 1, v___x_3623_);
lean_ctor_set(v___x_3639_, 2, v___x_3638_);
v___x_3640_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__10));
v___x_3641_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__11));
lean_inc(v___x_3620_);
v___x_3642_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3620_);
lean_ctor_set(v___x_3642_, 1, v___x_3641_);
v___x_3643_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__4));
v___x_3644_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__12);
v___x_3645_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__13));
lean_inc(v_currMacroScope_3616_);
lean_inc(v_quotContext_3615_);
v___x_3646_ = l_Lean_addMacroScope(v_quotContext_3615_, v___x_3645_, v_currMacroScope_3616_);
v___x_3647_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__26));
lean_inc(v___x_3620_);
v___x_3648_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3648_, 0, v___x_3620_);
lean_ctor_set(v___x_3648_, 1, v___x_3644_);
lean_ctor_set(v___x_3648_, 2, v___x_3646_);
lean_ctor_set(v___x_3648_, 3, v___x_3647_);
lean_inc(v___x_3620_);
v___x_3649_ = l_Lean_Syntax_node1(v___x_3620_, v___x_3623_, v_a_3609_);
lean_inc(v___x_3620_);
v___x_3650_ = l_Lean_Syntax_node2(v___x_3620_, v___x_3643_, v___x_3648_, v___x_3649_);
lean_inc(v___x_3620_);
v___x_3651_ = l_Lean_Syntax_node2(v___x_3620_, v___x_3640_, v___x_3642_, v___x_3650_);
lean_inc(v___x_3620_);
v___x_3652_ = l_Lean_Syntax_node2(v___x_3620_, v___x_3637_, v___x_3639_, v___x_3651_);
v___x_3653_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__10));
v___x_3654_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___closed__11));
lean_inc(v___x_3620_);
v___x_3655_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3655_, 0, v___x_3620_);
lean_ctor_set(v___x_3655_, 1, v___x_3654_);
v___x_3656_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__32));
v___x_3657_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__34));
v___x_3658_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__36));
v___x_3659_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__1);
v___x_3660_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__2));
lean_inc(v_currMacroScope_3616_);
lean_inc(v_quotContext_3615_);
v___x_3661_ = l_Lean_addMacroScope(v_quotContext_3615_, v___x_3660_, v_currMacroScope_3616_);
v___x_3662_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__6));
lean_inc(v___x_3620_);
v___x_3663_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3663_, 0, v___x_3620_);
lean_ctor_set(v___x_3663_, 1, v___x_3659_);
lean_ctor_set(v___x_3663_, 2, v___x_3661_);
lean_ctor_set(v___x_3663_, 3, v___x_3662_);
lean_inc_ref(v___x_3626_);
lean_inc(v___x_3620_);
v___x_3664_ = l_Lean_Syntax_node2(v___x_3620_, v___x_3658_, v___x_3663_, v___x_3626_);
v___x_3665_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__38));
v___x_3666_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__27));
lean_inc(v___x_3620_);
v___x_3667_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3667_, 0, v___x_3620_);
lean_ctor_set(v___x_3667_, 1, v___x_3666_);
v___x_3668_ = lean_mk_syntax_ident(v___x_3579_);
v_sz_3669_ = lean_array_size(v_fst_3601_);
v___x_3670_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__2(v_sz_3669_, v___x_3597_, v_fst_3601_);
v___x_3671_ = l_Array_append___redArg(v___x_3624_, v___x_3670_);
lean_dec_ref(v___x_3670_);
lean_inc(v___x_3620_);
v___x_3672_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3672_, 0, v___x_3620_);
lean_ctor_set(v___x_3672_, 1, v___x_3623_);
lean_ctor_set(v___x_3672_, 2, v___x_3671_);
lean_inc(v___x_3620_);
v___x_3673_ = l_Lean_Syntax_node2(v___x_3620_, v___x_3643_, v___x_3668_, v___x_3672_);
lean_inc_ref(v___x_3626_);
lean_inc_ref(v___x_3667_);
lean_inc(v___x_3620_);
v___x_3674_ = l_Lean_Syntax_node3(v___x_3620_, v___x_3665_, v___x_3667_, v___x_3626_, v___x_3673_);
lean_inc_ref_n(v___x_3626_, 2);
lean_inc(v___x_3620_);
v___x_3675_ = l_Lean_Syntax_node3(v___x_3620_, v___x_3623_, v___x_3626_, v___x_3626_, v___x_3674_);
lean_inc(v___x_3620_);
v___x_3676_ = l_Lean_Syntax_node2(v___x_3620_, v___x_3657_, v___x_3664_, v___x_3675_);
v___x_3677_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__8);
v___x_3678_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__9));
lean_inc(v_currMacroScope_3616_);
lean_inc(v_quotContext_3615_);
v___x_3679_ = l_Lean_addMacroScope(v_quotContext_3615_, v___x_3678_, v_currMacroScope_3616_);
v___x_3680_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__12));
lean_inc(v___x_3620_);
v___x_3681_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3620_);
lean_ctor_set(v___x_3681_, 1, v___x_3677_);
lean_ctor_set(v___x_3681_, 2, v___x_3679_);
lean_ctor_set(v___x_3681_, 3, v___x_3680_);
lean_inc_ref(v___x_3626_);
lean_inc(v___x_3620_);
v___x_3682_ = l_Lean_Syntax_node2(v___x_3620_, v___x_3658_, v___x_3681_, v___x_3626_);
lean_inc_ref(v___x_3626_);
lean_inc(v___x_3620_);
v___x_3683_ = l_Lean_Syntax_node3(v___x_3620_, v___x_3665_, v___x_3667_, v___x_3626_, v_a_3611_);
lean_inc_ref_n(v___x_3626_, 2);
lean_inc(v___x_3620_);
v___x_3684_ = l_Lean_Syntax_node3(v___x_3620_, v___x_3623_, v___x_3626_, v___x_3626_, v___x_3683_);
lean_inc(v___x_3620_);
v___x_3685_ = l_Lean_Syntax_node2(v___x_3620_, v___x_3657_, v___x_3682_, v___x_3684_);
lean_inc_ref(v___x_3626_);
lean_inc(v___x_3620_);
v___x_3686_ = l_Lean_Syntax_node3(v___x_3620_, v___x_3623_, v___x_3676_, v___x_3626_, v___x_3685_);
lean_inc(v___x_3620_);
v___x_3687_ = l_Lean_Syntax_node1(v___x_3620_, v___x_3656_, v___x_3686_);
lean_inc_ref(v___x_3626_);
lean_inc(v___x_3620_);
v___x_3688_ = l_Lean_Syntax_node3(v___x_3620_, v___x_3653_, v___x_3655_, v___x_3687_, v___x_3626_);
lean_inc(v___x_3620_);
v___x_3689_ = l_Lean_Syntax_node6(v___x_3620_, v___x_3629_, v___x_3631_, v___x_3632_, v___x_3626_, v___x_3636_, v___x_3652_, v___x_3688_);
v___x_3690_ = l_Lean_Syntax_node2(v___x_3620_, v___x_3621_, v___x_3627_, v___x_3689_);
v___x_3691_ = lean_array_push(v_fst_3557_, v___x_3690_);
if (v_isShared_3605_ == 0)
{
lean_ctor_set(v___x_3604_, 1, v___x_3583_);
lean_ctor_set(v___x_3604_, 0, v___x_3691_);
v___x_3693_ = v___x_3604_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v___x_3691_);
lean_ctor_set(v_reuseFailAlloc_3694_, 1, v___x_3583_);
v___x_3693_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
v_a_3550_ = v___x_3693_;
goto v___jp_3549_;
}
}
}
else
{
lean_object* v_a_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3703_; 
lean_dec(v_a_3611_);
lean_dec(v_a_3609_);
lean_del_object(v___x_3604_);
lean_dec(v_snd_3602_);
lean_dec(v_fst_3601_);
lean_dec(v_a_3594_);
lean_dec(v_a_3591_);
lean_dec_ref(v___x_3583_);
lean_dec(v___x_3579_);
lean_del_object(v___x_3577_);
lean_dec(v_fst_3557_);
lean_dec_ref(v___y_3546_);
v_a_3696_ = lean_ctor_get(v___x_3612_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3698_ = v___x_3612_;
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_a_3696_);
lean_dec(v___x_3612_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3701_; 
if (v_isShared_3699_ == 0)
{
v___x_3701_ = v___x_3698_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_a_3696_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
}
else
{
lean_object* v_a_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3711_; 
lean_dec(v_a_3609_);
lean_del_object(v___x_3604_);
lean_dec(v_snd_3602_);
lean_dec(v_fst_3601_);
lean_dec(v_a_3594_);
lean_dec(v_a_3591_);
lean_dec_ref(v___x_3583_);
lean_dec(v___x_3579_);
lean_del_object(v___x_3577_);
lean_dec(v_name_3574_);
lean_dec(v_fst_3557_);
lean_dec_ref(v___y_3546_);
v_a_3704_ = lean_ctor_get(v___x_3610_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3706_ = v___x_3610_;
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_a_3704_);
lean_dec(v___x_3610_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3709_; 
if (v_isShared_3707_ == 0)
{
v___x_3709_ = v___x_3706_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_a_3704_);
v___x_3709_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
return v___x_3709_;
}
}
}
}
else
{
lean_object* v_a_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3719_; 
lean_del_object(v___x_3604_);
lean_dec(v_snd_3602_);
lean_dec(v_fst_3601_);
lean_dec(v_a_3594_);
lean_dec(v_a_3591_);
lean_dec(v_a_3589_);
lean_dec_ref(v___x_3583_);
lean_dec(v___x_3579_);
lean_del_object(v___x_3577_);
lean_dec(v_name_3574_);
lean_dec(v_fst_3557_);
lean_dec_ref(v___y_3546_);
v_a_3712_ = lean_ctor_get(v___x_3608_, 0);
v_isSharedCheck_3719_ = !lean_is_exclusive(v___x_3608_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3714_ = v___x_3608_;
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_a_3712_);
lean_dec(v___x_3608_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___x_3717_; 
if (v_isShared_3715_ == 0)
{
v___x_3717_ = v___x_3714_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v_a_3712_);
v___x_3717_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
return v___x_3717_;
}
}
}
}
else
{
lean_object* v_a_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3727_; 
lean_del_object(v___x_3604_);
lean_dec(v_snd_3602_);
lean_dec(v_fst_3601_);
lean_dec(v_a_3594_);
lean_dec(v_a_3591_);
lean_dec(v_a_3589_);
lean_dec_ref(v___x_3583_);
lean_dec(v___x_3579_);
lean_del_object(v___x_3577_);
lean_dec(v_name_3574_);
lean_dec(v_fst_3557_);
lean_dec_ref(v___y_3546_);
v_a_3720_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3727_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3727_ == 0)
{
v___x_3722_ = v___x_3606_;
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_a_3720_);
lean_dec(v___x_3606_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3725_; 
if (v_isShared_3723_ == 0)
{
v___x_3725_ = v___x_3722_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_a_3720_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
return v___x_3725_;
}
}
}
}
}
else
{
lean_object* v_a_3729_; lean_object* v___x_3731_; uint8_t v_isShared_3732_; uint8_t v_isSharedCheck_3736_; 
lean_dec(v_a_3594_);
lean_dec(v_a_3591_);
lean_dec(v_a_3589_);
lean_dec_ref(v___x_3583_);
lean_dec(v___x_3579_);
lean_del_object(v___x_3577_);
lean_dec(v_name_3574_);
lean_dec(v_fst_3557_);
lean_dec_ref(v___y_3546_);
v_a_3729_ = lean_ctor_get(v___x_3598_, 0);
v_isSharedCheck_3736_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3736_ == 0)
{
v___x_3731_ = v___x_3598_;
v_isShared_3732_ = v_isSharedCheck_3736_;
goto v_resetjp_3730_;
}
else
{
lean_inc(v_a_3729_);
lean_dec(v___x_3598_);
v___x_3731_ = lean_box(0);
v_isShared_3732_ = v_isSharedCheck_3736_;
goto v_resetjp_3730_;
}
v_resetjp_3730_:
{
lean_object* v___x_3734_; 
if (v_isShared_3732_ == 0)
{
v___x_3734_ = v___x_3731_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v_a_3729_);
v___x_3734_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
return v___x_3734_;
}
}
}
}
else
{
lean_object* v_a_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3744_; 
lean_dec(v_a_3591_);
lean_dec(v_a_3589_);
lean_dec_ref(v___x_3583_);
lean_dec(v___x_3579_);
lean_del_object(v___x_3577_);
lean_dec(v_levelParams_3575_);
lean_dec(v_name_3574_);
lean_dec(v_fst_3557_);
lean_dec_ref(v___y_3546_);
v_a_3737_ = lean_ctor_get(v___x_3593_, 0);
v_isSharedCheck_3744_ = !lean_is_exclusive(v___x_3593_);
if (v_isSharedCheck_3744_ == 0)
{
v___x_3739_ = v___x_3593_;
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_a_3737_);
lean_dec(v___x_3593_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
lean_object* v___x_3742_; 
if (v_isShared_3740_ == 0)
{
v___x_3742_ = v___x_3739_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v_a_3737_);
v___x_3742_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
return v___x_3742_;
}
}
}
}
else
{
lean_object* v_a_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3752_; 
lean_dec(v_a_3589_);
lean_dec_ref(v___x_3583_);
lean_dec(v___x_3579_);
lean_del_object(v___x_3577_);
lean_dec(v_levelParams_3575_);
lean_dec(v_name_3574_);
lean_dec(v_fst_3557_);
lean_dec_ref(v___y_3546_);
v_a_3745_ = lean_ctor_get(v___x_3590_, 0);
v_isSharedCheck_3752_ = !lean_is_exclusive(v___x_3590_);
if (v_isSharedCheck_3752_ == 0)
{
v___x_3747_ = v___x_3590_;
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_a_3745_);
lean_dec(v___x_3590_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___x_3750_; 
if (v_isShared_3748_ == 0)
{
v___x_3750_ = v___x_3747_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_a_3745_);
v___x_3750_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
return v___x_3750_;
}
}
}
}
else
{
lean_object* v_a_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3760_; 
lean_dec_ref(v___x_3583_);
lean_dec(v___x_3579_);
lean_del_object(v___x_3577_);
lean_dec(v_levelParams_3575_);
lean_dec(v_name_3574_);
lean_dec(v_fst_3557_);
lean_dec_ref(v___y_3546_);
v_a_3753_ = lean_ctor_get(v___x_3588_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3588_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3755_ = v___x_3588_;
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_a_3753_);
lean_dec(v___x_3588_);
v___x_3755_ = lean_box(0);
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
v_resetjp_3754_:
{
lean_object* v___x_3758_; 
if (v_isShared_3756_ == 0)
{
v___x_3758_ = v___x_3755_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v_a_3753_);
v___x_3758_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
return v___x_3758_;
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
v___jp_3549_:
{
size_t v___x_3551_; size_t v___x_3552_; 
v___x_3551_ = ((size_t)1ULL);
v___x_3552_ = lean_usize_add(v_i_3540_, v___x_3551_);
v_i_3540_ = v___x_3552_;
v_b_3541_ = v_a_3550_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3___boxed(lean_object* v_typeNames_3769_, lean_object* v_as_3770_, lean_object* v_sz_3771_, lean_object* v_i_3772_, lean_object* v_b_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_){
_start:
{
size_t v_sz_boxed_3781_; size_t v_i_boxed_3782_; lean_object* v_res_3783_; 
v_sz_boxed_3781_ = lean_unbox_usize(v_sz_3771_);
lean_dec(v_sz_3771_);
v_i_boxed_3782_ = lean_unbox_usize(v_i_3772_);
lean_dec(v_i_3772_);
v_res_3783_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3(v_typeNames_3769_, v_as_3770_, v_sz_boxed_3781_, v_i_boxed_3782_, v_b_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_);
lean_dec(v___y_3779_);
lean_dec(v___y_3777_);
lean_dec_ref(v___y_3776_);
lean_dec(v___y_3775_);
lean_dec_ref(v___y_3774_);
lean_dec_ref(v_as_3770_);
lean_dec_ref(v_typeNames_3769_);
return v_res_3783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds(lean_object* v_ctx_3784_, lean_object* v_typeNames_3785_, lean_object* v_a_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_){
_start:
{
lean_object* v_typeInfos_3793_; lean_object* v_auxFunNames_3794_; lean_object* v___x_3795_; lean_object* v_instances_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; size_t v_sz_3800_; size_t v___x_3801_; lean_object* v___x_3802_; 
v_typeInfos_3793_ = lean_ctor_get(v_ctx_3784_, 1);
lean_inc_ref(v_typeInfos_3793_);
v_auxFunNames_3794_ = lean_ctor_get(v_ctx_3784_, 2);
lean_inc_ref(v_auxFunNames_3794_);
lean_dec_ref(v_ctx_3784_);
v___x_3795_ = lean_unsigned_to_nat(0u);
v_instances_3796_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr___lam__0___closed__0));
v___x_3797_ = lean_array_get_size(v_auxFunNames_3794_);
v___x_3798_ = l_Array_toSubarray___redArg(v_auxFunNames_3794_, v___x_3795_, v___x_3797_);
v___x_3799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3799_, 0, v_instances_3796_);
lean_ctor_set(v___x_3799_, 1, v___x_3798_);
v_sz_3800_ = lean_array_size(v_typeInfos_3793_);
v___x_3801_ = ((size_t)0ULL);
lean_inc_ref(v_a_3790_);
v___x_3802_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__3(v_typeNames_3785_, v_typeInfos_3793_, v_sz_3800_, v___x_3801_, v___x_3799_, v_a_3786_, v_a_3787_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_);
lean_dec_ref(v_typeInfos_3793_);
if (lean_obj_tag(v___x_3802_) == 0)
{
lean_object* v_a_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3811_; 
v_a_3803_ = lean_ctor_get(v___x_3802_, 0);
v_isSharedCheck_3811_ = !lean_is_exclusive(v___x_3802_);
if (v_isSharedCheck_3811_ == 0)
{
v___x_3805_ = v___x_3802_;
v_isShared_3806_ = v_isSharedCheck_3811_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_a_3803_);
lean_dec(v___x_3802_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3811_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
lean_object* v_fst_3807_; lean_object* v___x_3809_; 
v_fst_3807_ = lean_ctor_get(v_a_3803_, 0);
lean_inc(v_fst_3807_);
lean_dec(v_a_3803_);
if (v_isShared_3806_ == 0)
{
lean_ctor_set(v___x_3805_, 0, v_fst_3807_);
v___x_3809_ = v___x_3805_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v_fst_3807_);
v___x_3809_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
return v___x_3809_;
}
}
}
else
{
lean_object* v_a_3812_; lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3819_; 
v_a_3812_ = lean_ctor_get(v___x_3802_, 0);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3802_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3814_ = v___x_3802_;
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
else
{
lean_inc(v_a_3812_);
lean_dec(v___x_3802_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
lean_object* v___x_3817_; 
if (v_isShared_3815_ == 0)
{
v___x_3817_ = v___x_3814_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v_a_3812_);
v___x_3817_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
return v___x_3817_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds___boxed(lean_object* v_ctx_3820_, lean_object* v_typeNames_3821_, lean_object* v_a_3822_, lean_object* v_a_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_, lean_object* v_a_3828_){
_start:
{
lean_object* v_res_3829_; 
v_res_3829_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds(v_ctx_3820_, v_typeNames_3821_, v_a_3822_, v_a_3823_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_);
lean_dec(v_a_3827_);
lean_dec_ref(v_a_3826_);
lean_dec(v_a_3825_);
lean_dec_ref(v_a_3824_);
lean_dec(v_a_3823_);
lean_dec_ref(v_a_3822_);
lean_dec_ref(v_typeNames_3821_);
return v_res_3829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1(size_t v_sz_3830_, size_t v_i_3831_, lean_object* v_bs_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_){
_start:
{
lean_object* v___x_3840_; 
lean_inc_ref(v___y_3837_);
v___x_3840_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___redArg(v_sz_3830_, v_i_3831_, v_bs_3832_, v___y_3837_, v___y_3838_);
return v___x_3840_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1___boxed(lean_object* v_sz_3841_, lean_object* v_i_3842_, lean_object* v_bs_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_){
_start:
{
size_t v_sz_boxed_3851_; size_t v_i_boxed_3852_; lean_object* v_res_3853_; 
v_sz_boxed_3851_ = lean_unbox_usize(v_sz_3841_);
lean_dec(v_sz_3841_);
v_i_boxed_3852_ = lean_unbox_usize(v_i_3842_);
lean_dec(v_i_3842_);
v_res_3853_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds_spec__1(v_sz_boxed_3851_, v_i_boxed_3852_, v_bs_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_);
lean_dec(v___y_3849_);
lean_dec_ref(v___y_3848_);
lean_dec(v___y_3847_);
lean_dec_ref(v___y_3846_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
return v_res_3853_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__0___redArg(lean_object* v_cls_3857_, lean_object* v___y_3858_){
_start:
{
lean_object* v_options_3860_; uint8_t v_hasTrace_3861_; 
v_options_3860_ = lean_ctor_get(v___y_3858_, 2);
v_hasTrace_3861_ = lean_ctor_get_uint8(v_options_3860_, sizeof(void*)*1);
if (v_hasTrace_3861_ == 0)
{
lean_object* v___x_3862_; lean_object* v___x_3863_; 
lean_dec(v_cls_3857_);
v___x_3862_ = lean_box(v_hasTrace_3861_);
v___x_3863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3863_, 0, v___x_3862_);
return v___x_3863_;
}
else
{
lean_object* v_inheritedTraceOptions_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; uint8_t v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; 
v_inheritedTraceOptions_3864_ = lean_ctor_get(v___y_3858_, 13);
v___x_3865_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__0___redArg___closed__1));
v___x_3866_ = l_Lean_Name_append(v___x_3865_, v_cls_3857_);
v___x_3867_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3864_, v_options_3860_, v___x_3866_);
lean_dec(v___x_3866_);
v___x_3868_ = lean_box(v___x_3867_);
v___x_3869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3869_, 0, v___x_3868_);
return v___x_3869_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__0___redArg___boxed(lean_object* v_cls_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_){
_start:
{
lean_object* v_res_3873_; 
v_res_3873_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__0___redArg(v_cls_3870_, v___y_3871_);
lean_dec_ref(v___y_3871_);
return v_res_3873_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__0(lean_object* v_cls_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_){
_start:
{
lean_object* v___x_3882_; 
v___x_3882_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__0___redArg(v_cls_3874_, v___y_3879_);
return v___x_3882_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__0___boxed(lean_object* v_cls_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_){
_start:
{
lean_object* v_res_3891_; 
v_res_3891_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__0(v_cls_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_);
lean_dec(v___y_3889_);
lean_dec_ref(v___y_3888_);
lean_dec(v___y_3887_);
lean_dec_ref(v___y_3886_);
lean_dec(v___y_3885_);
lean_dec_ref(v___y_3884_);
return v_res_3891_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3892_; double v___x_3893_; 
v___x_3892_ = lean_unsigned_to_nat(0u);
v___x_3893_ = lean_float_of_nat(v___x_3892_);
return v___x_3893_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2___redArg(lean_object* v_cls_3897_, lean_object* v_msg_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_){
_start:
{
lean_object* v_ref_3904_; lean_object* v___x_3905_; lean_object* v_a_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3950_; 
v_ref_3904_ = lean_ctor_get(v___y_3901_, 5);
v___x_3905_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_updateIndType_spec__0_spec__0(v_msg_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_);
v_a_3906_ = lean_ctor_get(v___x_3905_, 0);
v_isSharedCheck_3950_ = !lean_is_exclusive(v___x_3905_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3908_ = v___x_3905_;
v_isShared_3909_ = v_isSharedCheck_3950_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_a_3906_);
lean_dec(v___x_3905_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3950_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v___x_3910_; lean_object* v_traceState_3911_; lean_object* v_env_3912_; lean_object* v_nextMacroScope_3913_; lean_object* v_ngen_3914_; lean_object* v_auxDeclNGen_3915_; lean_object* v_cache_3916_; lean_object* v_messages_3917_; lean_object* v_infoState_3918_; lean_object* v_snapshotTasks_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3949_; 
v___x_3910_ = lean_st_ref_take(v___y_3902_);
v_traceState_3911_ = lean_ctor_get(v___x_3910_, 4);
v_env_3912_ = lean_ctor_get(v___x_3910_, 0);
v_nextMacroScope_3913_ = lean_ctor_get(v___x_3910_, 1);
v_ngen_3914_ = lean_ctor_get(v___x_3910_, 2);
v_auxDeclNGen_3915_ = lean_ctor_get(v___x_3910_, 3);
v_cache_3916_ = lean_ctor_get(v___x_3910_, 5);
v_messages_3917_ = lean_ctor_get(v___x_3910_, 6);
v_infoState_3918_ = lean_ctor_get(v___x_3910_, 7);
v_snapshotTasks_3919_ = lean_ctor_get(v___x_3910_, 8);
v_isSharedCheck_3949_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3949_ == 0)
{
v___x_3921_ = v___x_3910_;
v_isShared_3922_ = v_isSharedCheck_3949_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_snapshotTasks_3919_);
lean_inc(v_infoState_3918_);
lean_inc(v_messages_3917_);
lean_inc(v_cache_3916_);
lean_inc(v_traceState_3911_);
lean_inc(v_auxDeclNGen_3915_);
lean_inc(v_ngen_3914_);
lean_inc(v_nextMacroScope_3913_);
lean_inc(v_env_3912_);
lean_dec(v___x_3910_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3949_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
uint64_t v_tid_3923_; lean_object* v_traces_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3948_; 
v_tid_3923_ = lean_ctor_get_uint64(v_traceState_3911_, sizeof(void*)*1);
v_traces_3924_ = lean_ctor_get(v_traceState_3911_, 0);
v_isSharedCheck_3948_ = !lean_is_exclusive(v_traceState_3911_);
if (v_isSharedCheck_3948_ == 0)
{
v___x_3926_ = v_traceState_3911_;
v_isShared_3927_ = v_isSharedCheck_3948_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_traces_3924_);
lean_dec(v_traceState_3911_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3948_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v___x_3928_; double v___x_3929_; uint8_t v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3938_; 
v___x_3928_ = lean_box(0);
v___x_3929_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2___redArg___closed__0);
v___x_3930_ = 0;
v___x_3931_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2___redArg___closed__1));
v___x_3932_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3932_, 0, v_cls_3897_);
lean_ctor_set(v___x_3932_, 1, v___x_3928_);
lean_ctor_set(v___x_3932_, 2, v___x_3931_);
lean_ctor_set_float(v___x_3932_, sizeof(void*)*3, v___x_3929_);
lean_ctor_set_float(v___x_3932_, sizeof(void*)*3 + 8, v___x_3929_);
lean_ctor_set_uint8(v___x_3932_, sizeof(void*)*3 + 16, v___x_3930_);
v___x_3933_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2___redArg___closed__2));
v___x_3934_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3934_, 0, v___x_3932_);
lean_ctor_set(v___x_3934_, 1, v_a_3906_);
lean_ctor_set(v___x_3934_, 2, v___x_3933_);
lean_inc(v_ref_3904_);
v___x_3935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3935_, 0, v_ref_3904_);
lean_ctor_set(v___x_3935_, 1, v___x_3934_);
v___x_3936_ = l_Lean_PersistentArray_push___redArg(v_traces_3924_, v___x_3935_);
if (v_isShared_3927_ == 0)
{
lean_ctor_set(v___x_3926_, 0, v___x_3936_);
v___x_3938_ = v___x_3926_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v___x_3936_);
lean_ctor_set_uint64(v_reuseFailAlloc_3947_, sizeof(void*)*1, v_tid_3923_);
v___x_3938_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
lean_object* v___x_3940_; 
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 4, v___x_3938_);
v___x_3940_ = v___x_3921_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v_env_3912_);
lean_ctor_set(v_reuseFailAlloc_3946_, 1, v_nextMacroScope_3913_);
lean_ctor_set(v_reuseFailAlloc_3946_, 2, v_ngen_3914_);
lean_ctor_set(v_reuseFailAlloc_3946_, 3, v_auxDeclNGen_3915_);
lean_ctor_set(v_reuseFailAlloc_3946_, 4, v___x_3938_);
lean_ctor_set(v_reuseFailAlloc_3946_, 5, v_cache_3916_);
lean_ctor_set(v_reuseFailAlloc_3946_, 6, v_messages_3917_);
lean_ctor_set(v_reuseFailAlloc_3946_, 7, v_infoState_3918_);
lean_ctor_set(v_reuseFailAlloc_3946_, 8, v_snapshotTasks_3919_);
v___x_3940_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3944_; 
v___x_3941_ = lean_st_ref_set(v___y_3902_, v___x_3940_);
v___x_3942_ = lean_box(0);
if (v_isShared_3909_ == 0)
{
lean_ctor_set(v___x_3908_, 0, v___x_3942_);
v___x_3944_ = v___x_3908_;
goto v_reusejp_3943_;
}
else
{
lean_object* v_reuseFailAlloc_3945_; 
v_reuseFailAlloc_3945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3945_, 0, v___x_3942_);
v___x_3944_ = v_reuseFailAlloc_3945_;
goto v_reusejp_3943_;
}
v_reusejp_3943_:
{
return v___x_3944_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2___redArg___boxed(lean_object* v_cls_3951_, lean_object* v_msg_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
lean_object* v_res_3958_; 
v_res_3958_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2___redArg(v_cls_3951_, v_msg_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_);
lean_dec(v___y_3956_);
lean_dec_ref(v___y_3955_);
lean_dec(v___y_3954_);
lean_dec_ref(v___y_3953_);
return v_res_3958_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1(lean_object* v_a_3959_, lean_object* v_a_3960_){
_start:
{
if (lean_obj_tag(v_a_3959_) == 0)
{
lean_object* v___x_3961_; 
v___x_3961_ = l_List_reverse___redArg(v_a_3960_);
return v___x_3961_;
}
else
{
lean_object* v_head_3962_; lean_object* v_tail_3963_; lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3972_; 
v_head_3962_ = lean_ctor_get(v_a_3959_, 0);
v_tail_3963_ = lean_ctor_get(v_a_3959_, 1);
v_isSharedCheck_3972_ = !lean_is_exclusive(v_a_3959_);
if (v_isSharedCheck_3972_ == 0)
{
v___x_3965_ = v_a_3959_;
v_isShared_3966_ = v_isSharedCheck_3972_;
goto v_resetjp_3964_;
}
else
{
lean_inc(v_tail_3963_);
lean_inc(v_head_3962_);
lean_dec(v_a_3959_);
v___x_3965_ = lean_box(0);
v_isShared_3966_ = v_isSharedCheck_3972_;
goto v_resetjp_3964_;
}
v_resetjp_3964_:
{
lean_object* v___x_3967_; lean_object* v___x_3969_; 
v___x_3967_ = l_Lean_MessageData_ofSyntax(v_head_3962_);
if (v_isShared_3966_ == 0)
{
lean_ctor_set(v___x_3965_, 1, v_a_3960_);
lean_ctor_set(v___x_3965_, 0, v___x_3967_);
v___x_3969_ = v___x_3965_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v___x_3967_);
lean_ctor_set(v_reuseFailAlloc_3971_, 1, v_a_3960_);
v___x_3969_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
v_a_3959_ = v_tail_3963_;
v_a_3960_ = v___x_3969_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__2(void){
_start:
{
lean_object* v___x_3978_; lean_object* v___x_3979_; 
v___x_3978_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__1));
v___x_3979_ = l_Lean_stringToMessageData(v___x_3978_);
return v___x_3979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds(lean_object* v_declNames_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_){
_start:
{
lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; uint8_t v___x_3993_; lean_object* v___x_3994_; 
v___x_3988_ = lean_box(0);
v___x_3989_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__14));
v___x_3990_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToTypeExpr_spec__1___redArg___closed__0));
v___x_3991_ = lean_unsigned_to_nat(0u);
v___x_3992_ = lean_array_get_borrowed(v___x_3988_, v_declNames_3980_, v___x_3991_);
v___x_3993_ = 1;
lean_inc(v___x_3992_);
v___x_3994_ = l_Lean_Elab_Deriving_mkContext(v___x_3989_, v___x_3990_, v___x_3992_, v___x_3993_, v_a_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_, v_a_3986_);
if (lean_obj_tag(v___x_3994_) == 0)
{
lean_object* v_a_3995_; lean_object* v___x_3996_; 
v_a_3995_ = lean_ctor_get(v___x_3994_, 0);
lean_inc(v_a_3995_);
lean_dec_ref(v___x_3994_);
lean_inc(v_a_3995_);
v___x_3996_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAuxFunctions(v_a_3995_, v_a_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_, v_a_3986_);
if (lean_obj_tag(v___x_3996_) == 0)
{
lean_object* v_a_3997_; lean_object* v___x_3998_; 
v_a_3997_ = lean_ctor_get(v___x_3996_, 0);
lean_inc(v_a_3997_);
lean_dec_ref(v___x_3996_);
v___x_3998_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkInstanceCmds(v_a_3995_, v_declNames_3980_, v_a_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_, v_a_3986_);
if (lean_obj_tag(v___x_3998_) == 0)
{
lean_object* v_a_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v_a_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4037_; 
v_a_3999_ = lean_ctor_get(v___x_3998_, 0);
lean_inc(v_a_3999_);
lean_dec_ref(v___x_3998_);
v___x_4000_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__0));
v___x_4001_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__0___redArg(v___x_4000_, v_a_3985_);
v_a_4002_ = lean_ctor_get(v___x_4001_, 0);
v_isSharedCheck_4037_ = !lean_is_exclusive(v___x_4001_);
if (v_isSharedCheck_4037_ == 0)
{
v___x_4004_ = v___x_4001_;
v_isShared_4005_ = v_isSharedCheck_4037_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_a_4002_);
lean_dec(v___x_4001_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4037_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; uint8_t v___x_4010_; 
v___x_4006_ = lean_unsigned_to_nat(1u);
v___x_4007_ = lean_mk_empty_array_with_capacity(v___x_4006_);
v___x_4008_ = lean_array_push(v___x_4007_, v_a_3997_);
v___x_4009_ = l_Array_append___redArg(v___x_4008_, v_a_3999_);
lean_dec(v_a_3999_);
v___x_4010_ = lean_unbox(v_a_4002_);
lean_dec(v_a_4002_);
if (v___x_4010_ == 0)
{
lean_object* v___x_4012_; 
if (v_isShared_4005_ == 0)
{
lean_ctor_set(v___x_4004_, 0, v___x_4009_);
v___x_4012_ = v___x_4004_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4013_; 
v_reuseFailAlloc_4013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4013_, 0, v___x_4009_);
v___x_4012_ = v_reuseFailAlloc_4013_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
return v___x_4012_;
}
}
else
{
lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; 
lean_del_object(v___x_4004_);
v___x_4014_ = lean_obj_once(&l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__2, &l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__2_once, _init_l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__2);
lean_inc_ref(v___x_4009_);
v___x_4015_ = lean_array_to_list(v___x_4009_);
v___x_4016_ = lean_box(0);
v___x_4017_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__1(v___x_4015_, v___x_4016_);
v___x_4018_ = l_Lean_MessageData_ofList(v___x_4017_);
v___x_4019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4019_, 0, v___x_4014_);
lean_ctor_set(v___x_4019_, 1, v___x_4018_);
v___x_4020_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2___redArg(v___x_4000_, v___x_4019_, v_a_3983_, v_a_3984_, v_a_3985_, v_a_3986_);
if (lean_obj_tag(v___x_4020_) == 0)
{
lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4027_; 
v_isSharedCheck_4027_ = !lean_is_exclusive(v___x_4020_);
if (v_isSharedCheck_4027_ == 0)
{
lean_object* v_unused_4028_; 
v_unused_4028_ = lean_ctor_get(v___x_4020_, 0);
lean_dec(v_unused_4028_);
v___x_4022_ = v___x_4020_;
v_isShared_4023_ = v_isSharedCheck_4027_;
goto v_resetjp_4021_;
}
else
{
lean_dec(v___x_4020_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4027_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
lean_object* v___x_4025_; 
if (v_isShared_4023_ == 0)
{
lean_ctor_set(v___x_4022_, 0, v___x_4009_);
v___x_4025_ = v___x_4022_;
goto v_reusejp_4024_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v___x_4009_);
v___x_4025_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4024_;
}
v_reusejp_4024_:
{
return v___x_4025_;
}
}
}
else
{
lean_object* v_a_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4036_; 
lean_dec_ref(v___x_4009_);
v_a_4029_ = lean_ctor_get(v___x_4020_, 0);
v_isSharedCheck_4036_ = !lean_is_exclusive(v___x_4020_);
if (v_isSharedCheck_4036_ == 0)
{
v___x_4031_ = v___x_4020_;
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_a_4029_);
lean_dec(v___x_4020_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v___x_4034_; 
if (v_isShared_4032_ == 0)
{
v___x_4034_ = v___x_4031_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_a_4029_);
v___x_4034_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
return v___x_4034_;
}
}
}
}
}
}
else
{
lean_object* v_a_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4045_; 
lean_dec(v_a_3997_);
v_a_4038_ = lean_ctor_get(v___x_3998_, 0);
v_isSharedCheck_4045_ = !lean_is_exclusive(v___x_3998_);
if (v_isSharedCheck_4045_ == 0)
{
v___x_4040_ = v___x_3998_;
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_a_4038_);
lean_dec(v___x_3998_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v___x_4043_; 
if (v_isShared_4041_ == 0)
{
v___x_4043_ = v___x_4040_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_a_4038_);
v___x_4043_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
return v___x_4043_;
}
}
}
}
else
{
lean_object* v_a_4046_; lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4053_; 
lean_dec(v_a_3995_);
v_a_4046_ = lean_ctor_get(v___x_3996_, 0);
v_isSharedCheck_4053_ = !lean_is_exclusive(v___x_3996_);
if (v_isSharedCheck_4053_ == 0)
{
v___x_4048_ = v___x_3996_;
v_isShared_4049_ = v_isSharedCheck_4053_;
goto v_resetjp_4047_;
}
else
{
lean_inc(v_a_4046_);
lean_dec(v___x_3996_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4053_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
lean_object* v___x_4051_; 
if (v_isShared_4049_ == 0)
{
v___x_4051_ = v___x_4048_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v_a_4046_);
v___x_4051_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
return v___x_4051_;
}
}
}
}
else
{
lean_object* v_a_4054_; lean_object* v___x_4056_; uint8_t v_isShared_4057_; uint8_t v_isSharedCheck_4061_; 
v_a_4054_ = lean_ctor_get(v___x_3994_, 0);
v_isSharedCheck_4061_ = !lean_is_exclusive(v___x_3994_);
if (v_isSharedCheck_4061_ == 0)
{
v___x_4056_ = v___x_3994_;
v_isShared_4057_ = v_isSharedCheck_4061_;
goto v_resetjp_4055_;
}
else
{
lean_inc(v_a_4054_);
lean_dec(v___x_3994_);
v___x_4056_ = lean_box(0);
v_isShared_4057_ = v_isSharedCheck_4061_;
goto v_resetjp_4055_;
}
v_resetjp_4055_:
{
lean_object* v___x_4059_; 
if (v_isShared_4057_ == 0)
{
v___x_4059_ = v___x_4056_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_a_4054_);
v___x_4059_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
return v___x_4059_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___boxed(lean_object* v_declNames_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_){
_start:
{
lean_object* v_res_4070_; 
v_res_4070_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds(v_declNames_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_, v_a_4068_);
lean_dec(v_a_4068_);
lean_dec_ref(v_a_4067_);
lean_dec(v_a_4066_);
lean_dec_ref(v_a_4065_);
lean_dec(v_a_4064_);
lean_dec_ref(v_a_4063_);
lean_dec_ref(v_declNames_4062_);
return v_res_4070_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2(lean_object* v_cls_4071_, lean_object* v_msg_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_){
_start:
{
lean_object* v___x_4080_; 
v___x_4080_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2___redArg(v_cls_4071_, v_msg_4072_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
return v___x_4080_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2___boxed(lean_object* v_cls_4081_, lean_object* v_msg_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_){
_start:
{
lean_object* v_res_4090_; 
v_res_4090_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__2(v_cls_4081_, v_msg_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_);
lean_dec(v___y_4088_);
lean_dec_ref(v___y_4087_);
lean_dec(v___y_4086_);
lean_dec_ref(v___y_4085_);
lean_dec(v___y_4084_);
lean_dec_ref(v___y_4083_);
return v_res_4090_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0___redArg(lean_object* v_declName_4091_, lean_object* v___y_4092_){
_start:
{
lean_object* v___x_4094_; lean_object* v_env_4095_; uint8_t v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; 
v___x_4094_ = lean_st_ref_get(v___y_4092_);
v_env_4095_ = lean_ctor_get(v___x_4094_, 0);
lean_inc_ref(v_env_4095_);
lean_dec(v___x_4094_);
v___x_4096_ = l_Lean_isInductiveCore(v_env_4095_, v_declName_4091_);
v___x_4097_ = lean_box(v___x_4096_);
v___x_4098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4098_, 0, v___x_4097_);
return v___x_4098_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0___redArg___boxed(lean_object* v_declName_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_){
_start:
{
lean_object* v_res_4102_; 
v_res_4102_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0___redArg(v_declName_4099_, v___y_4100_);
lean_dec(v___y_4100_);
return v_res_4102_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0(lean_object* v_declName_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_){
_start:
{
lean_object* v___x_4107_; 
v___x_4107_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0___redArg(v_declName_4103_, v___y_4105_);
return v___x_4107_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0___boxed(lean_object* v_declName_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_){
_start:
{
lean_object* v_res_4112_; 
v_res_4112_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0(v_declName_4108_, v___y_4109_, v___y_4110_);
lean_dec(v___y_4110_);
lean_dec_ref(v___y_4109_);
return v_res_4112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__0(uint8_t v_____do__lift_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_){
_start:
{
if (v_____do__lift_4113_ == 0)
{
uint8_t v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; 
v___x_4117_ = 1;
v___x_4118_ = lean_box(v___x_4117_);
v___x_4119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4119_, 0, v___x_4118_);
return v___x_4119_;
}
else
{
uint8_t v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; 
v___x_4120_ = 0;
v___x_4121_ = lean_box(v___x_4120_);
v___x_4122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4122_, 0, v___x_4121_);
return v___x_4122_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__0___boxed(lean_object* v_____do__lift_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_){
_start:
{
uint8_t v_____do__lift_1624__boxed_4127_; lean_object* v_res_4128_; 
v_____do__lift_1624__boxed_4127_ = lean_unbox(v_____do__lift_4123_);
v_res_4128_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__0(v_____do__lift_1624__boxed_4127_, v___y_4124_, v___y_4125_);
lean_dec(v___y_4125_);
lean_dec_ref(v___y_4124_);
return v_res_4128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1_spec__1(lean_object* v_o_4129_, lean_object* v_k_4130_, uint8_t v_v_4131_){
_start:
{
lean_object* v_map_4132_; uint8_t v_hasTrace_4133_; lean_object* v___x_4135_; uint8_t v_isShared_4136_; uint8_t v_isSharedCheck_4147_; 
v_map_4132_ = lean_ctor_get(v_o_4129_, 0);
v_hasTrace_4133_ = lean_ctor_get_uint8(v_o_4129_, sizeof(void*)*1);
v_isSharedCheck_4147_ = !lean_is_exclusive(v_o_4129_);
if (v_isSharedCheck_4147_ == 0)
{
v___x_4135_ = v_o_4129_;
v_isShared_4136_ = v_isSharedCheck_4147_;
goto v_resetjp_4134_;
}
else
{
lean_inc(v_map_4132_);
lean_dec(v_o_4129_);
v___x_4135_ = lean_box(0);
v_isShared_4136_ = v_isSharedCheck_4147_;
goto v_resetjp_4134_;
}
v_resetjp_4134_:
{
lean_object* v___x_4137_; lean_object* v___x_4138_; 
v___x_4137_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4137_, 0, v_v_4131_);
lean_inc(v_k_4130_);
v___x_4138_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4130_, v___x_4137_, v_map_4132_);
if (v_hasTrace_4133_ == 0)
{
lean_object* v___x_4139_; uint8_t v___x_4140_; lean_object* v___x_4142_; 
v___x_4139_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds_spec__0___redArg___closed__1));
v___x_4140_ = l_Lean_Name_isPrefixOf(v___x_4139_, v_k_4130_);
lean_dec(v_k_4130_);
if (v_isShared_4136_ == 0)
{
lean_ctor_set(v___x_4135_, 0, v___x_4138_);
v___x_4142_ = v___x_4135_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v___x_4138_);
v___x_4142_ = v_reuseFailAlloc_4143_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
lean_ctor_set_uint8(v___x_4142_, sizeof(void*)*1, v___x_4140_);
return v___x_4142_;
}
}
else
{
lean_object* v___x_4145_; 
lean_dec(v_k_4130_);
if (v_isShared_4136_ == 0)
{
lean_ctor_set(v___x_4135_, 0, v___x_4138_);
v___x_4145_ = v___x_4135_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v___x_4138_);
lean_ctor_set_uint8(v_reuseFailAlloc_4146_, sizeof(void*)*1, v_hasTrace_4133_);
v___x_4145_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
return v___x_4145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1_spec__1___boxed(lean_object* v_o_4148_, lean_object* v_k_4149_, lean_object* v_v_4150_){
_start:
{
uint8_t v_v_boxed_4151_; lean_object* v_res_4152_; 
v_v_boxed_4151_ = lean_unbox(v_v_4150_);
v_res_4152_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1_spec__1(v_o_4148_, v_k_4149_, v_v_boxed_4151_);
return v_res_4152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1(lean_object* v_opts_4153_, lean_object* v_opt_4154_, uint8_t v_val_4155_){
_start:
{
lean_object* v_name_4156_; lean_object* v___x_4157_; 
v_name_4156_ = lean_ctor_get(v_opt_4154_, 0);
lean_inc(v_name_4156_);
lean_dec_ref(v_opt_4154_);
v___x_4157_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1_spec__1(v_opts_4153_, v_name_4156_, v_val_4155_);
return v___x_4157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1___boxed(lean_object* v_opts_4158_, lean_object* v_opt_4159_, lean_object* v_val_4160_){
_start:
{
uint8_t v_val_boxed_4161_; lean_object* v_res_4162_; 
v_val_boxed_4161_ = lean_unbox(v_val_4160_);
v_res_4162_ = l_Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1(v_opts_4158_, v_opt_4159_, v_val_boxed_4161_);
return v_res_4162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__1(uint8_t v_a_4163_, lean_object* v_scope_4164_){
_start:
{
lean_object* v_header_4165_; lean_object* v_opts_4166_; lean_object* v_currNamespace_4167_; lean_object* v_openDecls_4168_; lean_object* v_levelNames_4169_; lean_object* v_varDecls_4170_; lean_object* v_varUIds_4171_; lean_object* v_includedVars_4172_; lean_object* v_omittedVars_4173_; uint8_t v_isNoncomputable_4174_; uint8_t v_isPublic_4175_; uint8_t v_isMeta_4176_; lean_object* v_attrs_4177_; lean_object* v___x_4179_; uint8_t v_isShared_4180_; uint8_t v_isSharedCheck_4186_; 
v_header_4165_ = lean_ctor_get(v_scope_4164_, 0);
v_opts_4166_ = lean_ctor_get(v_scope_4164_, 1);
v_currNamespace_4167_ = lean_ctor_get(v_scope_4164_, 2);
v_openDecls_4168_ = lean_ctor_get(v_scope_4164_, 3);
v_levelNames_4169_ = lean_ctor_get(v_scope_4164_, 4);
v_varDecls_4170_ = lean_ctor_get(v_scope_4164_, 5);
v_varUIds_4171_ = lean_ctor_get(v_scope_4164_, 6);
v_includedVars_4172_ = lean_ctor_get(v_scope_4164_, 7);
v_omittedVars_4173_ = lean_ctor_get(v_scope_4164_, 8);
v_isNoncomputable_4174_ = lean_ctor_get_uint8(v_scope_4164_, sizeof(void*)*10);
v_isPublic_4175_ = lean_ctor_get_uint8(v_scope_4164_, sizeof(void*)*10 + 1);
v_isMeta_4176_ = lean_ctor_get_uint8(v_scope_4164_, sizeof(void*)*10 + 2);
v_attrs_4177_ = lean_ctor_get(v_scope_4164_, 9);
v_isSharedCheck_4186_ = !lean_is_exclusive(v_scope_4164_);
if (v_isSharedCheck_4186_ == 0)
{
v___x_4179_ = v_scope_4164_;
v_isShared_4180_ = v_isSharedCheck_4186_;
goto v_resetjp_4178_;
}
else
{
lean_inc(v_attrs_4177_);
lean_inc(v_omittedVars_4173_);
lean_inc(v_includedVars_4172_);
lean_inc(v_varUIds_4171_);
lean_inc(v_varDecls_4170_);
lean_inc(v_levelNames_4169_);
lean_inc(v_openDecls_4168_);
lean_inc(v_currNamespace_4167_);
lean_inc(v_opts_4166_);
lean_inc(v_header_4165_);
lean_dec(v_scope_4164_);
v___x_4179_ = lean_box(0);
v_isShared_4180_ = v_isSharedCheck_4186_;
goto v_resetjp_4178_;
}
v_resetjp_4178_:
{
lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4184_; 
v___x_4181_ = l_Lean_Elab_autoImplicit;
v___x_4182_ = l_Lean_Option_set___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__1(v_opts_4166_, v___x_4181_, v_a_4163_);
if (v_isShared_4180_ == 0)
{
lean_ctor_set(v___x_4179_, 1, v___x_4182_);
v___x_4184_ = v___x_4179_;
goto v_reusejp_4183_;
}
else
{
lean_object* v_reuseFailAlloc_4185_; 
v_reuseFailAlloc_4185_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v_reuseFailAlloc_4185_, 0, v_header_4165_);
lean_ctor_set(v_reuseFailAlloc_4185_, 1, v___x_4182_);
lean_ctor_set(v_reuseFailAlloc_4185_, 2, v_currNamespace_4167_);
lean_ctor_set(v_reuseFailAlloc_4185_, 3, v_openDecls_4168_);
lean_ctor_set(v_reuseFailAlloc_4185_, 4, v_levelNames_4169_);
lean_ctor_set(v_reuseFailAlloc_4185_, 5, v_varDecls_4170_);
lean_ctor_set(v_reuseFailAlloc_4185_, 6, v_varUIds_4171_);
lean_ctor_set(v_reuseFailAlloc_4185_, 7, v_includedVars_4172_);
lean_ctor_set(v_reuseFailAlloc_4185_, 8, v_omittedVars_4173_);
lean_ctor_set(v_reuseFailAlloc_4185_, 9, v_attrs_4177_);
lean_ctor_set_uint8(v_reuseFailAlloc_4185_, sizeof(void*)*10, v_isNoncomputable_4174_);
lean_ctor_set_uint8(v_reuseFailAlloc_4185_, sizeof(void*)*10 + 1, v_isPublic_4175_);
lean_ctor_set_uint8(v_reuseFailAlloc_4185_, sizeof(void*)*10 + 2, v_isMeta_4176_);
v___x_4184_ = v_reuseFailAlloc_4185_;
goto v_reusejp_4183_;
}
v_reusejp_4183_:
{
return v___x_4184_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__1___boxed(lean_object* v_a_4187_, lean_object* v_scope_4188_){
_start:
{
uint8_t v_a_1682__boxed_4189_; lean_object* v_res_4190_; 
v_a_1682__boxed_4189_ = lean_unbox(v_a_4187_);
v_res_4190_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__1(v_a_1682__boxed_4189_, v_scope_4188_);
return v_res_4190_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__2(lean_object* v_as_4191_, size_t v_i_4192_, size_t v_stop_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_){
_start:
{
uint8_t v___x_4197_; 
v___x_4197_ = lean_usize_dec_eq(v_i_4192_, v_stop_4193_);
if (v___x_4197_ == 0)
{
uint8_t v___x_4198_; uint8_t v_a_4200_; lean_object* v___x_4206_; lean_object* v___x_4207_; 
v___x_4198_ = 1;
v___x_4206_ = lean_array_uget_borrowed(v_as_4191_, v_i_4192_);
lean_inc(v___x_4206_);
v___x_4207_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__0___redArg(v___x_4206_, v___y_4195_);
if (lean_obj_tag(v___x_4207_) == 0)
{
lean_object* v_a_4208_; lean_object* v___x_4210_; uint8_t v_isShared_4211_; uint8_t v_isSharedCheck_4217_; 
v_a_4208_ = lean_ctor_get(v___x_4207_, 0);
v_isSharedCheck_4217_ = !lean_is_exclusive(v___x_4207_);
if (v_isSharedCheck_4217_ == 0)
{
v___x_4210_ = v___x_4207_;
v_isShared_4211_ = v_isSharedCheck_4217_;
goto v_resetjp_4209_;
}
else
{
lean_inc(v_a_4208_);
lean_dec(v___x_4207_);
v___x_4210_ = lean_box(0);
v_isShared_4211_ = v_isSharedCheck_4217_;
goto v_resetjp_4209_;
}
v_resetjp_4209_:
{
uint8_t v___x_4212_; 
v___x_4212_ = lean_unbox(v_a_4208_);
lean_dec(v_a_4208_);
if (v___x_4212_ == 0)
{
lean_object* v___x_4213_; lean_object* v___x_4215_; 
v___x_4213_ = lean_box(v___x_4198_);
if (v_isShared_4211_ == 0)
{
lean_ctor_set(v___x_4210_, 0, v___x_4213_);
v___x_4215_ = v___x_4210_;
goto v_reusejp_4214_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v___x_4213_);
v___x_4215_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4214_;
}
v_reusejp_4214_:
{
return v___x_4215_;
}
}
else
{
lean_del_object(v___x_4210_);
v_a_4200_ = v___x_4197_;
goto v___jp_4199_;
}
}
}
else
{
if (lean_obj_tag(v___x_4207_) == 0)
{
lean_object* v_a_4218_; uint8_t v___x_4219_; 
v_a_4218_ = lean_ctor_get(v___x_4207_, 0);
lean_inc(v_a_4218_);
lean_dec_ref(v___x_4207_);
v___x_4219_ = lean_unbox(v_a_4218_);
lean_dec(v_a_4218_);
v_a_4200_ = v___x_4219_;
goto v___jp_4199_;
}
else
{
return v___x_4207_;
}
}
v___jp_4199_:
{
if (v_a_4200_ == 0)
{
size_t v___x_4201_; size_t v___x_4202_; 
v___x_4201_ = ((size_t)1ULL);
v___x_4202_ = lean_usize_add(v_i_4192_, v___x_4201_);
v_i_4192_ = v___x_4202_;
goto _start;
}
else
{
lean_object* v___x_4204_; lean_object* v___x_4205_; 
v___x_4204_ = lean_box(v___x_4198_);
v___x_4205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4205_, 0, v___x_4204_);
return v___x_4205_;
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
lean_object* v___x_4236_; lean_object* v___x_4237_; uint8_t v___x_4238_; uint8_t v_a_4240_; lean_object* v___y_4280_; 
v___x_4236_ = lean_unsigned_to_nat(0u);
v___x_4237_ = lean_array_get_size(v_declNames_4232_);
v___x_4238_ = lean_nat_dec_lt(v___x_4236_, v___x_4237_);
if (v___x_4238_ == 0)
{
lean_object* v___x_4284_; 
v___x_4284_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__0(v___x_4238_, v_a_4233_, v_a_4234_);
v___y_4280_ = v___x_4284_;
goto v___jp_4279_;
}
else
{
if (v___x_4238_ == 0)
{
v_a_4240_ = v___x_4238_;
goto v___jp_4239_;
}
else
{
size_t v___x_4285_; size_t v___x_4286_; lean_object* v___x_4287_; 
v___x_4285_ = ((size_t)0ULL);
v___x_4286_ = lean_usize_of_nat(v___x_4237_);
v___x_4287_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler_spec__2(v_declNames_4232_, v___x_4285_, v___x_4286_, v_a_4233_, v_a_4234_);
if (lean_obj_tag(v___x_4287_) == 0)
{
lean_object* v_a_4288_; uint8_t v___x_4289_; lean_object* v___x_4290_; 
v_a_4288_ = lean_ctor_get(v___x_4287_, 0);
lean_inc(v_a_4288_);
lean_dec_ref(v___x_4287_);
v___x_4289_ = lean_unbox(v_a_4288_);
lean_dec(v_a_4288_);
v___x_4290_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__0(v___x_4289_, v_a_4233_, v_a_4234_);
v___y_4280_ = v___x_4290_;
goto v___jp_4279_;
}
else
{
v___y_4280_ = v___x_4287_;
goto v___jp_4279_;
}
}
}
v___jp_4239_:
{
if (v___x_4238_ == 0)
{
lean_object* v___x_4241_; lean_object* v___x_4242_; 
lean_dec_ref(v_declNames_4232_);
v___x_4241_ = lean_box(v___x_4238_);
v___x_4242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4242_, 0, v___x_4241_);
return v___x_4242_;
}
else
{
lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; 
v___x_4243_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___boxed), 8, 1);
lean_closure_set(v___x_4243_, 0, v_declNames_4232_);
v___x_4244_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftTermElabM___boxed), 5, 2);
lean_closure_set(v___x_4244_, 0, lean_box(0));
lean_closure_set(v___x_4244_, 1, v___x_4243_);
v___x_4245_ = l_Lean_Elab_Command_withFreshMacroScope___redArg(v___x_4244_, v_a_4233_, v_a_4234_);
if (lean_obj_tag(v___x_4245_) == 0)
{
lean_object* v_a_4246_; lean_object* v___x_4247_; lean_object* v___f_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; 
v_a_4246_ = lean_ctor_get(v___x_4245_, 0);
lean_inc(v_a_4246_);
lean_dec_ref(v___x_4245_);
v___x_4247_ = lean_box(v_a_4240_);
v___f_4248_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___lam__1___boxed), 2, 1);
lean_closure_set(v___f_4248_, 0, v___x_4247_);
v___x_4249_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkAppNTerm_spec__0___redArg___closed__16));
v___x_4250_ = lean_box(2);
v___x_4251_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4251_, 0, v___x_4250_);
lean_ctor_set(v___x_4251_, 1, v___x_4249_);
lean_ctor_set(v___x_4251_, 2, v_a_4246_);
v___x_4252_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(v___x_4252_, 0, v___x_4251_);
v___x_4253_ = l_Lean_Elab_Command_withScope___redArg(v___f_4248_, v___x_4252_, v_a_4233_, v_a_4234_);
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
v___x_4257_ = lean_box(v_a_4240_);
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
v_a_4271_ = lean_ctor_get(v___x_4245_, 0);
v_isSharedCheck_4278_ = !lean_is_exclusive(v___x_4245_);
if (v_isSharedCheck_4278_ == 0)
{
v___x_4273_ = v___x_4245_;
v_isShared_4274_ = v_isSharedCheck_4278_;
goto v_resetjp_4272_;
}
else
{
lean_inc(v_a_4271_);
lean_dec(v___x_4245_);
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
lean_dec_ref(v___y_4280_);
v___x_4283_ = lean_unbox(v_a_4281_);
lean_dec(v_a_4281_);
v_a_4240_ = v___x_4283_;
goto v___jp_4239_;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler___boxed(lean_object* v_declNames_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_){
_start:
{
lean_object* v_res_4295_; 
v_res_4295_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceHandler(v_declNames_4291_, v_a_4292_, v_a_4293_);
lean_dec(v_a_4293_);
lean_dec_ref(v_a_4292_);
return v_res_4295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; 
v___x_4363_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkLocalInstanceLetDecls_spec__1___closed__14));
v___x_4364_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__0_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_));
v___x_4365_ = l_Lean_Elab_registerDerivingHandler(v___x_4363_, v___x_4364_);
if (lean_obj_tag(v___x_4365_) == 0)
{
lean_object* v___x_4366_; uint8_t v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; 
lean_dec_ref(v___x_4365_);
v___x_4366_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_mkToExprInstanceCmds___closed__0));
v___x_4367_ = 0;
v___x_4368_ = ((lean_object*)(l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn___closed__25_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_));
v___x_4369_ = l_Lean_registerTraceClass(v___x_4366_, v___x_4367_, v___x_4368_);
return v___x_4369_;
}
else
{
return v___x_4365_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2____boxed(lean_object* v_a_4370_){
_start:
{
lean_object* v_res_4371_; 
v_res_4371_ = l___private_Lean_Elab_Deriving_ToExpr_0__Lean_Elab_Deriving_ToExpr_initFn_00___x40_Lean_Elab_Deriving_ToExpr_1932707508____hygCtx___hyg_2_();
return v_res_4371_;
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
